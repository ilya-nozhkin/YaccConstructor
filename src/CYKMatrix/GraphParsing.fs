﻿module GraphParsing
    open Util
    open TPMatrices
    open System
    open System.Collections.Generic
    open Yard.Core
    open Yard.Core.IL
    open Yard.Core.IL.Production
    open Yard.Core.IL.Definition
    open Yard.Core.Helpers
    open Conversions.TransformAux
    open QuickGraph
    open Alea.CUDA
    open Alea.CUDA.CULib
    open Alea.CUDA.Utilities
    open MathNet.Numerics.LinearAlgebra.Double
    open ManagedCuda
    open ManagedCuda.CudaSparse
    open ManagedCuda.BasicTypes
    open Microsoft.FSharp.Core.Operators

    type ParsingMatrix<'MatrixType> = Dictionary<NonTerminal, 'MatrixType>

    type MySparseMatrix(size : int, nnz : int, csrVal : float[], csrRow : int[], csrColInd : int[]) =
        member this.Size = size
        member this.Nnz = nnz
        member this.CsrVal = csrVal
        member this.CsrRow = csrRow
        member this.CsrColInd = csrColInd

    let initParsingMatrix<'MatrixType, 'InnerType when 'InnerType : comparison> (graph: AdjacencyGraph<int, TaggedEdge<int, int<AbstractAnalysis.Common.token>>>)
                  (allRules: RulesHolder)
                  nonterminals
                  createEmptyMatrix 
                  (matrixSetValue : 'MatrixType -> int -> int -> 'InnerType -> unit) 
                  (innerOne: 'InnerType) =
        let vertexToInt = new Dictionary<_,_>()
        let mutable procVertices = 0
        let parsingMatrix = new ParsingMatrix<'MatrixType> ()
        do 
            (
                nonterminals 
                |> Seq.map (fun x -> x, createEmptyMatrix (graph.VertexCount))
            )
            |> Seq.iter parsingMatrix.Add

        for vertex in graph.Vertices do
            vertexToInt.Add(vertex, procVertices)
            procVertices <- procVertices + 1

        for edg in graph.Edges do
            let label = edg.Tag
            if allRules.IsSimpleTail label
            then
                let simpleNonterminals = allRules.HeadsBySimpleTail label
                for (simpleNonterminal, _) in simpleNonterminals do
                    let row = vertexToInt.[edg.Source]
                    let col = vertexToInt.[edg.Target]
                    matrixSetValue parsingMatrix.[simpleNonterminal] row col innerOne

        parsingMatrix, vertexToInt

    let naiveSquareMatrix<'MatrixType, 'InnerType when 'InnerType : comparison> matrixSetValue toArray (innerSum: 'InnerType -> 'InnerType -> 'InnerType)
                (innerMult: 'InnerType -> 'InnerType -> 'InnerType) (innerZero: 'InnerType) (innerOne: 'InnerType)
                (matrix: ParsingMatrix<'MatrixType>) (allRules: RulesHolder) isChanged matrixSize =
        let unionArrays (matrix: 'MatrixType) (curArr: 'InnerType []) (updArr: 'InnerType []) =
            for ind in 0..matrixSize*matrixSize - 1 do
                if curArr.[ind] = innerZero && updArr.[ind] > innerZero
                then
                    isChanged := true
                    let i = ind / matrixSize
                    let j = ind - i * matrixSize
                    matrixSetValue matrix i j innerOne

        let multArrays (from1: 'InnerType []) (from2: 'InnerType []) =        
                let calculateCell x =
                    let i = x / matrixSize
                    let j = x - i * matrixSize 
                    let skipRows = i * matrixSize
                    let skipColumns = j * matrixSize                
                    Array.fold2 (fun b v1 v2 -> innerSum b <| innerMult v1 v2)
                                innerZero
                                from1.[skipRows..skipRows + matrixSize - 1] 
                                from2.[skipColumns..skipColumns + matrixSize - 1]

                Array.init (matrixSize * matrixSize) (fun x -> calculateCell <| x)

        let nontermPairs = allRules.ComplexTails
        for (nt1, nt2) in nontermPairs do
            let arr1 = toArray matrix.[nt1] false
            let arr2 = toArray matrix.[nt2] true
            let resultArray = multArrays arr1 arr2

            for (nonTerm, _) in allRules.HeadsByComplexTail (nt1, nt2) do
                unionArrays matrix.[nonTerm] (toArray matrix.[nonTerm] false) resultArray

    let sparseSquareMatrix (matrix: ParsingMatrix<SparseMatrix>) (allRules: RulesHolder) isChanged matrixSize =
        let unionArrays (matrix: SparseMatrix) (updMatrix: MathNet.Numerics.LinearAlgebra.Matrix<float>) =
            for i in 0..(matrixSize - 1) do
                for j in 0..(matrixSize - 1) do
                    if matrix.At(i, j) = 0.0 && updMatrix.At(i, j) > 0.0
                    then
                        isChanged := true
                        matrix.At(i, j, 1.0)

        let nontermPairs = allRules.ComplexTails
        for (nt1, nt2) in nontermPairs do
            let matrix1 = matrix.[nt1]
            let matrix2 = matrix.[nt2]
            let resultMatrix = matrix1.Multiply(matrix2)
            
            for (nonTerm, _) in allRules.HeadsByComplexTail (nt1, nt2) do
                unionArrays matrix.[nonTerm] resultMatrix

    let sparseSquareMatrix2 (matrix: ParsingMatrix<SparseMatrix>) (allRules: RulesHolder) isChanged matrixSize =
        let nontermPairs = allRules.ComplexTails
        for (nt1, nt2) in nontermPairs do
            let matrix1 = matrix.[nt1]
            let matrix2 = matrix.[nt2]
            let resultMatrix = matrix1.Multiply(matrix2)
            
            for (nonTerm, _) in allRules.HeadsByComplexTail (nt1, nt2) do
                let nonZ = matrix.[nonTerm].NonZerosCount
                matrix.[nonTerm].PointwiseMaximum(resultMatrix, matrix.[nonTerm])
                if (nonZ <> matrix.[nonTerm].NonZerosCount)
                then
                    isChanged := true

    let worker = Worker.Default

    let cudaSquareMatrix<'MatrixType> matrixSetValue toArray (matrix: ParsingMatrix<'MatrixType>) (allRules: RulesHolder) isChanged matrixSize =
        
        let (mult1:DeviceMemory<float>) = worker.Malloc((int)(matrixSize * matrixSize)) //need to do malloc only once per graph parsing
        let (mult2:DeviceMemory<float>) = worker.Malloc((int)(matrixSize * matrixSize))
        let (result:DeviceMemory<float>) = worker.Malloc((int)(matrixSize * matrixSize))

        let unionArrays (matrix: 'MatrixType) (curArr: float []) (updArr: float []) =
            for ind in 0..matrixSize*matrixSize - 1 do
                if curArr.[ind] = 0.0 && updArr.[ind] > 0.0
                then
                    isChanged := true
                    let i = ind / matrixSize
                    let j = ind - i * matrixSize
                    matrixSetValue matrix i j 1.0

        let multArrays (from1: float []) (from2: float []) =

                let transa = cublasOperation_t.CUBLAS_OP_N
                let transb = cublasOperation_t.CUBLAS_OP_N

                let dalpha = 1.
                let dbeta = 0.

                let multiplicationResult =               
                    
                    mult1.Scatter(from1)
                    mult2.Scatter(from2)

                    CUBLAS.Default.Dgemm(transa, 
                                            transb, 
                                            matrixSize, 
                                            matrixSize, 
                                            matrixSize, 
                                            dalpha,
                                            mult2.Ptr, 
                                            matrixSize, 
                                            mult1.Ptr, 
                                            matrixSize, 
                                            dbeta, 
                                            result.Ptr, 
                                            matrixSize) // mult1 and mult2 swaped because Dgemm expect column-major matrices

                    let resultArr = result.Gather()  
                    resultArr

                multiplicationResult

        let nontermPairs = allRules.ComplexTails
        for (nt1, nt2) in nontermPairs do
            let arr1 = toArray matrix.[nt1] false
            let arr2 = toArray matrix.[nt2] false
            let resultArray = multArrays arr1 arr2

            for (nonTerm, _) in allRules.HeadsByComplexTail (nt1, nt2) do
                unionArrays matrix.[nonTerm] (toArray matrix.[nonTerm] false) resultArray


    let sparseCudaGemm (matrix1 : MySparseMatrix) (matrix2 : MySparseMatrix) matrixSize =
        let nnzA = matrix1.Nnz
        let nnzB = matrix2.Nnz

        let csrValA = matrix1.CsrVal
        let csrRowA = matrix1.CsrRow
        let csrColIndA = matrix1.CsrColInd
        let csrValB = matrix2.CsrVal
        let csrRowB = matrix2.CsrRow
        let csrColIndB = matrix2.CsrColInd

        let sparsecntx = new cusparseContext()
        let mutable refcnt = ref sparsecntx
        CudaSparseNativeMethods.cusparseCreate(refcnt) |> ignore

        let transa = cusparseOperation.NonTranspose
        let transb = cusparseOperation.NonTranspose
        let descrA = new cusparseMatDescr()      
        let descrB = new cusparseMatDescr()       
        let descrC = new cusparseMatDescr()       
        let refdescrA = ref descrA
        CudaSparseNativeMethods.cusparseCreateMatDescr(refdescrA) |> ignore
        let refdescrB = ref descrB
        CudaSparseNativeMethods.cusparseCreateMatDescr(refdescrB) |> ignore
        let refdescrC = ref descrC
        CudaSparseNativeMethods.cusparseCreateMatDescr(refdescrC) |> ignore

        let mutable csrValPtrA : CudaDeviceVariable<float> = new CudaDeviceVariable<float>(new SizeT(nnzA))
        csrValPtrA.CopyToDevice(csrValA)
        let mutable csrRowPtrA : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(matrixSize + 1))
        csrRowPtrA.CopyToDevice(csrRowA)
        let mutable csrColIndPtrA : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(nnzA))
        csrColIndPtrA.CopyToDevice(csrColIndA)
        let mutable csrValPtrB : CudaDeviceVariable<float> = new CudaDeviceVariable<float>(new SizeT(nnzB))
        csrValPtrB.CopyToDevice(csrValB)
        let mutable csrRowPtrB : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(matrixSize + 1))
        csrRowPtrB.CopyToDevice(csrRowB)
        let mutable csrColIndPtrB : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(nnzB))
        csrColIndPtrB.CopyToDevice(csrColIndB)

        let mutable csrRowPtrC : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(matrixSize + 1))
        let mutable nnzTotalDevHostPtr : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(1))

        let nnzC = ref 0

        let status1 = CudaSparseNativeMethods.cusparseXcsrgemmNnz(!refcnt, transa, transb, matrixSize, matrixSize, matrixSize,
                                                !refdescrA, nnzA, csrRowPtrA.DevicePointer, csrColIndPtrA.DevicePointer,
                                                !refdescrB, nnzB, csrRowPtrB.DevicePointer, csrColIndPtrB.DevicePointer,
                                                !refdescrC, csrRowPtrC.DevicePointer, nnzTotalDevHostPtr.DevicePointer)


        if nnzTotalDevHostPtr <> null then
            nnzTotalDevHostPtr.CopyToHost(nnzC)
        else
            printfn "null nnzTotalDevHostPtr"

        printfn "%i" !nnzC

        let csrRowC = Array.init (matrixSize + 1) (fun x -> 0)
        csrRowPtrC.CopyToHost(csrRowC)

        let mutable csrColIndPtrC : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(!nnzC))
        let mutable csrValPtrC : CudaDeviceVariable<float> = new CudaDeviceVariable<float>(new SizeT(!nnzC))
        
        let status2 = CudaSparseNativeMethods.cusparseDcsrgemm(!refcnt, transa, transb, matrixSize, matrixSize, matrixSize,
                                                !refdescrA, nnzA, csrValPtrA.DevicePointer, csrRowPtrA.DevicePointer, csrColIndPtrA.DevicePointer,
                                                !refdescrB, nnzB, csrValPtrB.DevicePointer, csrRowPtrB.DevicePointer, csrColIndPtrB.DevicePointer,
                                                !refdescrC, csrValPtrC.DevicePointer, csrRowPtrC.DevicePointer, csrColIndPtrC.DevicePointer)

        
        printfn "%i" !nnzC
        let csrValC = Array.init !nnzC (fun x -> 0.0)        
        let csrColIndC = Array.init !nnzC (fun x -> 0)

        csrValPtrC.CopyToHost(csrValC)
        csrRowPtrC.CopyToHost(csrRowC)
        csrColIndPtrC.CopyToHost(csrColIndC)


        let resultMatrix = new MySparseMatrix(matrixSize, !nnzC, csrValC, csrRowC, csrColIndC)

        resultMatrix

    let sparseCudaGeam (matrix1 : MySparseMatrix) (matrix2 : MySparseMatrix) matrixSize =
        let nnzA = matrix1.Nnz
        let nnzB = matrix2.Nnz

        let csrValA = matrix1.CsrVal
        let csrRowA = matrix1.CsrRow
        let csrColIndA = matrix1.CsrColInd
        let csrValB = matrix2.CsrVal
        let csrRowB = matrix2.CsrRow
        let csrColIndB = matrix2.CsrColInd

        let sparsecntx = new cusparseContext()
        let mutable refcnt = ref sparsecntx
        CudaSparseNativeMethods.cusparseCreate(refcnt) |> ignore

        let transa = cusparseOperation.NonTranspose
        let transb = cusparseOperation.NonTranspose
        let descrA = new cusparseMatDescr()      
        let descrB = new cusparseMatDescr()       
        let descrC = new cusparseMatDescr()       
        let refdescrA = ref descrA
        CudaSparseNativeMethods.cusparseCreateMatDescr(refdescrA) |> ignore
        let refdescrB = ref descrB
        CudaSparseNativeMethods.cusparseCreateMatDescr(refdescrB) |> ignore
        let refdescrC = ref descrC
        CudaSparseNativeMethods.cusparseCreateMatDescr(refdescrC) |> ignore

        let mutable csrValPtrA : CudaDeviceVariable<float> = new CudaDeviceVariable<float>(new SizeT(nnzA))
        csrValPtrA.CopyToDevice(csrValA)
        let mutable csrRowPtrA : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(matrixSize + 1))
        csrRowPtrA.CopyToDevice(csrRowA)
        let mutable csrColIndPtrA : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(nnzA))
        csrColIndPtrA.CopyToDevice(csrColIndA)
        let mutable csrValPtrB : CudaDeviceVariable<float> = new CudaDeviceVariable<float>(new SizeT(nnzB))
        csrValPtrB.CopyToDevice(csrValB)
        let mutable csrRowPtrB : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(matrixSize + 1))
        csrRowPtrB.CopyToDevice(csrRowB)
        let mutable csrColIndPtrB : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(nnzB))
        csrColIndPtrB.CopyToDevice(csrColIndB)

        let mutable csrRowPtrC : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(matrixSize + 1))
        let mutable nnzTotalDevHostPtr : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(1))

        let nnzC = ref 0

        let status1 = CudaSparseNativeMethods.cusparseXcsrgeamNnz(!refcnt, matrixSize, matrixSize,
                                                !refdescrA, nnzA, csrRowPtrA.DevicePointer, csrColIndPtrA.DevicePointer,
                                                !refdescrB, nnzB, csrRowPtrB.DevicePointer, csrColIndPtrB.DevicePointer,
                                                !refdescrC, csrRowPtrC.DevicePointer, nnzTotalDevHostPtr.DevicePointer)

        if nnzTotalDevHostPtr <> null then
            nnzTotalDevHostPtr.CopyToHost(nnzC)
        else
            printfn "null nnzTotalDevHostPtr"

        printfn "%i" !nnzC

        let csrRowC = Array.init (matrixSize + 1) (fun x -> 0)
        csrRowPtrC.CopyToHost(csrRowC)

        let mutable csrColIndPtrC : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(!nnzC))
        let mutable csrValPtrC : CudaDeviceVariable<float> = new CudaDeviceVariable<float>(new SizeT(!nnzC))

        let mutable alpha_dev : CudaDeviceVariable<float> = new CudaDeviceVariable<float>(new SizeT(1))
        let mutable beta_dev : CudaDeviceVariable<float> = new CudaDeviceVariable<float>(new SizeT(1))
        let alpha_host = Array.init 1 (fun x -> 1.0)
        let beta_host = Array.init 1 (fun x -> 1.0)
        alpha_dev.CopyToDevice(alpha_host)
        beta_dev.CopyToDevice(beta_host)
        

        let status2 = CudaSparseNativeMethods.cusparseDcsrgeam(!refcnt, matrixSize, matrixSize, alpha_dev.DevicePointer,
                                                !refdescrA, nnzA, csrValPtrA.DevicePointer, csrRowPtrA.DevicePointer, csrColIndPtrA.DevicePointer,
                                                beta_dev.DevicePointer, !refdescrB, nnzB, csrValPtrB.DevicePointer, csrRowPtrB.DevicePointer, csrColIndPtrB.DevicePointer,
                                                !refdescrC, csrValPtrC.DevicePointer, csrRowPtrC.DevicePointer, csrColIndPtrC.DevicePointer)

        
        printfn "%i" !nnzC
        let csrValC = Array.init !nnzC (fun x -> 0.0)        
        let csrColIndC = Array.init !nnzC (fun x -> 0)

        csrValPtrC.CopyToHost(csrValC)
        csrRowPtrC.CopyToHost(csrRowC)
        csrColIndPtrC.CopyToHost(csrColIndC)

        let resultMatrix = new MySparseMatrix(matrixSize, !nnzC, csrValC, csrRowC, csrColIndC)
        resultMatrix
        
    

    let sparseCudaSquareMatrix (matrix: ParsingMatrix<MySparseMatrix>) (allRules: RulesHolder) isChanged matrixSize =
        let nontermPairs = allRules.ComplexTails
        for (nt1, nt2) in nontermPairs do
            let matrix1 = matrix.[nt1]
            let matrix2 = matrix.[nt2]

            let resultMatrix = sparseCudaGemm matrix1 matrix2 matrixSize
            
            for (nonTerm, _) in allRules.HeadsByComplexTail (nt1, nt2) do
                let nnz = matrix.[nonTerm].Nnz

                let finalMatrix = sparseCudaGeam matrix.[nonTerm] resultMatrix matrixSize
                if (nnz <> finalMatrix.Nnz)
                then
                    matrix.Remove(nonTerm) |> ignore
                    matrix.Add(nonTerm, finalMatrix)
                    isChanged := true

    (*let sparseCudaSquareMatrix_test =

        let csrValA = Array.init 4 (fun x -> 0.0)
        let csrRowA = Array.init 5 (fun x -> 0)
        let csrColIndA = Array.init 4 (fun x -> 0)
        let csrValB = Array.init 4 (fun x -> 0.0)
        let csrRowB = Array.init 5 (fun x -> 0)
        let csrColIndB = Array.init 4 (fun x -> 0)

        csrValA.[0] <- 5.0
        csrValA.[1] <- 8.0
        csrValA.[2] <- 3.0
        csrValA.[3] <- 6.0
        csrValB.[0] <- 5.0
        csrValB.[1] <- 8.0
        csrValB.[2] <- 3.0
        csrValB.[3] <- 6.0
        csrRowA.[0] <- 0
        csrRowA.[1] <- 0
        csrRowA.[2] <- 2
        csrRowA.[3] <- 3
        csrRowA.[4] <- 4
        csrRowB.[0] <- 0
        csrRowB.[1] <- 0
        csrRowB.[2] <- 2
        csrRowB.[3] <- 3
        csrRowB.[4] <- 4
        csrColIndA.[0] <- 0
        csrColIndA.[1] <- 1
        csrColIndA.[2] <- 2
        csrColIndA.[3] <- 1
        csrColIndB.[0] <- 0
        csrColIndB.[1] <- 1
        csrColIndB.[2] <- 2
        csrColIndB.[3] <- 1

        let sparsecntx = new cusparseContext()
        let mutable refcnt = ref sparsecntx
        CudaSparseNativeMethods.cusparseCreate(refcnt) |> ignore

        let transa = cusparseOperation.NonTranspose
        let transb = cusparseOperation.NonTranspose
        let descrA = new cusparseMatDescr()      
        let descrB = new cusparseMatDescr()       
        let descrC = new cusparseMatDescr()       
        let refdescrA = ref descrA
        CudaSparseNativeMethods.cusparseCreateMatDescr(refdescrA) |> ignore
        let refdescrB = ref descrB
        CudaSparseNativeMethods.cusparseCreateMatDescr(refdescrB) |> ignore
        let refdescrC = ref descrC
        CudaSparseNativeMethods.cusparseCreateMatDescr(refdescrC) |> ignore

        let mutable csrValPtrA : CudaDeviceVariable<float> = new CudaDeviceVariable<float>(new SizeT(4))
        csrValPtrA.CopyToDevice(csrValA)
        let mutable csrRowPtrA : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(5))
        csrRowPtrA.CopyToDevice(csrRowA)
        let mutable csrColIndPtrA : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(4))
        csrColIndPtrA.CopyToDevice(csrColIndA)
        let mutable csrValPtrB : CudaDeviceVariable<float> = new CudaDeviceVariable<float>(new SizeT(4))
        csrValPtrB.CopyToDevice(csrValB)
        let mutable csrRowPtrB : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(5))
        csrRowPtrB.CopyToDevice(csrRowB)
        let mutable csrColIndPtrB : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(4))
        csrColIndPtrB.CopyToDevice(csrColIndB)
        
        let mutable csrRowPtrC : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(5))
        let mutable nnzTotalDevHostPtr : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(1))

        let nnzC = ref 0

        let status1 = CudaSparseNativeMethods.cusparseXcsrgemmNnz(!refcnt, transa, transb, 4, 4, 4, !refdescrA, 4, csrRowPtrA.DevicePointer, csrColIndPtrA.DevicePointer,
                                                     !refdescrB, 4, csrRowPtrB.DevicePointer, csrColIndPtrB.DevicePointer,
                                                     !refdescrC, csrRowPtrC.DevicePointer, nnzTotalDevHostPtr.DevicePointer)

        if nnzTotalDevHostPtr <> null then
            nnzTotalDevHostPtr.CopyToHost(nnzC)
        else
            printfn "null nnzTotalDevHostPtr"

        printfn "%i" !nnzC

        let csrRowC = Array.init 5 (fun x -> 0)
        csrRowPtrC.CopyToHost(csrRowC)

        let mutable csrColIndPtrC : CudaDeviceVariable<int> = new CudaDeviceVariable<int>(new SizeT(!nnzC))
        let mutable csrValPtrC : CudaDeviceVariable<float> = new CudaDeviceVariable<float>(new SizeT(!nnzC))
        
        let status2 = CudaSparseNativeMethods.cusparseDcsrgemm(!refcnt, transa, transb, 4, 4, 4, !refdescrA, 4, csrValPtrA.DevicePointer, csrRowPtrA.DevicePointer, csrColIndPtrA.DevicePointer,
                                                    !refdescrB, 4, csrValPtrB.DevicePointer, csrRowPtrB.DevicePointer, csrColIndPtrB.DevicePointer,
                                                    !refdescrC, csrValPtrC.DevicePointer, csrRowPtrC.DevicePointer, csrColIndPtrC.DevicePointer)

        
        printfn "%i" !nnzC
        let csrValC = Array.init !nnzC (fun x -> 0.0)
        
        let csrColIndC = Array.init !nnzC (fun x -> 0)

        csrValPtrC.CopyToHost(csrValC)
        csrRowPtrC.CopyToHost(csrRowC)
        csrColIndPtrC.CopyToHost(csrColIndC)

        ()*)
        

    

    let recognizeGraph<'MatrixType, 'InnerType when 'InnerType : comparison> (graph:AdjacencyGraph<int, TaggedEdge<int, int<AbstractAnalysis.Common.token>>>)
                  (squareMatrix:ParsingMatrix<'MatrixType> -> RulesHolder -> bool ref -> int  -> unit)
                  (allRules: RulesHolder)
                  nonterminals
                  S 
                  createEmptyMatrix 
                  matrixSetValue 
                  (innerOne: 'InnerType) =
        let parsingMatrix, vertexToInt = initParsingMatrix<'MatrixType, 'InnerType> graph allRules nonterminals createEmptyMatrix matrixSetValue innerOne
//        printfn("Matrix initialized")
        let matrixSize = graph.VertexCount
        let isChanged = ref true
        let mutable multCount = 0

        while !isChanged do
//           printfn("Multiplication step started")
            isChanged := false
            squareMatrix parsingMatrix allRules isChanged matrixSize
            multCount <- multCount + 1

        (parsingMatrix.[S], vertexToInt, multCount)    

    let graphParse<'MatrixType, 'InnerType when 'InnerType : comparison> (graph:AdjacencyGraph<int, TaggedEdge<int, int<AbstractAnalysis.Common.token>>>)
                  squareMatrix
                  (loadIL:t<Source.t, Source.t>)
                  tokenToInt 
                  createEmptyMatrix 
                  matrixSetValue
                  (innerOne: 'InnerType) =
        let grammar = loadIL.grammar
        let mutable tokensCount = 0
        let S = ref (NonTerminal "")
        let nonterminals = new ResizeArray<NonTerminal>()
        let crl = new Dictionary<NonTerminal * NonTerminal, ResizeArray<NonTerminal*Probability.T>>()
        let srl = new Dictionary<int<AbstractAnalysis.Common.token>, ResizeArray<NonTerminal*Probability.T>>()
        let crl_result = new Dictionary<NonTerminal * NonTerminal, (NonTerminal * Probability.T) list>()
        let srl_result = new Dictionary<int<AbstractAnalysis.Common.token>, (NonTerminal * Probability.T) list>()
        let erl_result: NonTerminal list = []

        let probOne = Probability.create 1.0

        for module' in grammar do
            for r in module'.rules do
                let nonterm = NonTerminal <| Source.toString r.name
                if not <| nonterminals.Contains nonterm
                then
                    nonterminals.Add nonterm
                    if r.isStart
                    then
                        S := nonterm

                match r.body with
                | PSeq([elem],_,_) ->
                    match elem.rule with
                    | PToken src ->
                        let token = Source.toString src
                        let intToken = tokenToInt token
                        if not <| srl.ContainsKey intToken
                        then
                            srl.Add(intToken, new ResizeArray<NonTerminal*Probability.T>())
                        if not <| srl.[intToken].Contains (nonterm, probOne)
                        then
                            srl.[intToken].Add (nonterm, probOne)
                    | _ ->
                        failwith "Given grammar is not in normal form."
                        
                | PSeq([e1; e2],_,_) ->
                    match e1.rule, e2.rule with 
                    | PRef (name1, _), PRef (name2, _) ->
                        let nonterm1 = NonTerminal <| Source.toString name1
                        if not <| nonterminals.Contains nonterm1
                        then
                            nonterminals.Add nonterm1
                        let nonterm2 = NonTerminal <| Source.toString name2
                        if not <| nonterminals.Contains nonterm2
                        then
                            nonterminals.Add nonterm2
                        if not <| crl.ContainsKey (nonterm1, nonterm2)
                        then
                            crl.Add((nonterm1, nonterm2), new ResizeArray<NonTerminal*Probability.T>())
                        if not <| crl.[(nonterm1, nonterm2)].Contains (nonterm, probOne)
                        then
                            crl.[(nonterm1, nonterm2)].Add (nonterm, probOne)                     
                    | _ -> failwith "Given grammar is not in normal form."               
                | _ -> failwith "Given grammar is not in normal form."

        for key in crl.Keys do
            let list = Seq.toList crl.[key]
            crl_result.Add(key, list)
        for key in srl.Keys do
            let list = Seq.toList srl.[key]
            srl_result.Add(key, list)
        
        let rulesHolder = new RulesHolder(crl_result, srl_result, erl_result)

        recognizeGraph<'MatrixType, 'InnerType> graph squareMatrix rulesHolder nonterminals !S  createEmptyMatrix matrixSetValue innerOne

