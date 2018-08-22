module Yard.Generators.GLL.AbstractParser
open System 
open Microsoft.FSharp.Collections
open System.Collections.Generic
open FSharpx.Collections.Experimental

open Yard.Generators.GLL
open Yard.Generators.Common.DataStructures
open AbstractAnalysis.Common
open Yard.Generators.GLL.ParserCommon
open Yard.Generators.GLL.ParserCommon.CommonFuns
open Yard.Generators.Common.ASTGLLFSA
open YC.GLL.GSS
open YC.GLL.SPPF

type GLLParser(parser : ParserSourceGLL, input : IParserInput, buildTree : bool)= 
    let summLengths (len1 : ParseData) (len2 : ParseData) = 
        match len1, len2 with 
        | Length len1, Length len2  -> Length(len1 + len2)
        | _ -> failwith "Wrong type"
    
    let unpackNode = function
        | TreeNode x -> x
        | _ -> failwith "Wrong type"
    
    let dummy = 
        if buildTree
        then TreeNode(-1<nodeMeasure>)
        else Length(0us)
    
    let epsilon = -1<token>
    
    let gss = new GSS()
    let gssVertexInstanceHolder = new GSSVertexInstanceHolder()
    let sppf = new SPPF(parser.StartState, parser.FinalStates)
    
    let setR = new System.Collections.Generic.Stack<ContextFSA<_>>()
    
    /// Adds new context to stack (setR)
    let pushContext posInInput posInGrammar gssVertex data =
        setR.Push(new ContextFSA<_>(posInInput, posInGrammar, gssVertex, data))

    /// Adds new context to stack (setR) if it is first occurrence of this context (if SetU doesn't contain it).
    let addContext posInInput posInGrammar (gssVertex:GSSVertex) data =
        if not <| gssVertex.ContainsContext posInInput posInGrammar data
        then pushContext posInInput posInGrammar gssVertex data
    
    let rec pop (posInInput:int<positionInInput>) (gssVertex : GSSVertex) (newData : ParseData)=
        let outEdges = gss.OutEdges gssVertex |> Array.ofSeq
        
        if new PoppedData(posInInput, newData) |> gssVertex.P.Add |> not then () else
        if outEdges <> null && outEdges.Length <> 0
        then
            for e in outEdges do
                if buildTree
                then
                    let y, n = sppf.GetNodes e.Tag.StateToContinue e.Target.Nonterm e.Tag.Data newData
                    if y <> dummy
                    then
                        addContext posInInput e.Tag.StateToContinue e.Target y
                    if n <> dummy
                    then
                        pop posInInput e.Target n
                else
                    if e.Tag.StateToContinue |> parser.FinalStates.Contains
                    then
                        pop posInInput e.Target (summLengths newData e.Tag.Data)
                    addContext posInInput e.Tag.StateToContinue e.Target (summLengths newData e.Tag.Data)

    ///Creates new descriptors.(Calls when found nonterninal in rule(on current input edge, or on some of next)))
    let create (curContext:ContextFSA<_>) stateToContinue nonterm =        
        let startV = gssVertexInstanceHolder.Get(nonterm, curContext.PosInInput)
        let vertexExists, edgeExists = gss.ContainsVertexAndEdge(startV, curContext.GssVertex, stateToContinue, curContext.Data)        

        if vertexExists
        then
            if not edgeExists
            then
//                if startV.P.Count > 0
//                then 
                startV.P.SetP
                |> ResizeArray.iter(fun p -> 
                    if buildTree
                    then 
                        let y,nontermNode = sppf.GetNodes stateToContinue curContext.GssVertex.Nonterm curContext.Data p.data
                        if nontermNode <> dummy
                        then
                            let x = (sppf.Nodes.Item (int <| unpackNode nontermNode))
                            let newIndex = getRightExtension (x.getExtension())
                            pop newIndex curContext.GssVertex nontermNode
                        let x = (sppf.Nodes.Item (int <| unpackNode y))
                        let newIndex = getRightExtension (x.getExtension())
                        addContext newIndex stateToContinue curContext.GssVertex y
                    else
                        if stateToContinue |> parser.FinalStates.Contains
                        then
                            pop p.posInInput curContext.GssVertex (summLengths curContext.Data p.data)
                        addContext p.posInInput stateToContinue curContext.GssVertex (summLengths curContext.Data p.data))        
        else addContext curContext.PosInInput nonterm startV dummy

    let eatTerm (currentContext : ContextFSA<GSSVertex>) nextToken nextPosInInput nextPosInGrammar =
        if buildTree
        then
            let newR = sppf.GetNodeT nextToken currentContext.PosInInput nextPosInInput
            let y, nontermNode = sppf.GetNodes nextPosInGrammar currentContext.GssVertex.Nonterm currentContext.Data newR

            if nontermNode <> dummy
            then
                pop nextPosInInput currentContext.GssVertex nontermNode 
        
            if parser.MultipleInEdges.[int nextPosInGrammar]
            then 
                addContext nextPosInInput nextPosInGrammar currentContext.GssVertex y
            else
                pushContext nextPosInInput nextPosInGrammar currentContext.GssVertex y
        else
            if nextPosInGrammar |> parser.FinalStates.Contains
            then
                pop nextPosInInput currentContext.GssVertex (summLengths currentContext.Data (Length(1us)))
            
            if parser.MultipleInEdges.[int nextPosInGrammar]
            then 
                addContext nextPosInInput nextPosInGrammar currentContext.GssVertex (summLengths currentContext.Data (Length(1us)))
            else
                pushContext nextPosInInput nextPosInGrammar currentContext.GssVertex (summLengths currentContext.Data (Length(1us)))
    
    member this.InterruptableParseFromPositions (initialPositions : int<positionInInput> array) (isInterrupted : unit -> bool) =         
        let startContexts = 
            initialPositions
            |> Array.map(fun pos -> 
                let vertex = gssVertexInstanceHolder.Get(parser.StartState, pos)
                gss.AddVertex vertex |> ignore
                new ContextFSA<_>(pos, parser.StartState, vertex, dummy))
    
        for startContext in startContexts do
            setR.Push startContext 
            
        let startTime = ref System.DateTime.Now
    
        while (setR.Count <> 0) && (not (isInterrupted())) do
            let currentContext = setR.Pop()
            
            let possibleNontermMovesInGrammar = parser.OutNonterms.[int currentContext.PosInGrammar]
    
            /// Current state is final
            if (currentContext.Data = dummy)&&(currentContext.PosInGrammar |> parser.FinalStates.Contains)
            then 
                if buildTree
                then
                    let eps = sppf.GetNodeT epsilon currentContext.PosInInput currentContext.PosInInput
                    let _, nontermNode = sppf.GetNodes currentContext.PosInGrammar currentContext.GssVertex.Nonterm dummy eps
                    pop currentContext.PosInInput currentContext.GssVertex nontermNode
                else
                    pop currentContext.PosInInput currentContext.GssVertex dummy
            
            /// Nonterminal transitions. Move pointer in grammar. Position in input is not changed.
            for curNonterm, nextState in possibleNontermMovesInGrammar do            
                create currentContext nextState curNonterm
    
            /// Terminal transitions.
            input.ForAllOutgoingEdges
                currentContext.PosInInput
                (fun nextToken nextPosInInput -> 
                    let nextPosInGrammar = parser.StateAndTokenToNewState currentContext.PosInGrammar nextToken
                    if nextPosInGrammar <> -10<positionInGrammar>
                    then eatTerm currentContext nextToken nextPosInInput nextPosInGrammar
                       //pushContext nextPosInInput nextPosInGrammar currentContext.GssVertex (currentContext.Length + 1us)
                )            
    
    member this.GetTree () = 
        if buildTree
        then 
            Some <| new Tree<_>(sppf.GetRoots gss input.InitialPositions.[0], input.PositionToString, parser.IntToString)
        else
            None
                    
    member this.Parse () = 
        this.InterruptableParseFromPositions (input.InitialPositions) (fun () -> false)
           
    member this.FindVertices (gss:GSS) state : seq<GSSVertex> =    
        gss.Vertices
        |> Seq.filter (fun v -> v.Nonterm = state)
    
    member this.BuildAst () = 
        this.Parse()
        let tree = this.GetTree()
        let tree = if tree.IsNone then failwith "NotParsed" else tree.Value
        tree
            
    member this.GetAllSPPFRoots() = 
        this.Parse()
        sppf.GetRootsForStartAndFinal gss input.InitialPositions input.FinalPositions
    
    member this.GetAllSPPFRootsAsINodes()= 
        this.Parse()
        sppf.GetRootsForStart gss input.InitialPositions
        
    member this.GetAllSPPFRootsAsINodesInterruptable isInterrupted = 
        if input.InitialPositions.Length > 0 then
            this.InterruptableParseFromPositions (input.InitialPositions) isInterrupted
            sppf.GetRootsForStart gss input.InitialPositions
        else
            Array.empty
    
    member this.ParseMore (newStartPositions : int<positionInInput> array) isInterrupted =
        this.InterruptableParseFromPositions newStartPositions isInterrupted
        sppf.GetRootsForStart gss newStartPositions
        
    member this.ParsedHaveResultOfLength length = 
        this.Parse()
        this.FindVertices gss parser.StartState
        |> Seq.exists (fun v -> v.P.SetP |> ResizeArray.exists (fun p -> int p.posInInput = length))
    
    member this.GetAllRangesForState gss state =
        this.FindVertices gss state
        |> Seq.collect (fun v -> v.P.SetP |> Seq.map (fun poped -> v.PositionInInput, poped.posInInput))    
    
    member this.GetAllRangesForStartState() = 
        this.Parse()
        this.GetAllRangesForState gss parser.StartState
    
    member this.GetAllRangesForStateWithLength gss state =
        this.FindVertices gss state
        |> Seq.collect (fun v -> v.P.SetP |> Seq.map (fun poped -> v.PositionInInput, poped.posInInput, match poped.data with Length x -> x | TreeNode _ -> failwith "Impossible!"))
    
    member this.ParseAndGetGSS () = 
        this.Parse()
        gss
    
    member this.ParseAndGetSPPF () = 
        this.Parse()
        sppf
    
    member this.ParseAndGetAllRangesForStartStateWithLength () = 
        this.Parse()
        this.GetAllRangesForStateWithLength gss parser.StartState
        
    member this.Source =
        parser
