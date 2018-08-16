namespace LockChecker.Graph

open AbstractAnalysis.Common
open System
open System.Collections.Generic
open System.Diagnostics

open System.Collections.Generic
open System.IO
open QuickGraph
open System.Runtime.Serialization
open System.Runtime.CompilerServices
(*

type QuickEdge(rawEdge: RawEdge) = 
    inherit TaggedEdge<int, string>(rawEdge.startNode, rawEdge.endNode, rawEdge.label)
    
    let mutable token = -1<token>
    
    member this.Token = token
    member this.SetToken newToken = token <- newToken
    
    override this.Equals obj =
        let edge = obj :?> QuickEdge
        
        edge.Source = this.Source && edge.Target = this.Target && edge.Tag = this.Tag
        
    override this.GetHashCode() =
        this.Source.GetHashCode() * this.Tag.GetHashCode() * this.Target.GetHashCode()

[<CustomEquality; NoComparison>]
type QuickMethod =
    {
        info: Method
        nodes: SortedSet<int>
    }
    
    override this.Equals obj =
        match obj with 
        | :? QuickMethod as method ->
            this.info.name = method.info.name
        | _ -> false
        
    override this.GetHashCode() =
        this.info.name.GetHashCode()
    
type QuickParserInput(starts, dynamicEdgesIndex: QuickEdge [] []) = 
    interface IParserInput with
        member this.InitialPositions = 
            starts |> Seq.map(fun x -> x * 1<positionInInput>) |> Seq.toArray

        member this.FinalPositions = 
            [||]

        [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
        member this.ForAllOutgoingEdges curPosInInput pFun =
            let rec forAllOutgoingEdgesAndEpsilons start =
                let edges = dynamicEdgesIndex.[start]
                edges |> Seq.iter
                    (
                        fun e -> 
                            if e.Token = -1<token> then
                                forAllOutgoingEdgesAndEpsilons e.Target
                            else
                                pFun e.Token (e.Target * 1<positionInInput>)
                    )
            
            forAllOutgoingEdgesAndEpsilons (int curPosInInput)

        member this.PositionToString (pos : int<positionInInput>) =
            sprintf "%i" pos

type QuickControlflowGraph() =
    inherit BidirectionalGraph<int, QuickEdge>()
    
    let files = Dictionary<string, HashSet<QuickMethod>>()
    let methods = Dictionary<string, QuickMethod>()
    let owners = SortedDictionary<int, QuickMethod>()
    
    let mutable dynamicEdgesIndex: QuickEdge [] [] = null
    
    let mutable maxNode = 0
    let mutable maxCall = 0
    let mutable maxLock = 0
    let mutable maxAssert = 0
    
    let mutable myTokenizer: string -> int<token> = fun _ -> 0<token>
    let mutable myStarts: int [] [] = null
    
    let addEdgeToStatistics (edge: QuickEdge) =
        if edge.Tag.StartsWith "C" then 
            let callId = int (edge.Tag.Substring 1)
            if (callId > maxCall) then 
                maxCall <- callId
                
        if edge.Tag.StartsWith "G" then 
            let lockId = int (edge.Tag.Substring 1)
            if (lockId > maxLock) then 
                maxLock <- lockId
                
        if edge.Tag.StartsWith "A" then 
            let assertId = int (edge.Tag.Substring 1)
            if (assertId > maxAssert) then 
                maxAssert <- assertId
    
    let addNodeToStatistics (node: int) =
        if maxNode < node then 
            maxNode <- node 
    
    let setNodeOwner method force node =
        if owners.ContainsKey node then 
            if force then 
                let previousOwner = owners.[node]
                previousOwner.nodes.Remove node |> ignore
                method.nodes.Add node |> ignore
                owners.[node] <- method
        else
            method.nodes.Add node |> ignore
            owners.[node] <- method
            
            addNodeToStatistics node
            
    member private this.TryToRemoveNode node =
        owners.Remove node |> ignore
        this.RemoveVertex node |> ignore
        
    member private this.ClearMethod name removeStart =
        let method = methods.[name]
        
        for node in method.nodes do
            if removeStart || (node <> method.info.startNode) then 
                this.TryToRemoveNode node
    
    member private this.AddMethodBody (method: Method) edges =
        let referencedNodes = SortedSet<int>()
        referencedNodes.Add method.startNode |> ignore
        referencedNodes.UnionWith method.finalNodes |> ignore
        
        edges |> Array.iter
            (
                fun rawEdge ->
                    referencedNodes.Add rawEdge.startNode |> ignore
                    referencedNodes.Add rawEdge.endNode |> ignore
                    let edge = QuickEdge rawEdge
                    addEdgeToStatistics edge
                    
                    if not (this.ContainsEdge edge) then
                        this.AddVerticesAndEdge edge |> ignore
            ) 
        
        referencedNodes
    
    interface IControlFlowGraph with
        member this.Serialize stream =
            use writer = new StreamWriter (stream)
            
            writer.WriteLine ("edges:")
            for edge in this.Edges do
                writer.WriteLine (edge.Source.ToString() + " " + edge.Tag + " " + edge.Target.ToString())
             
            writer.WriteLine ("methods:")
            for pair in methods do
                let method = pair.Value
                writer.WriteLine (method.info.name + " " + method.info.startNode.ToString())
                
                for final in method.info.finalNodes do
                    writer.Write final 
                    writer.Write ' '
                writer.WriteLine()
                
                for ref in method.nodes do
                    writer.Write ref
                    writer.Write ' '
                writer.WriteLine()
        
        member this.Deserialize stream = 
            use reader = new StreamReader (stream)
            
            let mutable state = 0
            
            while (not reader.EndOfStream) do
                let line = reader.ReadLine()
                
                if line.Length > 0 then
                    if (line = "edges:") then 
                        state <- 1
                    elif (line = "methods:") then 
                        state <- 2
                    elif (state = 1) then
                        let data = line.Split ' '
                        let edge = QuickEdge ({startNode = int data.[0]; endNode = int data.[2]; label = data.[1]})
                        addEdgeToStatistics edge
                        this.AddVerticesAndEdge edge |> ignore
                    elif (state = 2) then 
                        let finalNodes = (reader.ReadLine().Split ' ') 
                                         |> Array.filter (fun str -> str.Length > 0)
                                         |> Array.map (fun str -> int str)
                                         
                        let references = (reader.ReadLine().Split ' ') 
                                         |> Array.filter (fun str -> str.Length > 0)
                                         |> Array.map (fun str -> int str)
                                         |> fun array -> new SortedSet<int>(array)
                        
                        let data = line.Split ' '
                        let methodInfo = {name = data.[0]; startNode = int data.[1]; finalNodes = finalNodes}
                        let method = {info = methodInfo; nodes = references}
                        
                        methods.Add (method.info.name, method)
        
        member this.AddEdges (edges: RawEdge []) =
            edges |> Array.iter
                (
                    fun rawEdge ->
                        let edge = QuickEdge rawEdge
                        addEdgeToStatistics edge
                        if not (this.ContainsEdge edge) then
                            this.AddEdge edge |> ignore
                )
        
        member this.AddMethod method edges =
            let referencedNodes = this.AddMethodBody method edges
            let quickMethod = {info = method; nodes = new SortedSet<int>()}
            
            method.startNode |> this.AddVertex |> ignore
            method.startNode |> (setNodeOwner quickMethod true)
            method.finalNodes |> Seq.iter (this.AddVertex >> ignore)
            method.finalNodes |> Seq.iter (setNodeOwner quickMethod true)
            
            referencedNodes |> Seq.iter (setNodeOwner quickMethod false)
            
            methods.Add (method.name, quickMethod)
            
        member this.AlterMethod method edges =
            this.ClearMethod method.name false
            
            let referencedNodes = this.AddMethodBody method edges
            let quickMethod = {info = method; nodes = new SortedSet<int>()}
            
            method.startNode |> this.AddVertex |> ignore
            method.startNode |> (setNodeOwner quickMethod true)
            method.finalNodes |> Seq.iter (this.AddVertex >> ignore)
            method.finalNodes |> Seq.iter (setNodeOwner quickMethod true)
            
            referencedNodes |> Seq.iter (setNodeOwner quickMethod false)
            
            methods.[method.name] <- quickMethod
            
        member this.RemoveMethod name =
            this.ClearMethod name true
            methods.Remove name |> ignore
        
        member this.UpdateFileInfo fileName methodNames =
            let methods = 
                methodNames 
                |> Seq.map (fun name -> methods.[name])
                |> HashSet<QuickMethod>
                
            files.[fileName] <- methods
        
        member this.GetFileInfo fileName =
            if files.ContainsKey fileName then
                files.[fileName]
                |> Seq.map (fun method -> method.info.name)
                |> set
            else 
                Set.empty
            
        member this.GetStatistics() = 
            {
                nodes = maxNode + 1
                calls = maxCall + 1
                locks = maxLock + 1
                asserts = maxAssert + 1
            }
            
        member this.PrepareForParsing() = 
            dynamicEdgesIndex <- Array.zeroCreate (maxNode + 1)
            owners |> Seq.iter 
                (
                    fun pair -> 
                        let key = pair.Key
                        let success, edges = this.TryGetOutEdges key
                        for edge in edges do
                            if edge.Tag <> "e" then
                                edge.SetToken (myTokenizer edge.Tag)
                        dynamicEdgesIndex.[key] <- (Seq.toArray edges)
                )
            
        member this.CleanUpAfterParsing() = 
            dynamicEdgesIndex <- null
       
        member this.SetTokenizer tokenizer = 
            myTokenizer <- tokenizer
            
        member this.SetStarts starts =
            myStarts <- starts
        
        member this.SetStartFile file =
            let starts = files.[file] |> Seq.map (fun method -> method.info.startNode)
            myStarts <- [|Array.ofSeq starts|]
            
        member this.DumpTriples writer =
            for edge in this.Edges do
                writer.WriteLine (edge.Source.ToString() + " " + edge.Tag + " " + edge.Target.ToString())
            
            let statistics = (this :> IControlFlowGraph).GetStatistics()
            
            writer.WriteLine (sprintf "%i %i %i %i" statistics.nodes statistics.calls statistics.locks statistics.asserts)
            
            let starts = files |> Seq.collect (fun pair -> pair.Value |> Seq.map (fun method -> method.info.startNode))
            writer.WriteLine (String.Join (" ", (starts |> Seq.map (fun i -> i.ToString()))))
            
        member this.GetParserInputs count =
            let count = min count myStarts.Length
            let chunkSize = myStarts.Length / count
            
            [|0..count - 1|]
            |> Array.map
               (
                   fun id ->
                       let subArraySize = min (myStarts.Length - (id * chunkSize)) chunkSize
                       let starts = 
                           Array.sub myStarts (id * chunkSize) subArraySize 
                           |> Array.concat
                       QuickParserInput(starts, dynamicEdgesIndex)
                       :> IParserInput
            )
*)