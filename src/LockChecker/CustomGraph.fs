namespace LockChecker.Graph

open AbstractAnalysis.Common
open System
open System.Collections.Generic
open System.Diagnostics

open System.Collections.Generic
open QuickGraph
open System.Runtime.Serialization
open System.Runtime.CompilerServices
    
    (*
[<CustomEquality>]
[<CustomComparison>]
type Edge =
    {
        endNode: Node 
        label: string
    }
    interface IComparable with
        member this.CompareTo obj =
            let edge = obj :?> Edge
            (int this.label).CompareTo(int edge.label)
            
    override this.Equals obj =
        match obj with
        | :? Edge as edge ->
            edge.label = this.label
        | _ -> false
        
    override this.GetHashCode() =
        this.label.GetHashCode()
 
and [<CustomEquality>] [<NoComparison>] Node =
    {
        id: int
        edges: List<Edge>
        referencingNodes: SortedSet<int>
    }
    override this.Equals obj =
        match obj with
        | :? Node as node ->
            node.id = this.id
        | _ -> false
        
    override this.GetHashCode() =
        this.id
    
module Helpers =
    let emptyNode(id) = 
        { edges = new List<Edge>(); referencingNodes = null; id = id }
        
    let endOfHoleNode(id) = 
        { edges = new List<Edge>(); referencingNodes = new SortedSet<int>(); id = id }

type CustomControlFlowGraph () =
    let methodsIndex = new Dictionary<string, Method>()
    let nodesIdIndex = new SortedDictionary<int, Node>()
    let mutable dynamicIndex: Node [] = null
    
    let mutable starts: int [] = null
   
    let mutable tokenizer: string -> int<token> = fun _ -> 0<token>
    
    let mutable maxNode = 0
    let mutable maxCall = 0
    let mutable maxLock = 0
    let mutable maxAssert = 0
    
    let getOrCreateIndexedNode id provider =
        let exists, node = nodesIdIndex.TryGetValue id 
        if id > maxNode then 
            maxNode <- id
        
        if not exists then
            let newNode = provider id
            nodesIdIndex.[id] <- newNode
            newNode
        else 
            node
            
    let addEdges (rawEdges: RawEdge []) =
        let localIndex = new SortedDictionary<int, Node>()
        
        let getOrCreateLocalNode id =
            let exists, node = localIndex.TryGetValue id 
            if id > maxNode then 
                maxNode <- id
            
            if not exists then
                let exists, node = nodesIdIndex.TryGetValue id
                if exists then 
                    localIndex.[id] <- node
                    node
                else
                    let newNode = Helpers.emptyNode id
                    localIndex.[id] <- newNode
                    newNode
            else 
                node
        
        for edge in rawEdges do
            let startNode' = 
                if edge.label.StartsWith "RT" then 
                    getOrCreateIndexedNode edge.startNode Helpers.emptyNode
                else
                    getOrCreateLocalNode edge.startNode 
                    
            let endNode' = 
                if edge.label.StartsWith "C" then 
                    getOrCreateIndexedNode edge.endNode Helpers.emptyNode
                else
                    if edge.label.StartsWith "RT" then 
                        getOrCreateIndexedNode edge.endNode Helpers.endOfHoleNode
                    else
                        getOrCreateLocalNode edge.endNode 
                    
            let label' = edge.label
            
            startNode'.edges.Add {endNode = endNode'; label = label'} |> ignore
            
            if edge.label.StartsWith "RT" then
                endNode'.referencingNodes.Add edge.startNode |> ignore
                
            if edge.label.StartsWith "C" then 
                let callId = int (edge.label.Substring 1)
                if (callId > maxCall) then 
                    maxCall <- callId
                    
            if edge.label.StartsWith "G" then 
                let lockId = int (edge.label.Substring 1)
                if (lockId > maxLock) then 
                    maxLock <- lockId
                    
            if edge.label.StartsWith "A" then 
                let assertId = int (edge.label.Substring 1)
                if (assertId > maxAssert) then 
                    maxAssert <- assertId
    
    let cleanMethod (method: Method) =
        let startNode = nodesIdIndex.[method.startNode]
        startNode.edges.Clear()
        
        for holeEndId in method.holeEnds do
            let holeEnd = nodesIdIndex.[holeEndId]
            nodesIdIndex.Remove holeEndId |> ignore
            
            for referencingId in holeEnd.referencingNodes do
                let exists, referencingNode = nodesIdIndex.TryGetValue referencingId
                if exists then 
                    referencingNode.edges.RemoveAll (fun edge -> edge.endNode = holeEnd) |> ignore
                    
        for finalNodeId in method.finalNodes do
            let holeEnd = nodesIdIndex.[finalNodeId]
            nodesIdIndex.Remove finalNodeId |> ignore
        
    interface IControlFlowGraph with
        member this.AddMethod method edges =
            methodsIndex.Add (method.name, method)
            
            getOrCreateIndexedNode method.startNode Helpers.emptyNode |> ignore
            for id in method.holeEnds do
                getOrCreateIndexedNode id Helpers.endOfHoleNode |> ignore
            for id in method.finalNodes do
                getOrCreateIndexedNode id Helpers.emptyNode |> ignore
            
            addEdges edges
            
        member this.AlterMethod method edges =
            let oldMethod = methodsIndex.[method.name]
            Debug.Assert (method.startNode = oldMethod.startNode)
            
            cleanMethod oldMethod
            methodsIndex.[method.name] <- method
            
            for id in method.holeEnds do
                getOrCreateIndexedNode id Helpers.endOfHoleNode |> ignore
            for id in method.finalNodes do
                getOrCreateIndexedNode id Helpers.emptyNode |> ignore
                
            addEdges edges
        
        member this.AddEdges edges =
            addEdges edges
        
        member this.RemoveMethod name =
            let method = methodsIndex.[name]
            
            cleanMethod method
            nodesIdIndex.Remove method.startNode |> ignore
        
        member this.SetTokenizer tokenizer' =
            tokenizer <- tokenizer'
            
        member this.SetStarts starts' =
            starts <- starts'
            
        member this.PrepareForParsing() = 
            dynamicIndex <- Array.zeroCreate (maxNode + 1) 
            starts |> Array.iter (fun start -> dynamicIndex.[start] <- nodesIdIndex.[start])
            
        member this.CleanUpAfterParsing() = 
            dynamicIndex <- null
        
        member this.GetStatistics() =
            {
                nodes = maxNode + 1
                calls = maxCall + 1
                locks = maxLock + 1
                asserts = maxAssert + 1 
            }
                
    interface IParserInput with
        member this.InitialPositions = 
            starts |> Seq.map(fun x -> x * 1<positionInInput>) |> Seq.toArray
        
        member this.FinalPositions = 
            [||]

        [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
        member this.ForAllOutgoingEdges curPosInInput pFun =
            let node = dynamicIndex.[int curPosInInput]
            node.edges |> Seq.iter
                (
                    fun e -> 
                        dynamicIndex.[e.endNode.id] <- e.endNode
                        pFun (tokenizer e.label) (e.endNode.id * 1<positionInInput>)
                )

        member this.PositionToString (pos : int<positionInInput>) =
            sprintf "%i" pos
*)