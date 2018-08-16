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

[<Measure>] type stateId

[<DataContract>]
type Method =
    {
        [<field: DataMember(Name="name")>]
        name: string
        
        [<field: DataMember(Name="startNode")>]
        startNode: int<stateId>
        
        [<field: DataMember(Name="finalNode")>]
        finalNode: int<stateId>
    }
    
[<DataContract>]
type RawEdge = 
    {
        [<field: DataMember(Name="s")>]
        startNode: int<stateId>
        
        [<field: DataMember(Name="l")>]
        label: string
        
        [<field: DataMember(Name="t")>]
        endNode: int<stateId>
    }

[<DataContract>]
type Substitution = 
    {
        [<field: DataMember(Name="start")>]
        startNode: int<stateId>
        
        [<field: DataMember(Name="end")>]
        endNode: int<stateId>
    }

[<DataContract>]
type Passing = 
    {
        [<field: DataMember(Name="method")>]
        method: string
        
        [<field: DataMember(Name="parameterId")>]
        parameterId: int
    }
    
[<DataContract>]
type DelegateParameterInfo = 
    {
        [<field: DataMember(Name="method")>]
        method: string
        
        [<field: DataMember(Name="parameterId")>]
        parameterId: int
        
        [<field: DataMember(Name="substitutions")>]
        substitutions: Substitution []
        
        [<field: DataMember(Name="passings")>]
        passings: Passing []
        
        [<field: DataMember(Name="implementations")>]
        implementations: string []
    }

type GraphStatistics =
    {
        nodes: int
        calls: int
        locks: int
        asserts: int
    }

[<AllowNullLiteral>]
type IGraphIndex<'key when 'key : equality> =
    abstract member AddNode: 'key -> int -> bool
    abstract member FindNode: 'key -> (bool * int)
    abstract member FindKey: int -> (bool * 'key)
    abstract member Pairs: unit -> ('key * int) seq
    
type IGraphStorage =
    abstract member CreateNode: unit -> int
    abstract member RemoveNode: int -> bool
    abstract member SetNodeLabel: int -> string -> bool
    abstract member GetNodeLabel: int -> (bool * string)
    
    abstract member AddEdge: int -> string -> int -> bool
    abstract member RemoveEdge: int -> string -> int -> bool
    
    abstract member CreateIndex<'key when 'key : equality> : string -> bool
    abstract member GetIndex<'key when 'key : equality> : string -> (bool * IGraphIndex<'key>)
    
    abstract member OutgoingEdges: int -> (string * int) []
    abstract member IncomingEdges: int -> (string * int) []
    
type ControlFlowInput(starts, dynamicEdgesIndex: (int<token> * int) [] []) = 
    interface IParserInput with
        member this.InitialPositions = 
            starts |> Seq.map(fun x -> x * 1<positionInInput>) |> Seq.toArray

        member this.FinalPositions = 
            [||]

        [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
        member this.ForAllOutgoingEdges curPosInInput pFun =
            let rec forAllOutgoingEdgesAndEpsilons start =
                let edges = dynamicEdgesIndex.[start]
                edges |> Array.iter
                    (
                        fun e -> 
                            if fst e = -1<token> then
                                forAllOutgoingEdgesAndEpsilons (snd e)
                            else
                                pFun (fst e) ((snd e) * 1<positionInInput>)
                    )
            
            forAllOutgoingEdgesAndEpsilons (int curPosInInput)

        member this.PositionToString (pos : int<positionInInput>) =
            sprintf "%i" pos

type ControlFlowGraph(storage: IGraphStorage) =
    let OWNS = "owns"
    let CONTAINS = "contains"
    let STARTS_FROM = "start"
    let FINISHES_AT = "final"
    let HAS_PARAMETER = "parameter"
    let CAN_BE_INSTANTIATED_WITH = "instance"
    let PASSED_THROUGH_TO = "pass"
    let SUBSTITUTES_TO = "substitute"
    let INVALID_NODE_ID = -1

    let mutable filesIndex: IGraphIndex<string> = null
    let mutable methodsIndex: IGraphIndex<string> = null
    let mutable denseStatesIndex: IGraphIndex<int<stateId>> = null
    
    let queuedMethods = Dictionary<string, (Method * (RawEdge []))>()
    
    let mutable maxState = 0<stateId>
    let mutable maxCall = 0
    let mutable maxLock = 0
    let mutable maxAssert = 0
    
    let addEdgeToStatistics (edge: RawEdge) =
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
    
    let addStateToStaticstics (state: int<stateId>) = 
        if maxState < state then
            maxState <- state
    
    let assertTrue condition = 
        assert condition
    
    let queryReferencedNodes (origin: int) (referenceType: string) =
        storage.OutgoingEdges origin 
        |> Array.filter (fun (label, _) -> label = referenceType)
        |> Array.map snd
    
    let queryReferencedNodesWithLabels (origin: int) (referenceType: string) (targetLabel: string) =
        storage.OutgoingEdges origin 
        |> Array.filter 
            (
                fun (edgeLabel, nodeId) -> 
                    if referenceType = edgeLabel then
                        let exists, nodeLabel = storage.GetNodeLabel nodeId
                        exists && nodeLabel = targetLabel
                    else
                        false
            )
        |> Array.map snd
   
    let addFileNode (fileName: string) =
        let nodeId = storage.CreateNode()
        storage.SetNodeLabel nodeId fileName |> assertTrue
        filesIndex.AddNode fileName nodeId |> assertTrue
        nodeId
     
    let addMethodNode (identifier: string) = 
        let nodeId = storage.CreateNode()
        storage.SetNodeLabel nodeId identifier |> assertTrue
        methodsIndex.AddNode identifier nodeId |> assertTrue
        nodeId
     
    let getOrCreateMethodNode (identifier: string) =
        let exists, nodeId = methodsIndex.FindNode identifier
        if exists then
            nodeId
        else
            addMethodNode identifier
    
    let removeMethod (identifier: string) =
        let exists, nodeId = methodsIndex.FindNode identifier 
        
        if exists then 
            queryReferencedNodes nodeId OWNS
            |> Array.iter (storage.RemoveNode >> assertTrue)
            
            storage.RemoveNode nodeId |> assertTrue
            true
        else
            false
    
    let tryAddState (owner: int) (state: int<stateId>) =
        let exists, nodeId = denseStatesIndex.FindNode state
        
        if not exists then 
            assert (owner <> INVALID_NODE_ID)
            
            addStateToStaticstics state
            
            let nodeId = storage.CreateNode()
            denseStatesIndex.AddNode state nodeId |> assertTrue
            storage.AddEdge owner OWNS nodeId |> assertTrue
            nodeId
        else 
            nodeId
    
    let setOwner (owner: int) (state: int<stateId>) =
        let exists, nodeId = denseStatesIndex.FindNode state
        assert exists
        
        let mutable counter = 0
        for edge in (storage.IncomingEdges nodeId) do
            if OWNS = fst edge then
                counter <- counter + 1
                storage.RemoveEdge (snd edge) OWNS nodeId |> assertTrue
        
        assert (counter = 1)
        
        storage.AddEdge owner OWNS nodeId |> assertTrue
    
    let setStartState (owner: int) (state: int<stateId>) = 
        let exists, nodeId = denseStatesIndex.FindNode state
        assert exists
        
        storage.AddEdge owner STARTS_FROM nodeId |> assertTrue
        setOwner owner state
    
    let setFinalState (owner: int) (state: int<stateId>) =
        let exists, nodeId = denseStatesIndex.FindNode state
        assert exists
        
        storage.AddEdge owner FINISHES_AT nodeId |> assertTrue
        setOwner owner state
    
    let addEdges (edges: RawEdge []) (owner: int) =
        for edge in edges do
            addEdgeToStatistics edge
        
            let startNode = tryAddState owner (edge.startNode)
            let endNode = tryAddState owner (edge.endNode)
            
            storage.AddEdge startNode edge.label endNode |> assertTrue
    
    let addMethod (identifier: string) =
        let methodInfo, edges = queuedMethods.[identifier]
        queuedMethods.Remove identifier |> ignore
        
        let methodNodeId = getOrCreateMethodNode methodInfo.name
        
        addEdges edges methodNodeId
        methodInfo.startNode |> tryAddState methodNodeId |> ignore
        methodInfo.startNode |> setStartState methodNodeId
        methodInfo.finalNode |> tryAddState methodNodeId |> ignore
        methodInfo.finalNode |> setFinalState methodNodeId
        
        methodNodeId
    
    let alterMethod (identifier: string) = 
        let methodInfo, edges = queuedMethods.[identifier]
        queuedMethods.Remove identifier |> ignore
        
        let exists, methodNodeId = methodsIndex.FindNode (methodInfo.name)
        assert exists
        
        let startNodeId = 
            let possibleStarts = queryReferencedNodes methodNodeId STARTS_FROM
            assert (possibleStarts.Length = 1)
            possibleStarts.[0]
            
        let finalNodeId = 
            let possibleFinals = queryReferencedNodes methodNodeId FINISHES_AT
            assert (possibleFinals.Length = 1)
            possibleFinals.[0]
        
        let allOwned = queryReferencedNodes methodNodeId OWNS
        
        let toDelete = set allOwned |> Set.remove startNodeId |> Set.remove finalNodeId
        toDelete |> Set.iter (storage.RemoveNode >> assertTrue)
        
        addEdges edges methodNodeId
        
        true
    
    member this.GetStorage = 
        storage
    
    member this.LoadIndices() =
        let success, filesIndex' = storage.GetIndex<string> "filesIndex"
        assert success
        filesIndex <- filesIndex'
            
        let success, methodsIndex' = storage.GetIndex<string> "methodsIndex"
        assert success
        methodsIndex <- methodsIndex'
        
        let success, denseStatesIndex' = storage.GetIndex<int<stateId>> "statesIndex"
        assert success
        denseStatesIndex <- denseStatesIndex'

    member this.InitStorage() =
        let success = storage.CreateIndex<string> "filesIndex"
        assert success
        
        let success = storage.CreateIndex<string> "methodsIndex"
        assert success
        
        let success = storage.CreateIndex<int<stateId>> "statesIndex"
        assert success
        
        this.LoadIndices()
    
    member this.EnqueueMethodForProcessing (method: Method) (edges: RawEdge[]) =
        queuedMethods.Add (method.name, (method, edges))
        
    member this.UpdateFileInfo (fileName: string) (newMethods: Set<string>) =
        let oldMethods = 
            (
                let exists, nodeId = filesIndex.FindNode fileName
                if exists then 
                    queryReferencedNodes nodeId "contains"
                    |> Array.map 
                        (
                            fun id -> 
                                let exists, label = storage.GetNodeLabel id
                                assert exists
                                label
                        )
                    |> set
                else
                    Set.empty
            )
            
        let removed = Set.difference oldMethods newMethods
        let updated = Set.intersect oldMethods newMethods
        let added = Set.difference newMethods oldMethods
        
        removed |> Set.iter (removeMethod >> assertTrue)
        updated |> Set.iter (alterMethod >> assertTrue)
        
        let addedMethodNodeIds = 
            added |> Seq.map (addMethod)
        
        let fileNodeId = 
            let exists, nodeId = filesIndex.FindNode fileName
            if exists then 
                nodeId
            else
                addFileNode fileName
        
        addedMethodNodeIds |> Seq.iter (storage.AddEdge fileNodeId CONTAINS >> assertTrue)
    
    member this.AddEdgePack (edges: RawEdge []) =
        addEdges edges INVALID_NODE_ID
    
    member private this.TryClearDelegateParameter (method: string) (parameterId: int) = 
        let exists, methodNodeId = methodsIndex.FindNode method
        assert exists
        
        let possibleParameterNodes = queryReferencedNodesWithLabels methodNodeId HAS_PARAMETER (parameterId.ToString())
        assert (possibleParameterNodes.Length <= 1)
        
        if possibleParameterNodes.Length = 1 then
            let parameterNodeId = possibleParameterNodes.[0]
            
            let substitutions = queryReferencedNodes parameterId SUBSTITUTES_TO
            substitutions |> Array.iter (storage.RemoveNode >> assertTrue)
            
            let edges = storage.OutgoingEdges parameterNodeId
            for edge in edges do
                storage.RemoveEdge parameterNodeId (fst edge) (snd edge) |> assertTrue
                
            true
        else
            false
    
    member this.AddDelegateParameter (method: string) (parameterId: int) =
        let exists, methodNodeId = methodsIndex.FindNode method
        assert exists
        
        let parameterNodeId = storage.CreateNode()
        storage.SetNodeLabel parameterNodeId (parameterId.ToString()) |> assertTrue
        
        storage.AddEdge methodNodeId HAS_PARAMETER parameterNodeId |> assertTrue
        
        parameterNodeId
    
    member this.AddDelegateInstance (method: string) (parameterId: int) (instance: string) =
        let exists, methodNodeId = methodsIndex.FindNode method
        assert exists
        
        let exists, instanceNodeId = methodsIndex.FindNode instance
        assert exists
        
        let possibleParameterNodes = queryReferencedNodesWithLabels methodNodeId HAS_PARAMETER (parameterId.ToString())
        assert (possibleParameterNodes.Length = 1)
        let parameterNodeId = possibleParameterNodes.[0]
        
        storage.AddEdge parameterNodeId CAN_BE_INSTANTIATED_WITH instanceNodeId
    
    member this.AddDelegateParameterPassing (caller: string) (sourceParameterId: int) (called: string) (targetParameterId: int) =
        let exists, callerId = methodsIndex.FindNode caller
        assert exists
        
        let possibleParameterNodes = queryReferencedNodesWithLabels callerId HAS_PARAMETER (sourceParameterId.ToString())
        assert (possibleParameterNodes.Length = 1)
        let sourceParameterNodeId = possibleParameterNodes.[0]
        
        let exists, calledId = methodsIndex.FindNode called
        let targetParameterNodeId = 
            if exists then
                let possibleParameterNodes = queryReferencedNodesWithLabels calledId HAS_PARAMETER (targetParameterId.ToString())
                assert (possibleParameterNodes.Length = 1)
                let parameterNodeId = possibleParameterNodes.[0]
                
                parameterNodeId
            else
                let methodNodeId = getOrCreateMethodNode called
                let parameterNodeId = this.AddDelegateParameter called targetParameterId
                
                parameterNodeId
        
        storage.AddEdge sourceParameterNodeId PASSED_THROUGH_TO targetParameterNodeId
    
    member this.AddSubstitution (method: string) (parameterId: int) (startState: int<stateId>) (finalState: int<stateId>) =
        let exists, callerId = methodsIndex.FindNode method
        assert exists
        
        let possibleParameterNodes = queryReferencedNodesWithLabels callerId HAS_PARAMETER (parameterId.ToString())
        assert (possibleParameterNodes.Length = 1)
        let parameterNodeId = possibleParameterNodes.[0]
        
        let substitutionNodeId = storage.CreateNode()
        
        let (exists, startStateNodeId) = denseStatesIndex.FindNode startState
        assert exists
        
        let (exists, finalStateNodeId) = denseStatesIndex.FindNode finalState
        assert exists
        
        storage.AddEdge parameterNodeId SUBSTITUTES_TO substitutionNodeId |> assertTrue
        storage.AddEdge substitutionNodeId STARTS_FROM startStateNodeId |> assertTrue
        storage.AddEdge substitutionNodeId FINISHES_AT finalStateNodeId |> assertTrue
        
        true
    
    member this.UpdateDelegateParameter (info: DelegateParameterInfo) =
        let exists, methodNodeId = methodsIndex.FindNode info.method
        assert exists
        
        this.TryClearDelegateParameter info.method info.parameterId |> ignore
        
        this.AddDelegateParameter info.method info.parameterId |> ignore
        
        for substitution in info.substitutions do
            this.AddSubstitution info.method info.parameterId substitution.startNode substitution.endNode |> assertTrue
        
        for passing in info.passings do
            this.AddDelegateParameterPassing info.method info.parameterId passing.method passing.parameterId |> assertTrue
        
        for implementaion in info.implementations do
            this.AddDelegateInstance info.method info.parameterId implementaion |> assertTrue
        
    member this.GetStatistics() = 
        {
            nodes = int maxState + 1
            calls = maxCall + 1
            locks = maxLock + 1
            asserts = maxAssert + 1
        }
    
    member this.DumpStatesLevel (writer: StreamWriter) = 
        for pair in denseStatesIndex.Pairs() do
            for edge in storage.OutgoingEdges (snd pair) do
                writer.WriteLine ((snd pair).ToString() + " " + (fst edge) + " " + (snd edge).ToString())
        
        let statistics = this.GetStatistics()
        
        writer.WriteLine (sprintf "%i %i %i %i" statistics.nodes statistics.calls statistics.locks statistics.asserts)
        
        let starts = 
            methodsIndex.Pairs() 
            |> Seq.map 
                (
                    fun (name, id) -> 
                        let referencedNodes = queryReferencedNodes id STARTS_FROM
                        referencedNodes.[0]
                )
        writer.WriteLine (String.Join (" ", (starts |> Seq.map (fun i -> i.ToString()))))

    member this.GetParserInput (startFile: string) (tokenizer: string -> int<token>) =
        let statistics = this.GetStatistics()
        let dynamicIndex = Array.zeroCreate (statistics.nodes)
        
        for i in [0 .. statistics.nodes - 1] do
            let exists, nodeId = denseStatesIndex.FindNode (i * 1<stateId>)
            if exists then
                dynamicIndex.[i] <- 
                    storage.OutgoingEdges nodeId
                    |> Array.map
                        (
                            fun (label, target) ->
                                let exists, newTarget = denseStatesIndex.FindKey target
                                assert exists
                                
                                let newTarget = int newTarget
                                
                                if label = "e" then
                                    (-1<token>, newTarget)
                                else 
                                    (tokenizer label, newTarget)
                        )
        
        let exists, fileNodeId = filesIndex.FindNode startFile
        assert exists
        
        let starts =
            queryReferencedNodes fileNodeId CONTAINS 
            |> Array.collect (fun methodNodeId -> queryReferencedNodes methodNodeId STARTS_FROM)
            |> Array.map (denseStatesIndex.FindKey >> (fun (exists, id) -> assert exists; int id))
        
        ControlFlowInput (starts, dynamicIndex)
        