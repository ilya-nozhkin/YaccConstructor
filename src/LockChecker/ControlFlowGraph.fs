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
open System.Text

[<Measure>] type state
[<Measure>] type local_state

[<DataContract>]
type Method = 
    {
        [<field: DataMember(Name="name")>]
        methodName: string
    
        [<field: DataMember(Name="startNode")>]
        startNode: int<local_state>
        
        [<field: DataMember(Name="finalNode")>]
        finalNode: int<local_state> 
        
        [<field: DataMember(Name="inheritedFrom")>]
        inheritedFrom: string []
    }
    
[<DataContract>]
type RawEdge = 
    {
        [<field: DataMember(Name="s")>]
        startNode: int<local_state>
        
        [<field: DataMember(Name="l")>]
        label: string
        
        [<field: DataMember(Name="t")>]
        endNode: int<local_state>
    }

type Edge = 
    {
        startNode: int<state>
        label: string
        endNode: int<state>
    }

[<DataContract>]
type Substitution = 
    {
        [<field: DataMember(Name="start")>]
        startNode: int<state>
        
        [<field: DataMember(Name="end")>]
        endNode: int<state>
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

type DenseIdsProvider() = 
    let mutable counter = 0
    let vacatedIds = Queue<int>()
    
    member this.FreeId id =
        vacatedIds.Enqueue id
    
    member this.GetFreeId() =
        if vacatedIds.Count = 0 then
            let tempId = counter
            counter <- counter + 1
            tempId
        else
            vacatedIds.Dequeue()
    
    member this.DumpStateToString() =
        use builder = new StringWriter()
        
        builder.Write counter
        builder.Write ' '
        
        let vacatedIdsArray = vacatedIds.ToArray()
        
        builder.Write (vacatedIdsArray |> Array.map (fun i -> i.ToString()) |> String.concat " ")
        
        builder.ToString()
    
    member this.RestoreStateFromString (source: string) =
        let splitted = source.Split ' ' |> Array.filter (fun entity -> entity.Length > 0)
        
        counter <- int splitted.[0]
        
        vacatedIds.Clear()
        splitted.[1..] |> Array.iter (int >> this.FreeId)

[<AllowNullLiteral>]
type IGraphIndex<'key when 'key : equality> =
    abstract member AddNode: 'key -> int -> bool
    abstract member FindNode: 'key -> (bool * int)
    abstract member FindKey: int -> (bool * 'key)
    abstract member Pairs: unit -> ('key * int) seq

[<AllowNullLiteral>]
[<AbstractClass>]
type DenseGraphIndex<'key when 'key : equality>(indexer: 'key -> int, deindexer: int -> 'key) = 
    let provider = new DenseIdsProvider()
    
    member this.Provider = provider
    
    abstract member AddNode: 'key -> int -> bool
    abstract member FindNode: 'key -> (bool * int)
    abstract member FindKey: int -> (bool * 'key)
    abstract member Pairs: unit -> ('key * int) seq
    
    // protected!!!
    member this.FreeIndex (index: int) = 
        this.Provider.FreeId index
    
    member this.GetFreeIndex() = 
        let freeId = this.Provider.GetFreeId()
        
        deindexer freeId
        
    interface IGraphIndex<'key> with
        member this.AddNode key node = this.AddNode key node
        member this.FindNode key = this.FindNode key
        member this.FindKey node = this.FindKey node
        member this.Pairs()  = this.Pairs()
    
type IGraphStorage =
    abstract member CreateNode: unit -> int
    abstract member RemoveNode: int -> bool
    abstract member SetNodeLabel: int -> string -> bool
    abstract member GetNodeLabel: int -> (bool * string)
    
    abstract member AddEdge: int -> string -> int -> bool
    abstract member RemoveEdge: int -> string -> int -> bool
    
    abstract member SetOnEdgeRemovedListener: (int -> string -> int -> unit) -> unit
    
    abstract member AddWeakEdge: int -> string -> int -> bool
    abstract member ClearWeakEdges: unit -> unit
    
    abstract member CreateIndex<'key when 'key : equality> : string -> bool
    abstract member CreateDenseIndex<'key when 'key : equality> : string -> ('key -> int) -> (int -> 'key) -> bool
    
    abstract member GetIndex<'key when 'key : equality> : string -> (bool * IGraphIndex<'key>)
    abstract member GetDenseIndex<'key when 'key : equality> : string -> (bool * DenseGraphIndex<'key>)
    
    abstract member OutgoingEdges: int -> (string * int) []
    abstract member IncomingEdges: int -> (string * int) []
    
    abstract member DumpToDot: string -> unit
    
    abstract member Serialize: StreamWriter -> unit
    abstract member Deserialize: StreamReader -> unit
    
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

//TODO: Remove unsubstituted delegate parameters
type ControlFlowGraph(storage: IGraphStorage) =
    let OWNS = "owns"
    let CONTAINS = "contains"
    let STARTS_FROM = "start"
    let FINISHES_AT = "final"
    let HAS_PARAMETER = "parameter"
    let INITIATES_PASSING = "controls"
    let INSTANTIATED_WITH = "instance"
    let PASSED_TO = "pass"
    let SUBSTITUTES_TO = "substitute"
    let INVALID_NODE_ID = -1
    
    let CALL id = "C" + id.ToString()
    let RETURN id = "RT" + id.ToString()

    let denseCallIdsProvider = DenseIdsProvider()

    let mutable filesIndex: IGraphIndex<string> = null
    let mutable methodsIndex: IGraphIndex<string> = null
    let mutable delegatesIndex: IGraphIndex<int> = null
    
    let mutable denseStatesIndex: DenseGraphIndex<int<state>> = null
    
    let mutable maxState = 0<state>
    let mutable maxCall = 0
    let mutable maxLock = 0
    let mutable maxAssert = 0
    
    let decoderInfo = Dictionary<string, string>()
    
    let addEdgeToStatistics (edge: Edge) =
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
    
    let addStateToStaticstics (state: int<state>) = 
        if maxState < state then
            maxState <- state
    
    let assertTrue condition = 
        assert condition
    
    let queryReferencedNodes (origin: int) (referenceType: string) =
        storage.OutgoingEdges origin 
        |> Array.filter (fun (label, _) -> label = referenceType)
        |> Array.map snd
        
    let queryReferencingNodes (target: int) (referenceType: string) =
        storage.IncomingEdges target 
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
    
    let clearDelegateParameterNode (parameterNodeId: int) =
        let substitutions = queryReferencedNodes parameterNodeId SUBSTITUTES_TO
        substitutions |> Array.iter (storage.RemoveNode >> assertTrue)
        
        let edges = storage.OutgoingEdges parameterNodeId
        for edge in edges do
            storage.RemoveEdge parameterNodeId (fst edge) (snd edge) |> assertTrue
            
    let tryClearDelegateParameter (method: string) (parameterId: int) = 
        let exists, methodNodeId = methodsIndex.FindNode method
        assert exists
        
        let possibleParameterNodes = queryReferencedNodesWithLabels methodNodeId HAS_PARAMETER (parameterId.ToString())
        assert (possibleParameterNodes.Length <= 1)
        
        if possibleParameterNodes.Length = 1 then
            let parameterNodeId = possibleParameterNodes.[0]
            
            clearDelegateParameterNode parameterNodeId
                
            true
        else
            false
    
    let clearMethod (identifier: string) = 
        let exists, methodNodeId = methodsIndex.FindNode identifier 
        assert exists
        
        let parameterNodes = queryReferencedNodes methodNodeId HAS_PARAMETER
        parameterNodes |> Array.iter (clearDelegateParameterNode)
        
        let initiatorNodes = queryReferencedNodes methodNodeId INITIATES_PASSING
        initiatorNodes |> Array.iter (storage.RemoveNode >> assertTrue)
        
        let owned = queryReferencedNodes methodNodeId OWNS
        let start = queryReferencedNodes methodNodeId STARTS_FROM |> fun ids -> assert (ids.Length = 1); ids.[0]
        let final = queryReferencedNodes methodNodeId FINISHES_AT |> fun ids -> assert (ids.Length = 1); ids.[0]
        
        let toDelete = set owned |> Set.remove start |> Set.remove final
        
        toDelete |> Set.iter (storage.RemoveNode >> assertTrue)
        storage.OutgoingEdges start |> Array.iter (fun (label, target) -> (storage.RemoveEdge start label target) |> assertTrue)
    
    let removeMethod (identifier: string) =
        let exists, nodeId = methodsIndex.FindNode identifier 
        
        if exists then 
            clearMethod identifier
        
            queryReferencedNodes nodeId OWNS
            |> Array.iter (storage.RemoveNode >> assertTrue)
            
            storage.RemoveNode nodeId |> assertTrue
            true
        else
            false
    
    let tryAddState (owner: int) (state: int<state>) =
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
    
    let setOwner (owner: int) (state: int<state>) =
        let exists, nodeId = denseStatesIndex.FindNode state
        assert exists
        
        let mutable counter = 0
        for edge in (storage.IncomingEdges nodeId) do
            if OWNS = fst edge then
                counter <- counter + 1
                storage.RemoveEdge (snd edge) OWNS nodeId |> assertTrue
        
        assert (counter = 1)
        
        storage.AddEdge owner OWNS nodeId |> assertTrue
    
    let setStartState (owner: int) (state: int<state>) = 
        let exists, nodeId = denseStatesIndex.FindNode state
        assert exists
        
        storage.AddEdge owner STARTS_FROM nodeId |> assertTrue
        setOwner owner state
    
    let setFinalState (owner: int) (state: int<state>) =
        let exists, nodeId = denseStatesIndex.FindNode state
        assert exists
        
        storage.AddEdge owner FINISHES_AT nodeId |> assertTrue
        setOwner owner state
    
    let addEdges (edges: Edge []) (owner: int) =
        for edge in edges do
            addEdgeToStatistics edge
        
            let startNode = tryAddState owner (edge.startNode)
            let endNode = tryAddState owner (edge.endNode)
            
            storage.AddEdge startNode edge.label endNode |> assertTrue
    
    let onEdgeRemovedListener source (label: string) target =
        if label.StartsWith "C" then
            denseCallIdsProvider.FreeId (int (label.Substring 1))
    
    member this.GetFreeStateId() = 
        denseStatesIndex.GetFreeIndex()
    
    member this.GetFreeCallId() =
        denseCallIdsProvider.GetFreeId()
    
    member this.GetStorage = 
        storage
    
    member this.PrepareStorage() =
        let success, filesIndex' = storage.GetIndex<string> "filesIndex"
        assert success
        filesIndex <- filesIndex'
            
        let success, methodsIndex' = storage.GetIndex<string> "methodsIndex"
        assert success
        methodsIndex <- methodsIndex'
        
        let success, delegatesIndex' = storage.GetIndex<int> "delegatesIndex"
        assert success
        delegatesIndex <- delegatesIndex'
        
        let success, denseStatesIndex' = storage.GetDenseIndex<int<state>> "statesIndex"
        assert success
        denseStatesIndex <- denseStatesIndex'
        
        storage.SetOnEdgeRemovedListener onEdgeRemovedListener

    member this.InitStorage() =
        let success = storage.CreateIndex<string> "filesIndex"
        assert success
        
        let success = storage.CreateIndex<string> "methodsIndex"
        assert success
        
        let success = storage.CreateIndex<int> "delegatesIndex"
        assert success
        
        let success = storage.CreateDenseIndex<int<state>> "statesIndex" (int) ((*) 1<state>)
        assert success
        
        this.PrepareStorage()
    
    member private this.InitMethodBounds (methodNodeId: int) =
        let startNode = this.GetFreeStateId()
        let finalNode = this.GetFreeStateId()
        
        startNode |> tryAddState methodNodeId |> ignore
        startNode |> setStartState methodNodeId
        finalNode |> tryAddState methodNodeId |> ignore
        finalNode |> setFinalState methodNodeId
    
    member this.InitMethod (method: string) =
        let methodNodeId = addMethodNode method
        
        this.InitMethodBounds methodNodeId
        
        methodNodeId
    
    member this.GetOrCreateMethodBounds method =
        let exists, nodeId = methodsIndex.FindNode method
        
        let methodNodeId =
            if exists then
                nodeId
            else
                this.InitMethod method
        
        let mutable possibleIds = queryReferencedNodes methodNodeId STARTS_FROM
        assert (possibleIds.Length <= 1)
        
        if (possibleIds.Length = 0) then
            this.InitMethodBounds methodNodeId
            possibleIds <- queryReferencedNodes methodNodeId STARTS_FROM
            assert (possibleIds.Length = 1)
        
        let start = possibleIds.[0]
        
        let possibleIds = queryReferencedNodes methodNodeId FINISHES_AT
        assert (possibleIds.Length = 1)
        let final = possibleIds.[0]
        
        (start, final)
    
    member this.GetOrCreateMethodBoundStates (method: string) =
        let start, final = this.GetOrCreateMethodBounds method
        
        let exists, start = denseStatesIndex.FindKey start
        assert exists
        
        let exists, final = denseStatesIndex.FindKey final
        assert exists
        
        (start, final)
    
    member this.ClearMethod (method: string) =
        clearMethod method
        
    member this.FillMethod (method: string) (edges: Edge []) =
        let exists, nodeId = methodsIndex.FindNode method
        assert exists
        
        addEdges edges nodeId
    
    member this.AddInheritance (basicMethod: string) (inheritor: string) =
        let basicStart, basicFinal = this.GetOrCreateMethodBounds basicMethod
        let inheritorStart, inheritorFinal = this.GetOrCreateMethodBounds inheritor
       
        storage.AddEdge basicStart "e" inheritorStart |> assertTrue
        storage.AddEdge inheritorFinal "e" basicFinal |> assertTrue
        
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
        
        let addedMethodNodeIds = 
            added |> Seq.map (methodsIndex.FindNode >> (fun (exists, id) -> assert exists; id))
        
        let fileNodeId = 
            let exists, nodeId = filesIndex.FindNode fileName
            if exists then 
                nodeId
            else
                addFileNode fileName
        
        addedMethodNodeIds |> Seq.iter (storage.AddEdge fileNodeId CONTAINS >> assertTrue)
    
    member this.AddEdgePack (edges: Edge []) =
        addEdges edges INVALID_NODE_ID
    
    member this.GetOrCreateDelegateParameter (method: string) (parameterId: int) =
        let methodNodeId = getOrCreateMethodNode method
        
        let possibleParameterNodes = queryReferencedNodesWithLabels methodNodeId HAS_PARAMETER (parameterId.ToString())
        assert (possibleParameterNodes.Length <= 1)
        
        if possibleParameterNodes.Length = 0 then
            let parameterNodeId = storage.CreateNode()
            storage.SetNodeLabel parameterNodeId (parameterId.ToString()) |> assertTrue
            delegatesIndex.AddNode parameterNodeId parameterNodeId |> assertTrue
            storage.AddEdge methodNodeId HAS_PARAMETER parameterNodeId |> assertTrue
            
            parameterNodeId
        else
            possibleParameterNodes.[0]
    
    member this.AddDelegateInstancePassing (method: string) (instance: string) (passedTo: string) (parameterId: int) =
        let exists, callerId = methodsIndex.FindNode method
        assert exists
        
        let instantiator = storage.CreateNode()
        
        storage.AddEdge callerId INITIATES_PASSING instantiator |> assertTrue
        storage.AddEdge instantiator INSTANTIATED_WITH (getOrCreateMethodNode instance) |> assertTrue
        storage.AddEdge instantiator PASSED_TO (this.GetOrCreateDelegateParameter passedTo parameterId) |> assertTrue
    
    member this.AddDelegateParameterPassing (caller: string) (sourceParameterId: int) (called: string) (targetParameterId: int) =
        let exists, callerId = methodsIndex.FindNode caller
        assert exists
        
        let possibleParameterNodes = queryReferencedNodesWithLabels callerId HAS_PARAMETER (sourceParameterId.ToString())
        assert (possibleParameterNodes.Length = 1)
        let sourceParameterNodeId = possibleParameterNodes.[0]
        
        let exists, calledId = methodsIndex.FindNode called
        let targetParameterNodeId = this.GetOrCreateDelegateParameter called targetParameterId
        
        storage.AddEdge sourceParameterNodeId PASSED_TO targetParameterNodeId
    
    member this.AddSubstitution (method: string) (parameterId: int) (startState: int<state>) (finalState: int<state>) (label: string) =
        let parameterNodeId = this.GetOrCreateDelegateParameter method parameterId
        
        let substitutionNodeId = storage.CreateNode()
        storage.SetNodeLabel substitutionNodeId label |> assertTrue
        
        let (exists, startStateNodeId) = denseStatesIndex.FindNode startState
        
        
        let (exists, finalStateNodeId) = denseStatesIndex.FindNode finalState
        assert exists
        
        storage.AddEdge parameterNodeId SUBSTITUTES_TO substitutionNodeId |> assertTrue
        storage.AddEdge substitutionNodeId STARTS_FROM startStateNodeId |> assertTrue
        storage.AddEdge substitutionNodeId FINISHES_AT finalStateNodeId |> assertTrue
        
        true
        
    member this.GetStatistics() = 
        {
            nodes = int maxState + 1
            calls = maxCall + 1
            locks = maxLock + 1
            asserts = maxAssert + 1
        }
    
    member this.DumpStatesLevel (writer: StreamWriter) = 
        this.GenerateWeakEdges()
    
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
        
        this.ClearWeakEdges()
    
    member private this.CollectAllPossibleInstances (visited: IDictionary<int, string list>) (delegateNode: int) : string list =
        if (visited.ContainsKey delegateNode) then
            visited.[delegateNode]
        else
            visited.Add (delegateNode, List.empty)
            
            let instances = queryReferencedNodes delegateNode INSTANTIATED_WITH
            let passings = queryReferencingNodes delegateNode PASSED_TO
            
            let leftHalf =
                instances 
                |> List.ofArray
                |> List.map (storage.GetNodeLabel >> (fun (exists, label) -> assert exists; label))
            
            let rightHalf =
                passings 
                |> List.ofArray
                |> List.collect (this.CollectAllPossibleInstances visited)
            
            let result = List.append leftHalf rightHalf 
            visited.[delegateNode] <- result 
            result
    
    member this.SetDecoderInfo key value =
        decoderInfo.[key] <- value
    
    member this.GenerateWeakEdges() = 
        let cache = new SortedDictionary<int, string list>()
        for parameter in delegatesIndex.Pairs() do
            assert (fst parameter = snd parameter)
            let parameter = snd parameter
            
            let instances = this.CollectAllPossibleInstances cache parameter
            let instanceBounds = instances |> List.map this.GetOrCreateMethodBounds
            
            let substitutions = queryReferencedNodes parameter SUBSTITUTES_TO
            let substitutionBounds = 
                substitutions
                |> Array.map
                    (
                        fun substitutionNode ->
                            let possibleNodes = queryReferencedNodes substitutionNode STARTS_FROM
                            assert (possibleNodes.Length = 1)
                            let start = possibleNodes.[0]
                            
                            let possibleNodes = queryReferencedNodes substitutionNode FINISHES_AT
                            assert (possibleNodes.Length = 1)
                            let final = possibleNodes.[0]
                            
                            let exists, label = storage.GetNodeLabel substitutionNode
                            assert exists
                            
                            (start, final, label)
                    )
            
            for instance in instanceBounds do
                for substitution in substitutionBounds do
                    let callId = this.GetFreeCallId()
                    
                    let subsStart, subsFinal, label = substitution
                    
                    decoderInfo.[CALL callId] <- label
                    
                    storage.AddWeakEdge (subsStart) (CALL callId) (fst instance) |> assertTrue
                    storage.AddWeakEdge (snd instance) (RETURN callId) (subsFinal) |> assertTrue
    
    member this.ClearWeakEdges() =
        storage.ClearWeakEdges()

    member this.GetParserInput (startFile: string) (tokenizer: string -> int<token>) =
        let statistics = this.GetStatistics()
        let dynamicIndex = Array.zeroCreate (statistics.nodes)
        
        for i in [0 .. statistics.nodes - 1] do
            let exists, nodeId = denseStatesIndex.FindNode (i * 1<state>)
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
        
    member this.GetDecoder() = 
        fun key -> decoderInfo.[key]
        
    member this.Serialize (writer: StreamWriter) = 
        writer.WriteLine "#decoder"
        
        for pair in decoderInfo do
            writer.WriteLine (sprintf "%s %s" pair.Key pair.Value)
            
        writer.WriteLine "#calls_provider"
        writer.WriteLine (denseCallIdsProvider.DumpStateToString())
            
        storage.Serialize writer
        
    member this.Deserialize (reader: StreamReader) = 
        let tryReadLine (reader: StreamReader) = 
            let peek = reader.Peek()
            if peek = int '#' || peek = -1 then
                (false, null)
            else
                (true, reader.ReadLine())
                
        let splitOnFirstOccurence (str: string) (sep: string) =
            let index = str.IndexOf sep
            (str.Substring (0, index), str.Substring (index + sep.Length))
                
        let infoLine = reader.ReadLine()
        assert (infoLine = "#decoder")
        
        Seq.initInfinite (fun _ -> tryReadLine reader)
        |> Seq.takeWhile (fun (success, _) -> success)
        |> Seq.iter 
            (
                fun (_, data) -> 
                    let key, value = splitOnFirstOccurence data " "
                    decoderInfo.Add (key, value)
            )
            
        let infoLine = reader.ReadLine()
        assert (infoLine = "#calls_provider")
        
        let providerInfo = reader.ReadLine()
        denseCallIdsProvider.RestoreStateFromString providerInfo

        storage.Deserialize reader