namespace LockChecker.Graph

open System.Collections.Generic
open System.Runtime.Serialization

[<DataContract>]
type PassedParameter = 
    {
        [<field: DataMember(Name = "id")>]
        id: int
        
        // Value:
        [<field: DataMember(Name = "method")>]
        method: string
        
        [<field: DataMember(Name = "localParameter")>]
        parameter: int
    }

[<DataContract>]
type CallInfo =
    {
        [<field: DataMember(Name = "callId")>] 
        callId: int
    
        [<field: DataMember(Name = "parameter")>]
        calledParameter: int
        
        [<field: DataMember(Name = "target")>]
        target: string
        
        [<field: DataMember(Name = "passedParameters")>]
        passedParameters: PassedParameter [] 
        
        [<field: DataMember(Name = "decoderInfo")>]
        decoderInfo: string
    }

type ControlFlowGraphBuilder(graph: ControlFlowGraph) =
    let localToGlobalMap = new SortedDictionary<int<local_state>, int<state>>()
    
    let queuedCallInfos = new SortedDictionary<int, CallInfo>()
    let queuedActions = new Queue<unit -> unit>()
    
    let assertTrue condition = assert condition
    
    let getGlobalId (local: int<local_state>) =
        let exists, id = localToGlobalMap.TryGetValue local
        
        if exists then
            id
        else
            let id = graph.GetFreeStateId()
            localToGlobalMap.Add (local, id)
            id
    
    let processParameter (owner: string) (target: string) (parameter: PassedParameter) =
        if parameter.parameter <> -1 then
            graph.GetOrCreateDelegateParameter owner parameter.parameter |> ignore
            graph.AddDelegateParameterPassing owner parameter.parameter target parameter.id |> ignore
        else 
            assert (parameter.method.Length > 0)
            graph.AddDelegateInstancePassing owner parameter.method target parameter.id
    
    let processCallInfo (owner: string) (callInfo: CallInfo) (source: int<state>) (target: int<state>) =
        if callInfo.calledParameter <> -1 then
            queuedActions.Enqueue (fun () ->
                graph.AddSubstitution owner callInfo.calledParameter source target callInfo.decoderInfo |> assertTrue)
                
            [||]
        else
            let targetStart, targetFinal = graph.GetOrCreateMethodBoundStates callInfo.target
            
            let newEdge = {startNode = source; label = "I"; endNode = target}
            
            callInfo.passedParameters |> Array.iter (processParameter owner callInfo.target)
            
            let callId = graph.GetFreeCallId()
            
            let callLabel = "C" + callId.ToString()
            let returnLabel = "RT" + callId.ToString()
            
            let modifiedDecoderInfo = callInfo.decoderInfo + " " + callInfo.target
            graph.SetDecoderInfo callLabel modifiedDecoderInfo
            
            ([|{startNode = source; label = callLabel; endNode = targetStart}; 
               {startNode = targetFinal; label = returnLabel; endNode = target}|])

    let globalizeEdge (owner: string) (edge: RawEdge): (Edge []) =
        let source = getGlobalId edge.startNode
        let target = getGlobalId edge.endNode
        
        if edge.label.StartsWith "I" then
            let idSubs = edge.label.Substring 1
            let id = int idSubs
            let callInfo = queuedCallInfos.[id]
            queuedCallInfos.Remove id |> assertTrue
            
            let newEdge = {startNode = source; label = "I"; endNode = target}
            
            Array.append [|newEdge|] (processCallInfo owner callInfo source target)
        else
            let newEdge = {startNode = source; label = edge.label; endNode = target}
            ([|newEdge|])
        
    member this.UpdateMethod (method: Method) (edges: RawEdge []) (callInfos: CallInfo []) =
        callInfos |> Array.iter (fun info -> queuedCallInfos.Add (info.callId, info))
        
        let startState, finalState = graph.GetOrCreateMethodBoundStates method.methodName
        graph.ClearMethod method.methodName
        
        localToGlobalMap.Clear()
        localToGlobalMap.Add (method.startNode, startState)
        
        if (method.startNode <> method.finalNode) then
            localToGlobalMap.Add (method.finalNode, finalState)
        else
            assert (edges.Length = 0)
        
        let globalizedEdges = 
            if edges.Length = 0 then
                [|{startNode = startState; label = "e"; endNode = finalState}|]
            else
                edges |> Array.collect (globalizeEdge method.methodName)
        
        graph.FillMethod method.methodName globalizedEdges
        
        while queuedActions.Count > 0 do
            (queuedActions.Dequeue())()
        
        method.inheritedFrom
        |> Array.iter (fun basic -> graph.AddInheritance basic method.methodName)
        
    member this.UpdateFileInfo (fileName: string) (newMethods: Set<string>) =
        graph.UpdateFileInfo fileName newMethods
    
    member this.AddDecoderInfo key value =
        graph.SetDecoderInfo key value