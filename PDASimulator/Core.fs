namespace PDASimulator

open System.Collections.Generic
open FSharpx.Collections.Experimental
open FSharp.Collections
open Microsoft.FSharp.Collections
open System.Diagnostics
open System.Globalization
open System.Security.Claims

type full_state = uint64
type pda_state_id = uint32
type stack_data = uint32
type gss_id = uint32
type input_token = uint32

module internal Helper = 
    let pack (left: pda_state_id) (right: stack_data) =
        (uint64 left <<< 32) ||| (uint64 right)

type StackActionType = Push of stack_data | Pop | Skip
type ContextActionType = Drop | Finish | Continue

[<AllowNullLiteral>]
type PDAState(id: pda_state_id) = 
    member this.Id = id
    
type PDATransition<'State when 'State :> PDAState> = 
    {
        stackAction : StackActionType
        contextAction : ContextActionType
        target: 'State
    }

type GSSNode<'State, 'Edge, 'Node when 'State :> PDAState and 'Edge :> IAbstractInputEdge<'State, 'Edge, 'Node> and 'Node :> IAbstractInputNode<'State, 'Edge, 'Node>> private (data: stack_data, parents: ResizeArray<GSSNode<_,_,_>>) =
    let subscriptions = new HashSet<Context<'State,'Edge,'Node>>()
    
    member this.Data = data
    member this.Pop = parents
    member this.AddParent (node: GSSNode<'State,'Edge,'Node>) =
        parents.Add node
    
    member this.Subscribe context =
        subscriptions.Add context |> ignore
    
    member this.Subscriptions =
        subscriptions
    
    new (data: stack_data, parent: GSSNode<'State,'Edge,'Node>) =
        let parents = new ResizeArray<GSSNode<'State,'Edge,'Node>>()
        parents.Add parent
        GSSNode(data, parents)
        
    new (data: stack_data) =
        let parents = new ResizeArray<GSSNode<_,_,_>>()
        GSSNode(data, parents)

and IPDA<'State, 'Edge, 'Node when  'Edge :> IAbstractInputEdge<'State, 'Edge, 'Node> and 'Node :> IAbstractInputNode<'State, 'Edge, 'Node> and 'State :> PDAState> = 
    abstract member StartState: 'State
    abstract member InitialStackSymbol: stack_data
    
    abstract member Step: 'State -> stack_data -> 'Edge -> PDATransition<'State>
    abstract member Finished: Context<'State, 'Edge, 'Node> -> unit

and IAbstractInputEdge<'State, 'Edge, 'Node when 'State :> PDAState and 'Edge :> IAbstractInputEdge<'State, 'Edge, 'Node> and 'Node :> IAbstractInputNode<'State, 'Edge, 'Node>> =
    abstract member Target: 'Node
    
and IAbstractInputNode<'State, 'Edge, 'Node when 'State :> PDAState and 'Edge :> IAbstractInputEdge<'State, 'Edge, 'Node> and 'Node :> IAbstractInputNode<'State, 'Edge, 'Node>> =
    abstract member Visit: full_state -> Context<'State, 'Edge, 'Node> -> unit
    abstract member AlreadyVisitedBy: full_state -> (bool * Context<'State, 'Edge, 'Node>)
    abstract member OutgoingEdges: 'Edge seq
    
and ContextInheritanceInfo<'State, 'Edge, 'Node when 'State :> PDAState and 'Edge :> IAbstractInputEdge<'State, 'Edge, 'Node> and 'Node :> IAbstractInputNode<'State, 'Edge, 'Node>> = 
    {
        way: 'Edge
        target: Context<'State, 'Edge, 'Node>
    }

and [<CustomEquality; NoComparison>] Context<'State, 'Edge, 'Node when 'State :> PDAState and 'Edge :> IAbstractInputEdge<'State, 'Edge, 'Node> and 'Node :> IAbstractInputNode<'State, 'Edge, 'Node>> = 
    {
        id: int
    
        top: GSSNode<'State, 'Edge, 'Node>
        state: 'State
        position: 'Node
        
        parents: IDictionary<Context<'State, 'Edge, 'Node>, 'Edge>
        children: IDictionary<Context<'State, 'Edge, 'Node>, 'Edge>
        
        mutable popHistory: (ContextActionType * 'State * 'Edge) option //new state and edge that has been passed
        
        mutable survived: bool
        mutable finished: bool
    }
    
    override this.Equals obj = 
        (obj :?> Context<'State, 'Edge, 'Node>).id = this.id
        
    override this.GetHashCode() = 
        this.id

type Simulation<'State, 'Edge, 'Node when 'State :> PDAState and 'Edge :> IAbstractInputEdge<'State, 'Edge, 'Node> and 'Node :> IAbstractInputNode<'State, 'Edge, 'Node>>(pda: IPDA<'State, 'Edge, 'Node>) = 
    let contexts = Stack<Context<'State, 'Edge, 'Node>>()
    let loaded = Stack<int * Context<'State, 'Edge, 'Node>>()
    let gssRoot = new GSSNode<'State,'Edge,'Node>(pda.InitialStackSymbol)
   
    let mutable processedContexts = 0
    let mutable currentStart = 0
    
    let mutable contextsCounter = 0
    let newContextId() = 
        let id = contextsCounter
        contextsCounter <- contextsCounter + 1
        id
    
    let finals = new SortedDictionary<int, HashSet<Context<'State, 'Edge, 'Node>>>()
    
    let inheritance way target = 
        {way = way; target = target}
    
    member this.Load (uid: int) (start: 'Node) = 
        let newContext = 
            {
                id = newContextId()
                top = gssRoot
                state = pda.StartState
                position = start
                parents = new Dictionary<_, _>() 
                children = new Dictionary<_, _>()
                popHistory = None
                survived = false
                finished = false
            }
            
        loaded.Push (uid, newContext)
        start.Visit (Helper.pack pda.StartState.Id pda.InitialStackSymbol) newContext
        newContext
    
    member private this.InheritContext parent child edge =
        parent.children.[child] <- edge
        child.parents.[parent] <- edge
        
        if child.survived then
            this.MakeAlive parent
            
    member private this.NewContext top state position fullState (parent: Context<'State, 'Edge, 'Node>) (edge: 'Edge) = 
        let newContext = 
            {
                id = newContextId()
                top = top
                state = state
                position = position
                parents = new Dictionary<_,_>()
                children = new Dictionary<_,_>()
                popHistory = None
                survived = false
                finished = false
            }
        
        this.InheritContext parent newContext edge
        contexts.Push newContext
        position.Visit fullState newContext
        newContext
    
    member private this.MakeAlive context =
        if not context.survived then
            let survived = new Stack<Context<'State, 'Edge, 'Node>>()
            survived.Push context
            
            while survived.Count > 0 do
                let top = survived.Pop()
                
                if not top.survived then
                    top.survived <- true
                    
                    for pair in top.parents do
                    survived.Push pair.Key
    
    member private this.ProcessFinal context = 
        context.finished <- true
        this.MakeAlive context
        finals.[currentStart].Add context |> ignore
        pda.Finished context
    
    member private this.ProcessPush (context: Context<'State, 'Edge, 'Node>) (newState: 'State) (data: stack_data) (edge: 'Edge) =
        let newPosition = edge.Target
        let full_state = Helper.pack newState.Id data
        let exists, previous = newPosition.AlreadyVisitedBy full_state
        
        if exists then
            this.InheritContext context previous edge
            previous.top.AddParent context.top
            
            for subscription in previous.top.Subscriptions do
                if subscription.popHistory.IsSome then
                    let (contextAction, historyState, historyEdge) = subscription.popHistory.Value
                    let referencedContexts = this.ProcessPop subscription contextAction historyState historyEdge false
                    for reference in referencedContexts do
                        if contextAction = Finish then this.ProcessFinal reference
            
            previous
        else
            let newTop = new GSSNode<_,_,_>(data, context.top)
            this.NewContext newTop newState newPosition full_state context edge
    
    member private this.ProcessSkip (context: Context<'State, 'Edge, 'Node>) (newState: 'State) (edge: 'Edge) =
        let newPosition = edge.Target
        let full_state = Helper.pack newState.Id context.top.Data
        let exists, previous = newPosition.AlreadyVisitedBy full_state
        
        if exists then
            this.InheritContext context previous edge
            previous
        else
            this.NewContext context.top newState newPosition full_state context edge
    
    member private this.ProcessPop (context: Context<'State, 'Edge, 'Node>) (contextAction: ContextActionType) (newState: 'State) (edge: 'Edge) (subscribe: bool) =
        let newPosition = edge.Target
        
        if subscribe then
            context.top.Subscribe context
            context.popHistory <- Some (contextAction, newState, edge)
            
        context.top.Pop
        |> ResizeArray.map
            (
                fun newTop -> 
                    let full_state = Helper.pack newState.Id newTop.Data
                    let exists, previous = newPosition.AlreadyVisitedBy full_state
                    
                    if exists then
                        this.InheritContext context previous edge
                        previous
                    else
                    this.NewContext newTop newState newPosition full_state context edge
            )
    
    member private this.ProcessTransition (context: Context<'State, 'Edge, 'Node>) (transition: PDATransition<'State>) (edge: 'Edge) = 
        if transition.contextAction <> Drop then
            match transition.stackAction with
            | Push data -> 
                this.ProcessPush context transition.target data edge
                |> fun newContext -> if transition.contextAction = Finish then this.ProcessFinal newContext
            | Skip ->
                this.ProcessSkip context transition.target edge
                |> fun newContext -> if transition.contextAction = Finish then this.ProcessFinal newContext
            | Pop -> 
                this.ProcessPop context transition.contextAction transition.target edge true
                |> ResizeArray.iter (fun newContext -> if transition.contextAction = Finish then this.ProcessFinal newContext)
    
    member private this.Step() = 
        let currentContext = contexts.Pop()
        
        if not currentContext.finished then
            let outgoingEdges = currentContext.position.OutgoingEdges
            let first = null
            
            let state = currentContext.state
            let gssTop = currentContext.top
            let stackSymbol = gssTop.Data
            
            for edge in outgoingEdges do
            let transition = pda.Step state stackSymbol edge
            this.ProcessTransition currentContext transition edge
    
    member this.GetFinals id =
        finals.[id]

    member this.Run() =
        while loaded.Count > 0 do
            let (uid, start) = loaded.Pop()
            
            currentStart <- uid
            finals.[uid] <- new HashSet<Context<'State, 'Edge, 'Node>>()
            contexts.Push start
            
            while contexts.Count > 0 do
                this.Step()