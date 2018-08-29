namespace PDASimulator

open System.Collections.Generic
open FSharpx.Collections.Experimental
open FSharp.Collections
open FSharpx.Collections.Experimental
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
    let pack (left: pda_state_id) (right: stack_data) : full_state =
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
    // popHistory: (ContextActionType * 'State * 'Edge) option //new state and edge that has been passed
    
    let poppers = new ResizeArray<Context<'State, 'Edge, 'Node> * ContextActionType * 'State * 'Edge>()
    let popQueue = new ResizeArray<GSSNode<'State, 'Edge, 'Node>>()
    //let mutable initiator: Context<'State, 'Edge, 'Node> option = None
    
    member this.Data = data
    member this.Pop repop = 
        if repop then 
            popQueue 
        else 
            parents
    
    (*
    member this.SetInitiator initiator' =
        if initiator.IsNone then
            initiator <- initiator'
    *)
    
    member this.AddPopper (history: Context<'State, 'Edge, 'Node> * ContextActionType * 'State * 'Edge) =
        poppers.Add history
    
    member this.AddParent (node: GSSNode<'State,'Edge,'Node>) =
        popQueue.Add node
   
    member this.AcceptNewParents() = 
        parents.AddRange popQueue
        popQueue.Clear()
    
    member this.Poppers =
        poppers
    
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

and Context<'State, 'Edge, 'Node when 'State :> PDAState and 'Edge :> IAbstractInputEdge<'State, 'Edge, 'Node> and 'Node :> IAbstractInputNode<'State, 'Edge, 'Node>> = 
    {
        //id: int
    
        length: int
        top: GSSNode<'State, 'Edge, 'Node>
        //state: 'State
        //position: 'Node
        
        (*
        parents: ResizeArray<ContextInheritanceInfo<'State, 'Edge, 'Node>>
        children: ResizeArray<ContextInheritanceInfo<'State, 'Edge, 'Node>>
        
        mutable pairedLeft: Context<'State, 'Edge, 'Node> option
        mutable pairedRight: Context<'State, 'Edge, 'Node> option
        *)
        
        //mutable popHistory: (ContextActionType * 'State * 'Edge) option //new state and edge that has been passed
        
        //mutable survived: bool
        //mutable finished: bool
    }

type Simulation<'State, 'Edge, 'Node when 'State :> PDAState and 'Edge :> IAbstractInputEdge<'State, 'Edge, 'Node> and 'Node :> IAbstractInputNode<'State, 'Edge, 'Node>>(pda: IPDA<'State, 'Edge, 'Node>) = 
    let contexts = Stack<('State * 'Node * bool * Context<'State, 'Edge, 'Node>)>()
    let loaded = Stack<int * ('State * 'Node * bool * Context<'State, 'Edge, 'Node>)>()
   
    let mutable processedContexts = 0
    let mutable currentStart = 0
    let mutable currentStartPosition: 'Node option = None
    
    let mutable contextsCounter = 0
    let newContextId() = 
        let id = contextsCounter
        contextsCounter <- contextsCounter + 1
        id
    
    let finals = new SortedDictionary<int, HashSet<Context<'State, 'Edge, 'Node>>>()
    //let globalFinals = new HashSet<Context<'State, 'Edge, 'Node>>()
    
    let inheritance way target = 
        {way = way; target = target}
    
    member this.Load (uid: int) (start: 'Node) = 
        let full_state = (Helper.pack pda.StartState.Id pda.InitialStackSymbol)
        let exists, context = start.AlreadyVisitedBy full_state
        if not exists then
            let newContext = 
                {
                    top = new GSSNode<_,_,_>(pda.InitialStackSymbol)
                    //state = pda.StartState
                    (*
                    parents = new ResizeArray<_>()
                    children = new ResizeArray<_>()
                    popHistory = None
                    survived = false
                    pairedLeft = None
                    pairedRight = None
                    *)
                    //finished = false
                    length = 0
                }
                
            //newContext.top.SetInitiator (Some newContext)
            loaded.Push (uid, (pda.StartState, start, false, newContext))
            start.Visit full_state newContext
            newContext
        else
            context
    
    member private this.InheritContext parent child edge =
        (*
        parent.children.Add (inheritance edge child)
        child.parents.Add (inheritance edge parent)
        
        if child.survived then
            this.MakeAlive parent
            *)
            
        ()
            
    member private this.NewContext top state (position: 'Node) fullState (parent: Context<'State, 'Edge, 'Node>) (edge: 'Edge) = 
        let newContext = 
            {
                top = top
                //state = state
                (*
                parents = new ResizeArray<_>()
                children = new ResizeArray<_>()
                popHistory = None
                survived = false
                pairedLeft = None
                pairedRight = None
                *)
                //finished = false
                length = parent.length + 1
            }
        
        //top.SetInitiator (Some newContext)
        this.InheritContext parent newContext edge
        contexts.Push (state, position, false, newContext)
        position.Visit fullState newContext
        newContext
    
    (*
    member private this.MakeAlive context =
        if not context.survived then
            let survived = new Stack<Context<'State, 'Edge, 'Node>>()
            survived.Push context
            
            while survived.Count > 0 do
                let top = survived.Pop()
                
                if not top.survived then
                    top.survived <- true
                    
                    for inheritance in top.parents do
                        if not inheritance.target.survived then
                            survived.Push inheritance.target
                            //printf "%s " (inheritance.way.ToString())
                            (*
                        else
                            printfn ""
                    
                    if top.parents.Count = 0 then
                        printfn ""
                        *)
    *)
    
    member private this.ProcessFinal context position = 
        //context.finished <- true
        //this.MakeAlive context
        finals.[currentStart].Add context |> ignore
        pda.Finished context
        //printfn "%s -> %s (%i)" (currentStartPosition.ToString()) (position.ToString()) context.length
    
    member private this.ProcessPush (context: Context<'State, 'Edge, 'Node>) (newState: 'State) (data: stack_data) (edge: 'Edge) =
        let newPosition = edge.Target
        let full_state = Helper.pack newState.Id data
        let exists, previous = newPosition.AlreadyVisitedBy full_state
        
        if exists then
            this.InheritContext context previous edge
            previous.top.AddParent context.top
            
            for popHistory in previous.top.Poppers do
                let (popper, contextAction, historyState, historyEdge) = popHistory
                if contextAction <> Finish then
                    this.ProcessPop popper contextAction historyState historyEdge true |> ignore
            
            previous.top.AcceptNewParents()
            
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
    
    member private this.ProcessPop (context: Context<'State, 'Edge, 'Node>) (contextAction: ContextActionType) (newState: 'State) (edge: 'Edge) (repop: bool) =
        let newPosition = edge.Target
        
        if not repop then
            context.top.AddPopper (context, contextAction, newState, edge)
            
        context.top.Pop repop
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
            if transition.contextAction = Finish then
                this.ProcessFinal context edge.Target
            else
                match transition.stackAction with
                | Push data -> 
                    this.ProcessPush context transition.target data edge |> ignore
                | Skip ->
                    this.ProcessSkip context transition.target edge |> ignore
                | Pop -> 
                    this.ProcessPop context transition.contextAction transition.target edge false |> ignore
    
    member private this.Step() = 
        let (state, position, finished, currentContext) = contexts.Pop()
        
        if (not finished) then
            let outgoingEdges = position.OutgoingEdges
            let first = null
            
            let state = state
            let gssTop = currentContext.top
            let stackSymbol = gssTop.Data
            
            for edge in outgoingEdges do
                let transition = pda.Step state stackSymbol edge
                this.ProcessTransition currentContext transition edge
    
    member this.GetFinals id =
        finals.TryGetValue id |> fun (exists, finals) -> if exists then finals else new HashSet<_>()

    member this.Run() =
        while loaded.Count > 0 do
            let (uid, start) = loaded.Pop()
            let (_, position, _, _) = start
            
            currentStartPosition <- Some position
            currentStart <- uid
            contexts.Push start
            
            finals.[uid] <- new HashSet<Context<'State, 'Edge, 'Node>>()
            
            printfn "%i" uid
            
            while contexts.Count > 0 do
                this.Step()
