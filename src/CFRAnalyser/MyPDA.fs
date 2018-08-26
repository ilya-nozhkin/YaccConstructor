namespace CfrAnalyser.PDA

open PDASimulator
open System.Collections.Generic
open System

type MyEdgeLabel = Call of int | Return of int | ReadAssert of int | WriteAssert of int | GetLock of int | ReleaseLock of int | Delegate of int | DelegateReturn of int | Invocation | Epsilon | End

[<AllowNullLiteral>]
type MyState(id, stepper: MyEdge -> stack_data -> PDATransition<MyState>) =
    inherit PDAState(id)
    
    member this.Step edge stackTop = 
        stepper edge stackTop
        
and MyNode(id: int, getOutgoingEdges: int -> MyEdge seq) =
    let visitors = SortedDictionary<full_state, Context<_, _, _>>()
    
    member this.Id = id
    
    override this.Equals obj = 
        (obj :?> MyNode).Id = id
        
    override this.GetHashCode() = 
        id
        
    interface IComparable with
        member this.CompareTo obj =
            let leftId = id
            let rightId = (obj :?> MyNode).Id
            
            if leftId < rightId then -1 else (if leftId > rightId then 1 else 0)
    
    interface IAbstractInputNode<MyState, MyEdge, MyNode> with
        member this.Visit (state: full_state) (context) =
            visitors.Add (state, context)
        
        member this.AlreadyVisitedBy(state: full_state) = 
            visitors.TryGetValue state
        
        member this.OutgoingEdges = 
            getOutgoingEdges id
            
and MyEdge(label: string, target: MyNode) = 
    let tokenizedLabel =
        let prefix = label |> Seq.takeWhile (fun c -> c >= 'A' && c <= 'Z') |> String.Concat
        match prefix with
        | "C" -> Call (int (label.Substring(1)))
        | "D" -> Delegate (int (label.Substring(1)))
        | "RT" -> Return (int (label.Substring(2)))
        | "RD" -> DelegateReturn (int (label.Substring(2)))
        | "G" -> GetLock (int (label.Substring(1)))
        | "RL" -> ReleaseLock (int (label.Substring(2)))
        | "AR" -> ReadAssert (int (label.Substring(2)))
        | "AW" -> WriteAssert (int (label.Substring(2)))
        | "I" -> Invocation
        | "" -> Epsilon
        | "END" -> End
        | _ -> failwith "unexpected token"
    
    member this.Tokenized = tokenizedLabel
    
    member this.Label = label 
        
    interface IAbstractInputEdge<MyState, MyEdge, MyNode> with
        member this.Target = target

type MyGraph(dynamicEdgesIndex: (string * int) [] []) =
    let mutable (myEdges: MyEdge [] []) = null
    
    let getOutgoingEdges id = seq myEdges.[id]
    
    let nodes = 
        let nodes = Array.zeroCreate dynamicEdgesIndex.Length
        myEdges <- Array.zeroCreate dynamicEdgesIndex.Length
        
        for i in [0 .. nodes.Length - 1] do
            nodes.[i] <- MyNode(i, getOutgoingEdges)
            
        for i in [0 .. nodes.Length - 1] do
            if dynamicEdgesIndex.[i] <> null then
                myEdges.[i] <- dynamicEdgesIndex.[i] |> Array.map (fun (label, target) -> new MyEdge(label, nodes.[target]))
        
        nodes
    
    member this.GetNode id = 
        nodes.[id]

type MyPDA() = 
    let invalidState = null
    let drop = {stackAction = Skip; contextAction = Drop; target = invalidState}
    
    let locks = 1000000000;
    let delegates = 500000000;
    let calls = 100
    
    let transition stackAction contextAction target =
        {stackAction = stackAction; contextAction = contextAction; target = target}
    
    let conditional condition stackAction contextAction target = 
        if condition then
            transition Pop Continue target
        else
            drop
    
    let push id = Push (uint32 id)
    
    let rec startState = MyState(1u, processStartState)
    
    and afterAssertState = MyState(2u, processAfterAssertState)
    
    and underLockState = MyState(3u, processUnderLockState)
    
    and tailState = MyState(4u, processTailState)
    
    and underLockState2 = MyState(5u, processUnderLockState)
    
    and processStartState (edge: MyEdge) (stackTop: stack_data) =
        match edge.Tokenized with
        | Call id ->       transition (push (calls + id))               Continue startState
        | Delegate id ->   transition (push (delegates + id)) Continue startState
        | GetLock id ->    transition (push (locks + id))     Continue underLockState
        | Invocation ->    transition  Skip                   Continue startState
        | ReadAssert id -> transition  Skip                   Continue afterAssertState
        | Epsilon ->       transition  Skip                   Continue startState
        | _ ->             drop
        
    and processAfterAssertState (edge: MyEdge) (stackTop: stack_data) = 
        if stackTop <> 0u then
            match edge.Tokenized with
            | Return id ->         conditional (uint32 (id + calls) = stackTop)     Pop Continue afterAssertState
            | DelegateReturn id -> conditional (uint32 (id + delegates) = stackTop) Pop Continue afterAssertState
            | ReadAssert id ->  transition Skip Continue afterAssertState
            | GetLock id ->     transition Skip Continue underLockState2
            | Invocation ->     transition Skip Continue afterAssertState
            | Epsilon ->        transition Skip Continue afterAssertState
            | _ ->              drop
        else
            //transition Skip Finish afterAssertState
            processTailState edge stackTop
    
    and processTailState (edge: MyEdge) (stackTop: stack_data) =
        match edge.Tokenized with
        | Return id ->         transition Skip Continue tailState
        | DelegateReturn id -> transition Skip Continue tailState
        | ReadAssert id ->     transition Skip Continue tailState
        | GetLock id ->        transition Skip Continue underLockState2
        | Invocation ->        transition Skip Continue tailState
        | Epsilon ->           transition Skip Continue tailState
        | End ->               transition Skip Finish   tailState
        | _ ->                 drop
            
    and processUnderLockState (edge: MyEdge) (stackTop: stack_data) = 
        if stackTop >= uint32 locks then
            match edge.Tokenized with
            | ReleaseLock id -> conditional (uint32 (locks + id) = stackTop) Pop Continue underLockState
            | GetLock id ->   transition (push (locks + id)) Continue underLockState
            | Invocation ->   transition Skip Continue underLockState
            | ReadAssert _ -> transition Skip Continue underLockState
            | Epsilon ->      transition Skip Continue underLockState
            | _ ->            drop
        else
            processStartState edge stackTop
            
    and processUnderLockState2 (edge: MyEdge) (stackTop: stack_data) = 
        if stackTop >= uint32 locks then
            match edge.Tokenized with
            | ReleaseLock id -> conditional (uint32 (locks + id) = stackTop) Pop Continue underLockState2
            | GetLock id ->   transition (push (locks + id)) Continue underLockState2
            | Invocation ->   transition Skip Continue underLockState2
            | ReadAssert _ -> transition Skip Continue underLockState2
            | Epsilon ->      transition Skip Continue underLockState2
            | _ ->            drop
        else
            processAfterAssertState edge stackTop
    
    let results = Stack<string>()
    
    member this.Results = results
    
    interface IPDA<MyState, MyEdge, MyNode> with
        member this.StartState = startState
        member this.InitialStackSymbol = 0u
        
        member this.Step state stackTop edge =
            state.Step edge stackTop

        member this.Finished context = 
            ()//context.path |> List.rev |> List.map (fun edge -> edge.Label) |> String.concat " " |> results.Push