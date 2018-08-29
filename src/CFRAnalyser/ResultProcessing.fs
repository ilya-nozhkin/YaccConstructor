namespace CfrAnalyser 

open Yard.Generators.Common.ASTGLLFSA
open AbstractAnalysis.Common
open System.Collections.Generic
open PDASimulator
open CfrAnalyser.PDA

module ResultProcessing =
    open System.ComponentModel

    open System.Runtime.InteropServices

    open System
    open System.IO
    open Yard.Generators.Common.AstNode
    // extracts all non cyclic paths for start nonterminal, for another thakes only first child
    let extractNonCyclicPath (root: INode) (intToString: Dictionary<int, string>) (interruptCheck : unit -> unit): HashSet<string> =
        let visited = new HashSet<INode>()
        let pathsCache = new Dictionary<INode, HashSet<string>>();
        
        let rec extractNonCyclicPathsInternal (node: INode) : HashSet<string> option =
            interruptCheck()
            if visited.Contains node then None else
            if (pathsCache.ContainsKey node) then pathsCache.[node] |> Some else
            let results = 
                match node with
                | :? EpsilonNode -> HashSet<string>() |> Some
                | :? TerminalNode as terminal -> 
                    if (terminal.Name = -1<token>)
                    then
                        Some (HashSet<string>())
                    else 
                        let result = new HashSet<string>([intToString.[int terminal.Name]])
                        pathsCache.Add (node, result)
                        Some result
                | :? PackedNode as packed -> 
                    let left = extractNonCyclicPathsInternal packed.Left 
                    let right = extractNonCyclicPathsInternal packed.Right
                    
                    if left.IsSome && right.IsSome
                    then
                        if left.Value.Count = 0 
                        then right
                        elif right.Value.Count = 0
                        then left
                        else
                            let result = new HashSet<string>()
                            for leftPart in left.Value do
                                for rightPart in right.Value do
                                    result.Add (leftPart + " " + rightPart) |> ignore
                            Some result
                    else
                        None
                | :? IntermediateNode | :? NonTerminalNode ->
                    let mutable skip = false
                    
                    let mapOverChildren = 
                        match node with
                        | :? IntermediateNode as intermediate ->
                            intermediate.MapFirstChild
                            //intermediate.MapChildren
                        | :? NonTerminalNode as nonterminal ->
                            if intToString.[int nonterminal.Name].[0] = '#'
                            then
                                skip <- true
                            if intToString.[int nonterminal.Name].[0] = '!'
                            then
                                nonterminal.MapChildren
                            else
                                //nonterminal.MapChildren
                                nonterminal.MapFirstChild
                        | _ -> failwith "unexpected SPPF node type"
                    
                    if not skip then
                        visited.Add node |> ignore

                        let result = new HashSet<string>()
                        let pathSets = 
                            mapOverChildren (fun child -> extractNonCyclicPathsInternal child)
                            |> Seq.filter Option.isSome
                            |> Seq.map Option.get
                        
                        for pathSet in pathSets do
                            result.UnionWith pathSet
                        
                        pathsCache.Add(node, result)
                        
                        visited.Remove node |> ignore
                        
                        let result = 
                            if result.Count > 5 then
                                HashSet<string>(Seq.take 5 result)
                            else
                                result
                            
                        Some result
                    else 
                        Some (HashSet<string>())
                | _ -> failwith "unexpected SPPF node type"
                
            results
                        
        let extractionResults = extractNonCyclicPathsInternal root
        printfn "%s" (if extractionResults.IsSome && extractionResults.Value.Count > 0 then Seq.head extractionResults.Value else "" )
        Option.defaultValue (HashSet<string>()) extractionResults
    
    (*
    type UndoToken = AddCall of int | AddReturn of int | RemoveReturn of int | UnUndoable
    type Validator(pda: IPDA<MyState, MyEdge, MyNode>) = 
        let stack = new Stack<stack_data>()
        let currentState = pda.
        
        let processTransition (transition: PDATransition
        *)
    (* 
    type Validator1() = 
        let calls = SortedSet<int>()
        let returns = SortedSet<int>()

        let firstAcceptance = set ["C"; "RT"; "D"; "RD"]
        let accept (acceptance: Set<string>) = (Seq.takeWhile (fun c -> c >= 'A' && c <= 'Z') >> String.Concat >> (fun prefix -> acceptance.Contains prefix))
        
        let firstCheck = 
            path.Split ' '
            |> Array.filter (accept firstAcceptance)
            |> Array.forall 
                (
                    fun entity -> 
                        if entity.StartsWith "C" then
                            calls.Add (int (entity.Substring(1))) |> ignore
                            true
                        elif entity.StartsWith "D" then
                            calls.Contains (int (entity.Substring(1)))
                        elif entity.StartsWith "RT" then
                            returns.Remove (int (entity.Substring(2))) |> ignore
                            true
                        else //if entity.StartsWith "RD" then
                            returns.Add (int (entity.Substring(2))) |> ignore
                            true
                )
        
        firstCheck && (returns.Count = 0);
        
    type Validator2() = 
        let calls = SortedSet<int>()
        let returns = SortedSet<int>()
        
        member this.AddCall id = 
            calls.Add id |> ignore
            AddCall id
            
        member this.AddReturn id = 
            returns.Add id |> ignore
            AddReturn id
        
        member this.ContainsCall id = 
            calls.Contains id
        
        member this.RemoveReturn id =
            if returns.Remove id then
                RemoveReturn id
            else
                UnUndoable
            
        member this.Eat (entity: string) = 
            if entity.StartsWith "C" then
                let id = int (entity.Substring 1)
                (true, this.AddCall id)
            elif entity.StartsWith "D" then
                let id = int (entity.Substring 1)
                (this.ContainsCall id, UnUndoable)
            elif entity.StartsWith "RT" then
                let id = int (entity.Substring 1)
                (true, this.RemoveReturn id)
            elif entity.StartsWith "RD" then
                let id = int (entity.Substring 1)
                (true, this.AddReturn id)
            else
                (true, UnUndoable)
        
        member this.Undo (token: UndoToken) = 
            match token with
            | AddCall id -> calls.Remove id |> ignore
            | AddReturn id -> returns.Remove id |> ignore
            | RemoveReturn id -> returns.Add id |> ignore
            | UnUndoable -> ()
     *)
    
    let extractAllValidPaths (onFound: string -> unit) (finals: HashSet<Context<MyState, MyEdge, MyNode>>) (rootContext: Context<MyState, MyEdge, MyNode>) = 
        (*
        let pathsRoot = List.empty
        let visited = new HashSet<Context<MyState, MyEdge, MyNode>>()
        let pda = new MyPDA()
        
        printfn "%i" rootContext.owner
        
        //printfn "%s" (List.rev listPointer |> String.concat " ")
        
        let rec internalExtract (context: Context<MyState, MyEdge, MyNode>) listPointer = 
            if not (visited.Contains context) then
                visited.Add context |> ignore
                let mutable survived = true
                
                //printfn "%s" (List.rev listPointer |> String.concat " ")
        
                for inheritance in context.children do
                    if inheritance.target.survived && inheritance.target.owner >= context.owner then
                        let label = inheritance.way.Label
                        //let success, token = validator.Eat label
                        
                        if true then//visited.Count < 1000 then//success then
                            internalExtract inheritance.target (label :: listPointer)
                            if inheritance.target.survived then
                                survived <- true
                
                        //validator.Undo token
                        
                if finals.Contains context then
                    let result = listPointer |> List.toArray |> Array.rev
                    onFound (String.concat " " result)
                    raise (Exception(""))
                    survived <- true
                
                context.survived <- survived
            
                visited.Remove context |> ignore
        
        *)
        try
            ()//internalExtract rootContext pathsRoot
        with e -> ()
            
    let decode (path: string) (decoder: string -> string) =
        let firstAcceptance = set ["CP"; "C"; "RT"; "D"; "RD"; "AR"; "AW"]
        let secondAcceptance = set ["RT"; "RD"; "AR"; "AW"]
        let transformation = dict [("RT", "C"); ("RD", "D"); ("AR", "AR"); ("AW", "AW")]
        (*
        let secondAcceptance = set ["C"; "CP"; "D"; "AR"; "AW"]
        let transformation = dict [("C", "C"); ("CP", "CP"); ("D", "D"); ("AR", "AR"); ("AW", "AW")]
        *)
        
        let delegates = new SortedSet<int>()
        
        let accept (acceptance: Set<string>) = (Seq.takeWhile (fun c -> c >= 'A' && c <= 'Z') >> String.Concat >> (fun prefix -> acceptance.Contains prefix))
        let entities = path.Split ' ' |> Array.filter (accept firstAcceptance)
        let first = entities.[0]
        entities
        |> Array.filter (accept secondAcceptance)
        |> Array.map 
            (
                fun entity -> 
                    let prefix = entity |> Seq.takeWhile (fun c -> c >= 'A' && c <= 'Z') |> String.Concat
                    let index = entity.Substring (prefix.Length)
                    
                    if prefix = "RD" then
                        delegates.Add (int index) |> ignore
                    
                    if prefix = "RT" && delegates.Contains (int index) then
                        "CP" + index
                    else
                        transformation.[prefix] + index
            )
        |> Array.map (fun entity -> (entity = first, entity))
        |> Array.map (fun (isFirst, entity) -> (if isFirst then "*" else "") + (decoder entity))
        |> Array.rev
        |> String.concat "\n"
        
