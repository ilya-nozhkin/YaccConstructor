namespace CfrAnalyser 

open Yard.Generators.Common.ASTGLLFSA
open AbstractAnalysis.Common
open System.Collections.Generic

module ResultProcessing =
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
   
    let validate (path: string) = 
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
    
    let decode (path: string) (decoder: string -> string) =
        let firstAcceptance = set ["C"; "RT"; "D"; "RD"; "AR"; "AW"]
        let secondAcceptance = set ["RT"; "RD"; "AR"; "AW"]
        let transformation = dict [("RT", "C"); ("RD", "D"); ("AR", "AR"); ("AW", "AW")]
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
                    transformation.[prefix] + index
            )
        |> Array.map (fun entity -> (entity = first, entity))
        |> Array.map (fun (isFirst, entity) -> (if isFirst then "*" else "") + (decoder entity))
        |> Array.rev
        |> String.concat "\n"
        
