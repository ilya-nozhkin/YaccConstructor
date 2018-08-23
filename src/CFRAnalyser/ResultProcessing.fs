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
                        | :? NonTerminalNode as nonterminal ->
                            if intToString.[int nonterminal.Name].[0] = '#'
                            then
                                skip <- true
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
                        
                        Some result
                    else 
                        Some (HashSet<string>())
                | _ -> failwith "unexpected SPPF node type"
                
            if results.IsSome then
                if results.Value.Count > 10 then
                    Some (HashSet<string>(Seq.take 10 results.Value))
                else
                    results
            else 
                None
                        
        let extractionResults = extractNonCyclicPathsInternal root
        Option.defaultValue (HashSet<string>()) extractionResults
    
    let decode (path: string) (decoder: string -> string) =
        let entities = path.Split ' ' |> Array.filter (fun entity -> entity.StartsWith "C" || entity.StartsWith "RT" || entity.StartsWith "A")
        let first = entities.[0]
        entities
        |> Array.skipWhile (fun entity -> entity.StartsWith "C")
        |> Array.map (fun entity -> if (entity.StartsWith "RT") then "C" + (entity.Substring 2) else entity)
        |> Array.map (fun entity -> (entity = first, entity))
        |> Array.map (fun (isFirst, entity) -> (if isFirst then "*" else "") + (decoder entity))
        |> Array.rev
        |> String.concat "\n"
        
