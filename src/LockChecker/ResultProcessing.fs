namespace LockChecker

open Yard.Generators.Common.ASTGLLFSA
open AbstractAnalysis.Common
open System.Collections.Generic

module ResultProcessing =
    open System
    open System.IO
    open Yard.Generators.Common.AstNode

    let extractNonCyclicPaths (root: INode) (intToString: Dictionary<int, string>) : HashSet<string> =
        let visited = new HashSet<INode>()
        let pathsCache = new Dictionary<INode, HashSet<string>>();
        
        let rec extractNonCyclicPathsInternal (node: INode): HashSet<string> option =
            if visited.Contains node then
                None
            else
                if (pathsCache.ContainsKey node) then 
                    Some pathsCache.[node]
                else
                    let results = match node with
                        | :? EpsilonNode -> Some (HashSet<string>())
                        | :? TerminalNode as terminal -> 
                            if (terminal.Name = -1<token>) then
                                Some (HashSet<string>())
                            else 
                                let result = new HashSet<string>([intToString.[int terminal.Name]])
                                pathsCache.Add (node, result)
                                Some result
                        | :? PackedNode as packed -> 
                            let left = extractNonCyclicPathsInternal packed.Left
                            let right = extractNonCyclicPathsInternal packed.Right
                            
                            if left.IsSome && right.IsSome then
                                if   left.Value.Count = 0  then right
                                elif right.Value.Count = 0 then left
                                else
                                    let result = new HashSet<string>()
                                    for leftPart in left.Value do
                                        for rightPart in right.Value do
                                            result.Add (leftPart + " " + rightPart) |> ignore
                                    Some result
                            else
                                None
                        | :? IntermediateNode | :? NonTerminalNode ->
                            let mutable isS1 = false
                            
                            let mapOverChildren = 
                                match node with
                                | :? IntermediateNode as intermediate ->
                                    intermediate.MapChildren
                                | :? NonTerminalNode as nonterminal ->
                                    if intToString.[int nonterminal.Name] = "s1" then
                                        isS1 <- true
                                    nonterminal.MapChildren
                            
                            if not isS1 then
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
                        | _ -> failwith "a"
                        
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
        path.Split ' '
        |> Array.takeWhile (fun entity -> not (entity.StartsWith "RT"))
        |> Array.map decoder
        |> String.concat "\n"
        
