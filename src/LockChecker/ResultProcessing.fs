namespace LockChecker

open Yard.Generators.Common.ASTGLLFSA
open AbstractAnalysis.Common
open System.Collections.Generic

module ResultProcessing =
    open System
    open System.IO
    open Yard.Generators.Common.AstNode

    let decoder = new Dictionary<string, string>()

    let extractNonCyclicPaths (root: INode) (intToString: Dictionary<int, string>) : HashSet<string> =
        let visited = new HashSet<INode>()
        let pathsCache = new Dictionary<INode, HashSet<string>>();
        
        let rec extractNonCyclicPathsInternal (node: INode) =
            if visited.Contains node then
                new HashSet<string>(["cycle"])
            else
                if (pathsCache.ContainsKey node) then 
                    pathsCache.[node]
                else
                    let results = match node with
                        | :? EpsilonNode -> new HashSet<string>()
                        | :? TerminalNode as terminal -> 
                            if (terminal.Name = -1<token>) then
                                new HashSet<string>()
                            else 
                                let result = new HashSet<string>([intToString.[int terminal.Name]])
                                pathsCache.Add (node, result)
                                result
                        | :? PackedNode as packed -> 
                            let left = extractNonCyclicPathsInternal packed.Left
                            let right = extractNonCyclicPathsInternal packed.Right
                            
                            if left <> null && right <> null then
                                if   left.Count = 0  then right
                                elif right.Count = 0 then left
                                else
                                    let result = new HashSet<string>()
                                    for leftPart in left do
                                        for rightPart in right do
                                            result.Add (leftPart + " " + rightPart) |> ignore
                                    result
                            else
                                null
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
                                    mapOverChildren (
                                        fun child ->
                                            extractNonCyclicPathsInternal child
                                            |> Seq.filter (fun str -> not (str.Contains "cycle"))
                                    )
                                
                                for pathSet in pathSets do
                                    result.UnionWith pathSet
                                
                                pathsCache.Add(node, result)
                                
                                visited.Remove node |> ignore
                                
                                result
                            else 
                                new HashSet<_>()
                        | _ -> failwith "a"
                        
                    if results.Count > 10 then
                        new HashSet<string>(Seq.take 10 results)
                    else
                        results
                        
        let extractionResults = extractNonCyclicPathsInternal root
        if extractionResults = null then 
            new HashSet<string>()
        else 
            extractionResults