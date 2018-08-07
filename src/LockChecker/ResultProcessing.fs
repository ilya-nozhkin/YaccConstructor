namespace LockChecker

open Yard.Generators.Common.ASTGLLFSA
open AbstractAnalysis.Common
open System.Collections.Generic

module ResultProcessing =
    open System
    open System.IO
    open Yard.Generators.Common.AstNode

    let decoder = new Dictionary<string, string>()

    let internal visited = new HashSet<INode>()
    let internal pathsCache = new Dictionary<INode, HashSet<string>>();

    let rec extractNonCyclicPaths (root: INode) (intToString: Dictionary<int, string>) : HashSet<string> =
        if root = null || visited.Contains root then
            new HashSet<string>()
        else
            if (pathsCache.ContainsKey root) then 
                pathsCache.[root]
            else
                visited.Add root |> ignore

                let results = match root with
                    | :? EpsilonNode -> new HashSet<string>()
                    | :? TerminalNode as terminal -> 
                        if terminal.Name <> -1<token> then
                            let result = new HashSet<string>([intToString.[int terminal.Name]])
                            pathsCache.Add (root, result)
                            result
                        else 
                            new HashSet<_>()
                    | :? PackedNode as packed -> 
                        let left = extractNonCyclicPaths packed.Left intToString
                        let right = extractNonCyclicPaths packed.Right intToString

                        if   left.Count = 0  then right
                        elif right.Count = 0 then left
                        else
                            let result = new HashSet<string>()
                            for leftPart in left do
                                for rightPart in right do
                                    result.Add (leftPart + " " + rightPart) |> ignore
                            result
                    | :? IntermediateNode | :? NonTerminalNode ->
                        let mutable isS1 = false
                        
                        let mapOverChildren = 
                            match root with
                            | :? IntermediateNode as intermediate ->
                                intermediate.MapChildren
                            | :? NonTerminalNode as nonterminal ->
                                if intToString.[int nonterminal.Name] = "s1" then
                                    isS1 <- true
                                nonterminal.MapChildren
                        
                        if not isS1 then
                            let result = new HashSet<string>()
                            let pathSets = mapOverChildren (fun child -> extractNonCyclicPaths child intToString)
                            for pathSet in pathSets do
                                result.UnionWith pathSet
                                
                            pathsCache.Add(root, result)
                            result
                        else 
                            new HashSet<_>()
                    | _ -> failwith ""
                    
                visited.Remove root |> ignore
                
                if results.Count > 100 then
                    new HashSet<string>(Seq.take 100 results)
                else
                    results
