﻿namespace CfrAnalyser 

open Yard.Generators.Common.ASTGLLFSA
open AbstractAnalysis.Common
open System.Collections.Generic
open PDASimulator
open CfrAnalyser.PDA

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
   
    let validate (path: string []) = 
        let calls = SortedSet<int>()
        let returns = SortedSet<int>()
        
        let acceptance = set ["C"; "RT"; "D"; "RD"]
        let accept (acceptance: Set<string>) = (Seq.takeWhile (fun c -> c >= 'A' && c <= 'Z') >> String.Concat >> (fun prefix -> acceptance.Contains prefix))

        let firstCheck = 
            path
            |> Array.filter (accept acceptance)
            |> Array.forall 
                (
                    fun entity -> 
                        if entity.StartsWith "C" then
                            calls.Add (int (entity.Substring(1))) |> ignore
                            true
                        elif entity.StartsWith "D" then
                            calls.Contains (int (entity.Substring(1)))
                        elif entity.StartsWith "RD" then
                            returns.Add (int (entity.Substring(2))) |> ignore
                            true
                        else
                            returns.Remove (int (entity.Substring(2))) |> ignore
                            true
                )
        
        firstCheck && (returns.Count = 0)
    
    let extractAllValidPaths (onFound: string -> unit) (finals: HashSet<Context<MyState, MyEdge, MyNode>>) (rootContext: Context<MyState, MyEdge, MyNode>) = 
        let pathsRoot = List.empty
        let visited = new HashSet<Context<MyState, MyEdge, MyNode>>()
        
        //printfn "%s" (List.rev listPointer |> String.concat " ")
        
        let rec internalExtract (context: Context<MyState, MyEdge, MyNode>) listPointer = 
            if not (visited.Contains context) then
                visited.Add context |> ignore
                
                printfn "%s" (List.rev listPointer |> String.concat " ")
        
                for inheritance in context.children do
                    if inheritance.Key.survived then
                        internalExtract inheritance.Key (inheritance.Value.Label :: listPointer)
                
                if finals.Contains context then
                    let result = listPointer |> List.toArray |> Array.rev
                    if validate result then
                        onFound (String.concat " " result)
            
                visited.Remove context |> ignore
        
        internalExtract rootContext pathsRoot
            
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
        
