namespace LockChecker

open Yard.Generators.Common.ASTGLLFSA
open AbstractAnalysis.Common
open System.Collections.Generic

module ResultProcessing =
    let decoder = new Dictionary<string, string>()
    
    let singlePathForRoot (root: INode) (intToString : Dictionary<_,_>) : seq<string> =
        let results = new Dictionary<INode, _>() 
        let rec getPath : INode -> seq<string> = function
            | :? IntermidiateNode as i ->
                let isGot,value = results.TryGetValue i
                if isGot
                then 
                    Seq.empty
                else
                    results.Add(i, null)
                    getPath i.First
            | :? TerminalNode as t ->
                let res = new List<string>()
                if t.Name <> -1<token> 
                then
                    seq{yield (sprintf "%s %i %i" intToString.[int t.Name] (getLeftExtension t.Extension) (getRightExtension t.Extension))}
                else
                    Seq.empty
            | :? PackedNode as p ->
                let rightPath = getPath p.Right
                let leftPath = getPath p.Left
                Seq.append leftPath rightPath
            | :? NonTerminalNode as n ->
                let isGot,value = results.TryGetValue n
                if isGot
                then 
                    Seq.empty
                else
                    results.Add(n, null)
                    getPath n.First
            | :? EpsilonNode as eps ->
                Seq.empty
            | _ -> failwith "Unexpected node type. rly?"
    
        getPath root
    
    let allPathsForRoot (root: INode) (intToString : Dictionary<_,_>) =
        let results = new Dictionary<INode, _>() 
        let rec getPath (node : INode) : HashSet<_> =
            match node with
            | :? IntermidiateNode | :? NonTerminalNode ->
                let isGot,value = results.TryGetValue node
                let name, strName = 
                    match node with 
                    | :? IntermidiateNode as i -> string i.Extension + "_" + string i.Nonterm, intToString.[int i.Nonterm]
                    | :? NonTerminalNode as n -> string n.Extension + "_" + string n.Name,  intToString.[int n.Name]
                    | _ -> failwith "wrong node type"
                if strName = "s1" //|| strName = "s0"
                then new HashSet<_>()
                elif isGot
                then if value = null then new HashSet<_>([|name|]) else value
                else
                    results.Add(node, null)
                    let first, others = 
                        match node with 
                        | :? IntermidiateNode as i -> i.First, i.Others
                        | :? NonTerminalNode as n -> n.First, n.Others
                        | _ -> failwith "wrong node type"
                    let first = getPath first
                    
                    let res = new HashSet<_>(first)
                    (*if others <> null 
                    then others |> Microsoft.FSharp.Collections.ResizeArray.iter (fun elt -> res.UnionWith (getPath elt))
                    *)
                    let withPH, complete = 
                        Array.ofSeq res
                        |> Array.partition (fun a -> a.Contains name)
                    res.Clear()
                    res.UnionWith complete
                    for c in complete do for s in withPH do res.Add(s.Replace(name, c)) |> ignore
                    results.[node] <- res
                    res
           
            | :? PackedNode as p ->
                let rightPath = getPath p.Right
                let leftPath = getPath p.Left
                if leftPath.Count = 0
                then rightPath
                elif rightPath.Count = 0 
                then leftPath
                else new HashSet<_>([|for l in leftPath do yield! [|for r in rightPath -> l + " " + r|]|])
            
            | :? TerminalNode as t ->
                if t.Name <> -1<token> 
                then new HashSet<_> ([|intToString.[int t.Name]|])
                else new HashSet<_>()
    
            | :? EpsilonNode as eps -> new HashSet<_>()
    
            | _ -> failwith "Unexpected node type. rly?"
    
        getPath root
