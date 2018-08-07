module InputLoading
open Yard.Generators.GLL
open Yard.Generators.GLL.ParserCommon
open AbstractAnalysis.Common
open System.Collections.Generic

open LockChecker
open LockChecker
open Yard.Generators.Common.AutomataCombinators
open Yard.Generators.Common.FSA.Common
open System.IO

(*
ba: ASSERT
ca: ASSERT

s0: C s0 RT s0 | G s0 RL s0 | ca s0 | ca | eps

s1: C s1 RT s1 | G s0 RL s1 | eps

[<Start>]
s: ba s | s ba| s1 s | s s1 | ba | C s RT s1 | C s RT s 
*)

let parseGraphFile (graphStream: TextReader) = 
    let data =    Seq.initInfinite (fun _ -> graphStream.ReadLine()) 
               |> Seq.takeWhile ((<>) null)
               |> Seq.toArray
    
    let data = if data.[data.Length-1].Length < 1 then data.[..data.Length-2] else data
    
    let infoLine = data.[data.Length-2]
    let startVLine = data.[data.Length-1] 
    
    let edgesLines = data.[..data.Length-3]

    let info = infoLine.Split ' '

    let calls = info.[1].Trim() |> int |> fun n -> if (n < 2) then 2 else n
    let locks = info.[2].Trim() |> int |> fun n -> if (n < 2) then 2 else n  
    let asserts = info.[3].Trim() |> int |> fun n -> if (n < 2) then 2 else n

    let parserSource = Parsing.generateParser calls locks asserts
    let stringToToken = parserSource.StringToToken

    let time = System.DateTime.UtcNow
    Logging.stage "Graph loading"

    let tryParseInt str =
        try int str
        with e -> 0

    let startVerts = 
        if startVLine.Length = 0 then
            [||]
        else
            startVLine.Split ' ' |> Array.map tryParseInt 

    let edges = 
        edgesLines |> Array.map (fun s -> s.Split ' ' |> fun a -> new ParserEdge<_>(int a.[0], int a.[2], stringToToken a.[1]))

    Logging.log (sprintf "Graph loading time is %A" (System.DateTime.UtcNow - time))
    
    parserSource, edges, startVerts

let loadInput (graphStream: TextReader) =
    let parserSource, edges, startVerts = parseGraphFile graphStream
    
    let r = new HashSet<_>()
    let ev = edges |> Array.iter (fun e ->
        r.Add e.Source |> ignore
        r.Add e.Target |> ignore)

    Logging.log (sprintf "Starts: %A" startVerts.Length)

    let inputGraph = new TokenLabeledInputGraph(startVerts |> Array.filter (fun x -> r.Contains x), [||])
    inputGraph.AddVerticesAndEdgeRange edges |> ignore

    parserSource, inputGraph