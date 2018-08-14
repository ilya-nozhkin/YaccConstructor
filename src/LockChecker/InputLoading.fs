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
open System.Linq.Expressions
open System.Linq.Expressions
open QuickGraph

(*
ba: ASSERT
ca: ASSERT

s0: C s0 RT s0 | G s0 RL s0 | ca s0 | ca | eps

s1: C s1 RT s1 | G s0 RL s1 | eps

[<Start>]
s: ba | ba s | s ba | s1 s | s s1 | C s RT s1 | C s RT s 
*)

(*
ba: ASSERT
ca: ASSERT

s0: H s0 | G s0 RL s0 | ca | ca s0 | eps

s1: H s1 | G s0 RL s1 | eps

[<Start>]
s: ba | ba s | s ba | s1 s | s s1 | C s RT | C s RT s 
*)

(*
s0: C RT | C s0 RT | C s0 RT s0 | C RT s0 | ca | ca s0

s: ba | ba s | s ba | C s RT | C s RT s | s s1 | s1 s
*)

let readStartComponents (lines: string []) =
    let count = int lines.[lines.Length - 1]
    let componentsInfo = lines.[lines.Length - 1 - count .. lines.Length - 2]
    let components = 
        componentsInfo 
        |> Array.map 
            (
                fun line -> 
                    line.Split ' ' 
                    |> Array.filter (String.length >> ((<) 0))
                    |> Array.map int
            )
    
    components, lines.[..lines.Length - 2 - count]

let parseGraphFile (graphStream: TextReader) = 
    let data =    Seq.initInfinite (fun _ -> graphStream.ReadLine()) 
               |> Seq.takeWhile ((<>) null)
               |> Seq.toArray
    
    let data = if data.[data.Length-1].Length < 1 then data.[..data.Length-2] else data
    
    let components, data = readStartComponents data
    
    let infoLine = data.[data.Length-1]
    let edgesLines = data.[..data.Length-2]

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

    let edges = 
        edgesLines |> Array.map (fun s -> s.Split ' ' |> 
            fun a -> 
                let label = a.[1]
                let token =
                    if label = "e" then
                        -1<token>
                    else
                        stringToToken label
                    
                new ParserEdge<_>(int a.[0], int a.[2], token))
    
    Logging.log (sprintf "Graph loading time is %A" (System.DateTime.UtcNow - time))
    
    parserSource, edges, components
    

let loadInput (graphStream: TextReader) =
    let parserSource, edges, components = parseGraphFile graphStream
    
    let r = new HashSet<_>()
    let ev = edges |> Array.iter (fun e ->
        r.Add e.Source |> ignore
        r.Add e.Target |> ignore)

    let inputGraph = new TokenLabeledInputGraph([||], [||])
    inputGraph.AddVerticesAndEdgeRange edges |> ignore
    
    let filteredComponents = 
        components
        |> Array.map (Array.filter inputGraph.ContainsVertex)

    parserSource, inputGraph, filteredComponents