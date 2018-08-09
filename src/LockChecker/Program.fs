module Lockchecker.Main

open Argu
open Yard.Generators.GLL
open AbstractAnalysis.Common
open AbstractParser
open System.Collections.Generic
open Yard.Generators.Common.ASTGLLFSA
open Yard.Generators.GLL.ParserCommon

open InputLoading
open LockChecker
open LockChecker
open LockChecker.Graph
open System.IO
open System

let printAllPaths (roots: INode []) (parserSource: ParserSourceGLL) (outputStream: TextWriter) = 
    if roots.Length < 1
    then 
        printfn "doesn't parsed"
        outputStream.WriteLine ""
    else
        let result = 
            let res = new HashSet<_>()
            roots
            |> Array.map (fun x -> ResultProcessing.extractNonCyclicPaths x parserSource.IntToString)
            |> Array.iter (fun s -> res.UnionWith s)
            res

        result |> Seq.iter (outputStream.WriteLine)
 
type optionsSet = {
    graphFile: string;
    verbose: bool;
    printStages: bool;
    useStdin: bool;
    useStdout: bool;
    pathsOutput: string;
    drawGraph: bool;
    graphOutput: string;
    asService: bool;
    port: int}
    
let startAsConsoleApplication options = 
    let inputStream = new StreamReader (options.graphFile) :> TextReader

    let parserSource, inputGraph, components = loadInput inputStream

    (*if options.drawGraph then
        printGraph inputGraph options.graphOutput*)

    let start = System.DateTime.Now
    Logging.stage "Parsing"

    let roots = Parsing.parseGraph parserSource inputGraph components

    Logging.log (sprintf "Parsing time: %A" (System.DateTime.Now - start))

    let start = System.DateTime.Now
    Logging.stage "Processing"

    let outputStream =
        if options.useStdout then
            Console.Out
        else
            new StreamWriter (options.pathsOutput) :> TextWriter

    printAllPaths roots parserSource outputStream
    outputStream.Close()

    Logging.log (sprintf "Processing time: %A" (System.DateTime.Now - start))
    
type CLIArguments =
    | [<Unique; AltCommandLine("-v")>] Verbose 
    | Output_Path of path: string
    | Draw_Graph of path: string
    | Print_Stages
    | As_Service
    | Port of int
    | [<MainCommand; Last>] Graph_File of path:string
with
    interface IArgParserTemplate with   
        member s.Usage =
            match s with
            | Verbose -> "Print additional information, especially time measurements"
            | Output_Path path -> "Specify path to file where results should be stored"
            | Draw_Graph path -> "Print source graph in the .dot format"
            | Print_Stages -> "Print stage name when each of them starts"
            | Graph_File path -> "Path to graph that should be parsed"
            | As_Service -> "Run Lock Checker as service that can be accessed through socket"
            | Port _ -> "Set port where the service will be located"

open System.Net
open System.Threading

[<EntryPoint>]
let main argv =
    let parser = ArgumentParser.Create<CLIArguments>(programName = "LockChecker")

    try
        let results = parser.Parse argv

        let options = 
            {
                verbose = results.Contains Verbose
                useStdin = not (results.Contains Graph_File)
                useStdout = not (results.Contains Output_Path)
                printStages = results.Contains Print_Stages
                drawGraph = results.Contains Draw_Graph
                graphFile = results.GetResult (Graph_File, defaultValue = "")
                pathsOutput = results.GetResult (Output_Path, defaultValue = "")
                graphOutput = results.GetResult (Draw_Graph, defaultValue = "")
                asService = results.Contains As_Service
                port = results.GetResult (Port, defaultValue = 8888)
            }
        
        if options.asService then
            let serviceHost = new ServiceHost((fun () -> new QuickControlflowGraph() :> IControlFlowGraph), options.port)
            serviceHost.Start()
        else 
            startAsConsoleApplication options
    with e ->
        printfn "%s" e.Message
        raise e
        
    0