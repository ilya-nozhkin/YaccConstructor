namespace CfrAnalyser 

open AbstractAnalysis.Common
open System
open System.Collections.Generic
open System.Diagnostics

open System.Collections.Generic
open System.Diagnostics
open System.IO
open QuickGraph
open System.Runtime.Serialization
open System.Runtime.CompilerServices
open System.IO
open System.Net
open System.Net.Sockets
open System.Runtime.Serialization.Json
open System.Runtime.Serialization
open System.Collections.Generic
open System.Threading.Tasks

open System.Threading
open CfrAnalyser.Graph

open AbstractAnalysis.Common
open CfrAnalyser.PDA
open PDASimulator
open Yard.Generators.GLL.AbstractParser

[<DataContract>]
type AddMethodMessage =
    {
        [<field: DataMember(Name="method")>]
        method: Method 
        
        [<field: DataMember(Name="edges")>]
        edges: RawEdge []
        
        [<field: DataMember(Name="callInfos")>]
        callInfos: CallInfo []
    }
    static member JsonReader = DataContractJsonSerializer(typeof<AddMethodMessage>)
    static member FromJson (source: Stream) =
        AddMethodMessage.JsonReader.ReadObject(source) :?> AddMethodMessage

[<DataContract>]
type UpdateFileMessage =
    {
        [<field: DataMember(Name="fileName")>]
        fileName: string
        
        [<field: DataMember(Name="methods")>]
        methods: string []
    }
    static member JsonReader = DataContractJsonSerializer(typeof<UpdateFileMessage>)
    static member FromJson (source: Stream) =
        UpdateFileMessage.JsonReader.ReadObject(source) :?> UpdateFileMessage

[<DataContract>]
type RestoreMessage =
    {
        [<field: DataMember(Name="sourcePath")>]
        sourcePath: string
    }
    static member JsonReader = DataContractJsonSerializer(typeof<RestoreMessage>)
    static member FromJson (source: Stream) =
        RestoreMessage.JsonReader.ReadObject(source) :?> RestoreMessage

[<DataContract>]
type RunAnalysisMessage =
    {
        [<field: DataMember(Name="starts")>]
        starts: string []
    }
    static member JsonReader = DataContractJsonSerializer(typeof<RunAnalysisMessage>)
    static member FromJson (source: Stream) =
        RunAnalysisMessage.JsonReader.ReadObject(source) :?> RunAnalysisMessage

[<DataContract>]
type AddSpecificDecoderInfo =
    {
        [<field: DataMember(Name="key")>]
        key: string
        
        [<field: DataMember(Name="value")>]
        value: string
    }   
    static member JsonReader = DataContractJsonSerializer(typeof<AddSpecificDecoderInfo>)
    static member FromJson (source: Stream) =
        AddSpecificDecoderInfo.JsonReader.ReadObject(source) :?> AddSpecificDecoderInfo

type ServiceHost(graphProvider: unit -> ControlFlowGraph, port) =
    let socket = TcpListener.Create (port)
    let mutable client = null
    let mutable isProcess = true
    
    let mutable graph = graphProvider()
    let mutable graphBuilder = new ControlFlowGraphBuilder(graph)
    
    let mutable asyncReadTask = null
    
    let mutable parserIsValid = false
    
    let mutable (parser: GLLParser option) = None
    let mutable (currentInput: ControlFlowInput option) = None
    let mutable endToken = -2<token>
    
    let mutable globalStartTime = System.DateTime.MinValue
    let mutable weakEdgesHandler: IDisposable option = None
    
    let invalidateParser() =
        parserIsValid <- false
        parser <- None
        if weakEdgesHandler.IsSome then
            weakEdgesHandler.Value.Dispose()
            weakEdgesHandler <- None
    
    let prepareForParsing (checkForInterrupt: unit -> unit) =
        checkForInterrupt()

        let startTime = System.DateTime.Now
        weakEdgesHandler <- Some (graph.GenerateWeakEdges())
        Logging.log (sprintf "Weak edges generation time is %A" (System.DateTime.Now - startTime))
        checkForInterrupt()
       
        graph.ConstructDynamicIndex()
        
        let startTime = System.DateTime.Now
        use statesWriter = new StreamWriter(@"C:\hackathon\states.graph")
        graph.DumpStatesLevel statesWriter
        Logging.log (sprintf "States level dumping time is %A" (System.DateTime.Now - startTime))
        checkForInterrupt()
    
        let startTime = System.DateTime.Now
        let statistics = graph.GetStatistics()
        let parserSource = Parsing.generateParser statistics.userStatistics
        Logging.log (sprintf "Parser generation time is %A" (System.DateTime.Now - startTime))
        checkForInterrupt()
            
        let startTime = System.DateTime.Now
        let input = graph.GetParserInput parserSource.StringToToken
        Logging.log (sprintf "Input generation time is %A" (System.DateTime.Now - startTime))
        checkForInterrupt()
        
        globalStartTime <- System.DateTime.Now
        parser <- Some (new GLLParser(parserSource, input, true))
        parserIsValid <- true

        currentInput <- Some input
        endToken <- parserSource.StringToToken "END"
        
    let performParsing (reader: StreamReader) (writer: StreamWriter) (startFiles: string []) =
        let cancellation: CancellationTokenSource ref = ref null
        let cancelled = ref false
        
        let checkForInterrupt = (fun () -> if Volatile.Read(cancelled) then raise (new ThreadInterruptedException()))
        
        let asyncMessage = reader.ReadLineAsync()
        let asyncCanceller = 
            asyncMessage.ContinueWith (
                fun (completed: Task<_>) -> 
                    printfn "received while parsing: %s" completed.Result
                    if completed.Result = "interrupt" then 
                        if Volatile.Read(cancellation) <> null then
                            Volatile.Read(cancellation).Cancel()
                        Volatile.Write(cancelled, true)
            )
        
        asyncReadTask <- asyncCanceller
        
        if asyncCanceller.Status = TaskStatus.Created then
            asyncCanceller.Start()
        
        if not parserIsValid then
            prepareForParsing checkForInterrupt
        
        //let dynamicIndex = prepareForParsing checkForInterrupt
        
        checkForInterrupt()
        
        let startTime = System.DateTime.Now
        let starts = graph.GetStartsForFiles startFiles |> Array.map ((*) 1<positionInInput>)
        (*
        for start in starts do
            currentInput.Value.RemoveCyclesForStart (int start) endToken
        *)
        
        //-------------------------------
        
        (*
        let pda = new MyPDA()
        let simulation = Simulation(pda)
        
        let myGraph = MyGraph(dynamicIndex)
        
        let startContexts = starts |> Array.mapi (fun i start -> (i, start |> myGraph.GetNode |> simulation.Load i))
        simulation.Run()
        
        Logging.log (sprintf "Simulation time is %A" (System.DateTime.Now - startTime))
        let startTime = System.DateTime.Now
        
        let validPaths = Stack<string>() 
        startContexts 
        |> Array.filter (fun (i, context) -> false)//context.survived)
        |> Array.rev
        |> Array.map (fun (i, context) -> (simulation.GetFinals i, context))
        |> Array.iter (fun (finals, context) -> ResultProcessing.extractAllValidPaths (fun path -> printfn "%s" path; validPaths.Push path) finals context)
        
        let mutable counter = 0
        let decoder = graph.GetDecoder()
        for result in validPaths do
            printfn "%s" result
            
            let decoded = ResultProcessing.decode result decoder
            printfn "%s" decoded
            
            writer.WriteLine decoded
            writer.WriteLine ()
        *)
        //-------------------------------
        
        Logging.log (sprintf "Results extraction time is %A" (System.DateTime.Now - startTime))

        let startTime = System.DateTime.Now
        let task, parserCancellation = Parsing.parseAsync (Option.get parser) starts
        Volatile.Write(cancellation, parserCancellation)
        
        task.Wait()
        let roots = task.Result
        
        Logging.log (sprintf "Parsing time is %A" (System.DateTime.Now - startTime))
        Logging.log (sprintf "Full time is %A" (System.DateTime.Now - globalStartTime))
        checkForInterrupt()
        
        //let isNotLambda id = graph.GetOwnerNameByState (id * 1<state>) |> fun name -> (name.Substring (name.Length - 3)) <> "(0)"
        
        let startTime = System.DateTime.Now
        let results = 
            let temporaryResults = new HashSet<_>()
            roots
            //|> Array.filter (fun root -> (int64 (root.getExtension()) >>> 32 |> int |> isNotLambda) && (int64 (root.getExtension()) &&& 0xFFFFFFFFL |> int |> isNotLambda))
            |> Array.map (fun x -> (ResultProcessing.extractNonCyclicPath x (parser.Value.Source.IntToString) checkForInterrupt) |> Seq.map (fun path -> (int64 (x.getExtension()) &&& 0xFFFFFFFFL |> int), path))
            |> Array.iter (fun s -> temporaryResults.UnionWith s)
            temporaryResults
        
        Logging.log (sprintf "Paths extraction time is %A" (System.DateTime.Now - startTime))
        checkForInterrupt()
        
        let startTime = System.DateTime.Now
        let decoder = graph.GetDecoder()
        for (start, result) in results do
            
            let decoded = ResultProcessing.decode result decoder
            if decoded <> "" then
                printfn "%s" result
                printfn "%i %s" (graph.GetNodeByState (start * 1<state>)) (graph.GetOwnerNameByState (start * 1<state>))
                printfn "%s" decoded
                
                writer.WriteLine ("0;0;0 " + (graph.GetOwnerNameByState (start * 1<state>)))
                writer.WriteLine decoded
                writer.WriteLine ()
            
        Logging.log (sprintf "Decoding time is %A" (System.DateTime.Now - startTime))
        writer.Flush()
    
    member this.Start() =
    (*
        use reader = new StreamReader (@"C:\hackathon\asdf.Generated.db")
        graph.Deserialize reader

        performParsing reader (new StreamWriter(@"C:\hackathon\test.txt")) (graph.GetFiles() |> Seq.toArray)
        *)
    
        (*
        use reader = new StreamReader ("C:\hackathon\DotnetProducts.Generated.db")
        graph.Deserialize reader

        performParsing reader (new StreamWriter(@"C:\hackathon\test.txt")) (graph.GetAllFiles() |> Seq.toArray)
        *)
        (*
        let testMethod = {methodName = "test"; startNode = 0<local_state>; finalNode = 0<local_state>; inheritedFrom = ""}
        let testEdges = [||]
        let testCalls = [||]
        
        graphBuilder.UpdateMethod testMethod testEdges testCalls
        
        graphBuilder.UpdateFileInfo "testFile" (set ["test"])
        *)
    
        socket.Start()
        client <- socket.AcceptTcpClient()
        
        use stream = client.GetStream()
        use reader = new StreamReader(stream)
        use writer = new StreamWriter(stream)
        
        let mutable restoredFrom = ""
        
        while isProcess do
            if asyncReadTask <> null then
                asyncReadTask.Wait()
                asyncReadTask <- null
                
            let mutable messageType = reader.ReadLine()
            let mutable data = reader.ReadLine()
            let mutable success = false
            
            if messageType = null then 
                messageType <- "terminate"
                data <- ""
            
            printfn "incoming message:"
            printfn "%s" messageType
            printfn "%s" data
            
            try
                use dataStream = new MemoryStream(System.Text.Encoding.ASCII.GetBytes(data))
                match messageType with
                | "restore" ->
                    let message = RestoreMessage.FromJson dataStream
                    restoredFrom <- message.sourcePath
                    if System.IO.File.Exists message.sourcePath then
                        use reader = new StreamReader (message.sourcePath)
                        graph.Deserialize reader

                        //performParsing reader writer (graph.GetAllFiles() |> Seq.toArray)
                        
                    invalidateParser()
                    success <- true
                | "add_method" ->
                    let message = AddMethodMessage.FromJson dataStream
                    graphBuilder.UpdateMethod (message.method) (message.edges) (message.callInfos)
                    
                    invalidateParser()
                    success <- true
                | "add_specific_decoder_info" ->
                    let message = AddSpecificDecoderInfo.FromJson dataStream
                    graphBuilder.AddDecoderInfo message.key message.value
                    success <- true
                | "update_file" ->
                    let message = UpdateFileMessage.FromJson dataStream
                    graphBuilder.UpdateFileInfo (message.fileName) (set message.methods)
                    
                    invalidateParser()
                    success <- true
                | "run_analysis" ->
                    (*
                    if (restoredFrom <> "") && (not parserIsValid) then
                        let startTime = System.DateTime.Now
                        use fileStream = new StreamWriter (restoredFrom)
                        graph.Serialize fileStream
                        graph.GetStorage.DumpToDot (@"C:\hackathon\graph.db")
                        Logging.log (sprintf "Database saving time is %A" (System.DateTime.Now - startTime))
                        *)
                    
                    let message = RunAnalysisMessage.FromJson dataStream
                    performParsing reader writer message.starts
                    success <- true
                | "dump_graph" ->
                    graph.DumpStatesLevel writer
                    success <- true
                | "dump_decoder" ->
                    graph.DumpDecoder writer
                    success <- true
                | "terminate" ->
                    if (restoredFrom <> "") then
                        use fileStream = new StreamWriter (restoredFrom)
                        graph.Serialize fileStream
                    
                    isProcess <- false
                    success <- true
                | "reset" ->
                    graph <- graphProvider()
                    graphBuilder <- new ControlFlowGraphBuilder(graph)
                    
                    invalidateParser()
                    success <- true
                | _ -> ()
            with e -> printfn "%s\r\n%s" e.Message e.StackTrace
            
            if success then
                writer.WriteLine("success")
                printfn "success"
            else
                writer.WriteLine("failure")
                printfn "failure"
                
            writer.Flush()
                
        client.Close()
        socket.Stop()           
        
        
        
        
        
