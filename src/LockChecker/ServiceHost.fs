namespace LockChecker

open System.IO
open System.Net
open System.Net.Sockets
open System.Runtime.Serialization.Json
open System.Runtime.Serialization
open System.Collections.Generic
open System.Threading.Tasks

open LockChecker.Graph

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
    
    let mutable mostRecentlyUpdatedFile: string = null
        
    let performParsing (reader: StreamReader) (writer: StreamWriter) (startFile: string) =
        graph.GenerateWeakEdges()
        use statesWriter = new StreamWriter(@"C:\hackathon\states.graph")
        graph.DumpStatesLevel statesWriter
        graph.GetStorage.DumpToDot (@"C:\hackathon\graph.db")
    
        let statistics = graph.GetStatistics()
        let parserSource = Parsing.generateParser statistics.calls statistics.locks statistics.asserts
        
        let parallelTasks = 2
        let inputs = graph.GetParserInput startFile parserSource.StringToToken
        
        let task, cancellation = Parsing.parseAbstractInputsAsync parserSource [|inputs|]
        
        let asyncMessage = reader.ReadLineAsync()
        let asyncCanceller = 
            asyncMessage.ContinueWith (
                fun (completed: Task<_>) -> 
                    if completed.Result = "interrupt" then cancellation.Cancel()
            )
            
        asyncReadTask <- asyncCanceller
        
        if asyncCanceller.Status = TaskStatus.Created then
            asyncCanceller.Start()
        
        task.Wait()
        
        let roots = task.Result
        
        let results = 
            let temporaryResults = new HashSet<_>()
            roots
            |> Array.map (fun x -> ResultProcessing.extractNonCyclicPaths x parserSource.IntToString)
            |> Array.iter (fun s -> temporaryResults.UnionWith s)
            temporaryResults
        
        let decoder = graph.GetDecoder()
        for result in results do
            printfn "%s" result
            
            let decoded = ResultProcessing.decode result decoder
            printfn "%s" decoded
            
            writer.WriteLine decoded
            writer.WriteLine ()
            
        writer.Flush()
        
        graph.ClearWeakEdges()
    
    member this.Start() =
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
                    success <- true
                | "add_method" ->
                    let message = AddMethodMessage.FromJson dataStream
                    graphBuilder.UpdateMethod (message.method) (message.edges) (message.callInfos)
                    success <- true
                | "add_specific_decoder_info" ->
                    let message = AddSpecificDecoderInfo.FromJson dataStream
                    graphBuilder.AddDecoderInfo message.key message.value
                    success <- true
                | "update_file" ->
                    let message = UpdateFileMessage.FromJson dataStream
                    graphBuilder.UpdateFileInfo (message.fileName) (set message.methods)
                    mostRecentlyUpdatedFile <- message.fileName
                    success <- true
                | "run_analysis" ->
                    let message = RunAnalysisMessage.FromJson dataStream
                    if mostRecentlyUpdatedFile = null then
                        asyncReadTask <- reader.ReadLineAsync();
                    else
                        performParsing reader writer mostRecentlyUpdatedFile
                    success <- true
                | "dump_graph" ->
                    graph.DumpStatesLevel writer
                    success <- true
                | "terminate" ->
                    if (restoredFrom <> "") then
                        use fileStream = new StreamWriter ("graph.dump")
                        graph.Serialize fileStream
                    
                    isProcess <- false
                    success <- true
                | "reset" ->
                    graph <- graphProvider()
                    graphBuilder <- new ControlFlowGraphBuilder(graph)
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
        
        
        
        
        
