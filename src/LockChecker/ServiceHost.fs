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
type AddEdgePackMessage =
    {
        [<field: DataMember(Name="edges")>]
        edges: RawEdge []
    }
    static member JsonReader = DataContractJsonSerializer(typeof<AddEdgePackMessage>)
    static member FromJson (source: Stream) =
        AddEdgePackMessage.JsonReader.ReadObject(source) :?> AddEdgePackMessage

[<DataContract>]
type RunAnalysisMessage =
    {
        [<field: DataMember(Name="starts")>]
        starts: int [] []
    }
    static member JsonReader = DataContractJsonSerializer(typeof<RunAnalysisMessage>)
    static member FromJson (source: Stream) =
        RunAnalysisMessage.JsonReader.ReadObject(source) :?> RunAnalysisMessage
        
[<DataContract>]
type DecoderRecord =
    {
        [<field: DataMember(Name="code")>]
        code: string
        
        [<field: DataMember(Name="data")>]
        data: string
    }

[<DataContract>]
type UpdateDecoderMessage =
    {
        [<field: DataMember(Name="records")>]
        records: DecoderRecord []
    }
    static member JsonReader = DataContractJsonSerializer(typeof<UpdateDecoderMessage>)
    static member FromJson (source: Stream) =
        UpdateDecoderMessage.JsonReader.ReadObject(source) :?> UpdateDecoderMessage

type ServiceHost(graphProvider: unit -> IControlFlowGraph, port) =
    let socket = TcpListener.Create (port)
    let mutable client = null
    let mutable isProcess = true
    
    let mutable graph: IControlFlowGraph = graphProvider()
    let addedMethodsBuffer = Dictionary<string, AddMethodMessage>()
    
    let mutable asyncReadTask = null
    
    let mutable mostRecentlyUpdatedFile: string = null
    
    let updateFile (message: UpdateFileMessage) =
        let oldSet = graph.GetFileInfo message.fileName
        let newSet = set message.methods
        
        let removed = Set.difference oldSet newSet
        let updated = Set.intersect oldSet newSet
        let added = Set.difference newSet oldSet
        
        for method in removed do
            graph.RemoveMethod method
            
        for method in updated do
            let message = addedMethodsBuffer.[method]
            addedMethodsBuffer.Remove method |> ignore
            graph.AlterMethod message.method message.edges
        
        for method in added do
            let message = addedMethodsBuffer.[method]
            addedMethodsBuffer.Remove method |> ignore
            graph.AddMethod message.method message.edges
        
        graph.UpdateFileInfo message.fileName newSet
        
    let performParsing (reader: StreamReader) (writer: StreamWriter) =
        let statistics = graph.GetStatistics()
        let parserSource = Parsing.generateParser statistics.calls statistics.locks statistics.asserts
        graph.SetTokenizer parserSource.StringToToken
        
        graph.PrepareForParsing()
        
        let parallelTasks = 2
        let inputs = graph.GetParserInputs parallelTasks
        
        let task, cancellation = Parsing.parseAbstractInputsAsync parserSource inputs
        
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
        
        results |> Seq.iter (writer.WriteLine)
        writer.Flush()
        
        graph.CleanUpAfterParsing()
    
    member this.Start() =
        socket.Start()
        client <- socket.AcceptTcpClient()
        
        use stream = client.GetStream()
        use reader = new StreamReader(stream)
        use writer = new StreamWriter(stream)
        
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
                | "add_method" -> 
                    let message = AddMethodMessage.FromJson dataStream
                    addedMethodsBuffer.[message.method.name] <- message
                    success <- true
                | "update_file" ->
                    let message = UpdateFileMessage.FromJson dataStream
                    updateFile message
                    mostRecentlyUpdatedFile <- message.fileName
                    success <- true
                | "add_edge_pack" -> 
                    let message = AddEdgePackMessage.FromJson dataStream
                    graph.AddEdges message.edges
                    success <- true
                | "update_decoder" -> 
                    let message = UpdateDecoderMessage.FromJson dataStream
                    message.records |> Array.iter (fun record -> ResultProcessing.decoder.[record.code] <- record.data)
                    success <- true
                | "run_analysis" ->
                    let message = RunAnalysisMessage.FromJson dataStream
                    graph.SetStartFile mostRecentlyUpdatedFile
                    performParsing reader writer
                    success <- true
                | "dump_graph" ->
                    graph.DumpTriples writer
                    success <- true
                | "terminate" ->
                    use fileStream = new FileStream ("graph.dump", FileMode.Create)
                    graph.Serialize fileStream
                    
                    isProcess <- false
                    success <- true
                | "reset" ->
                    graph <- graphProvider()
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
        
        
        
        
        
