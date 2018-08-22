namespace CfrAnalyser.Graph

open System.IO
open System.Collections.Generic
open QuickGraph

module internal ReadHelper =
    let tryReadLine (reader: StreamReader) = 
        let peek = reader.Peek()
        if peek = int '#' || peek = -1 then
            (false, null)
        else
            (true, reader.ReadLine())
    
    let splitOnFirstOccurence (str: string) (sep: string) =
        let index = str.IndexOf sep
        (str.Substring (0, index), str.Substring (index + sep.Length))
    
    let fromString<'t> (value: string): 't =
        if (typeof<'t> = typeof<int>) then
            (System.Int32.Parse value) :> obj :?> 't
        elif (typeof<'t> = typeof<string>) then
            value :> obj :?> 't
        else 
            failwith "unknown value type"

type QuickEdge(source: int, label: string, target: int) = 
    inherit TaggedEdge<int, string>(source, target, label)
    
    override this.Equals obj =
        let edge = obj :?> QuickEdge
        
        edge.Source = this.Source && edge.Target = this.Target && edge.Tag = this.Tag
        
    override this.GetHashCode() =
        this.Source.GetHashCode() * this.Tag.GetHashCode() * this.Target.GetHashCode()

type IQuickSerializable =
    abstract member Serialize: StreamWriter -> unit
    abstract member Deserialize: StreamReader -> (int -> unit) -> unit

type QuickGraphIndex<'key when 'key : equality>() = 
    let dictionary = Dictionary<'key, int>()
    let reverseDictionary = Dictionary<int, 'key>()
    
    member this.RemoveFromIndex (id: int) =
        let exists, key = reverseDictionary.TryGetValue id
        if exists then
            dictionary.Remove key |> ignore
            reverseDictionary.Remove id |> ignore
            
    interface IQuickSerializable with 
        member this.Serialize writer =
            for pair in (this :> IGraphIndex<'key>).Pairs() do
                writer.WriteLine (sprintf "%s %s" ((snd pair).ToString()) ((fst pair).ToString()))
        
        member this.Deserialize (reader: StreamReader) (onNodeRestored: int -> unit) = 
            Seq.initInfinite (fun _ -> ReadHelper.tryReadLine reader)
            |> Seq.takeWhile (fun (success, _) -> success)
            |> Seq.iter 
                (
                    fun (_, data) -> 
                        let value, key = ReadHelper.splitOnFirstOccurence data " "
                        let value = int value
                        onNodeRestored value
                        (this :> IGraphIndex<'key>).AddNode (ReadHelper.fromString<'key> key) value |> ignore
                )
    
    interface IGraphIndex<'key> with
        member this.AddNode (key: 'key) (id: int) =
            if dictionary.ContainsKey key then
                false
            else
                dictionary.Add (key, id)
                reverseDictionary.Add (id, key)
                true
                
        member this.FindNode (key: 'key) = 
            dictionary.TryGetValue key
            
        member this.FindKey (id: int) = 
            reverseDictionary.TryGetValue id
            
        member this.Pairs() = 
            dictionary.Keys |> Seq.map (fun key -> (key, dictionary.[key]))

type QuickGraphDenseIndex<'key when 'key : equality>(indexer: 'key -> int, deindexer: int -> 'key) =
    inherit DenseGraphIndex<'key>(indexer, deindexer)
    
    let storage = ResizeArray<int>()
    let reverseDictionary = SortedDictionary<int, 'key>()
    
    member this.RemoveFromIndex (nodeId: int) =
        let exists, key = reverseDictionary.TryGetValue nodeId
        if exists then
            let index = indexer reverseDictionary.[nodeId]
            this.FreeIndex index
            
            storage.[index] <- -1
            reverseDictionary.Remove nodeId |> ignore
    
    override this.AddNode (key: 'key) (nodeId: int) =
        let index = indexer key
        while index >= storage.Count do
            storage.Add -1
            
        if storage.[index] <> -1 then
            false
        else
            storage.[index] <- nodeId
            reverseDictionary.Add (nodeId, key)
            true
            
    override this.FindNode (key: 'key) = 
        let index = indexer key
        if (index < 0 || index >= storage.Count || storage.[index] = -1) then
            (false, -1)
        else
            (true, storage.[index])
            
    override this.FindKey (id: int) = 
        reverseDictionary.TryGetValue id
        
    override this.Pairs() = 
        [|0 .. storage.Count - 1|] 
        |> Array.map (fun i -> (deindexer i, storage.[i])) 
        |> Array.filter (fun (key, node) -> node <> -1)
        |> seq
        
    interface IQuickSerializable with 
        member this.Serialize writer =
            writer.WriteLine (this.Provider.DumpStateToString())
            for pair in (this :> IGraphIndex<'key>).Pairs() do
                writer.WriteLine (sprintf "%s %s" ((snd pair).ToString()) ((fst pair).ToString()))
                
        member this.Deserialize (reader: StreamReader) (onNodeRestored: int -> unit) = 
            let providerInfo = reader.ReadLine()
            this.Provider.RestoreStateFromString providerInfo
            Seq.initInfinite (fun _ -> ReadHelper.tryReadLine reader)
            |> Seq.takeWhile (fun (success, _) -> success)
            |> Seq.iter 
                (
                    fun (_, data) -> 
                        let value, key = ReadHelper.splitOnFirstOccurence data " "
                        let value = int value
                        onNodeRestored value
                        (this :> IGraphIndex<'key>).AddNode (ReadHelper.fromString<'key> key) value |> ignore
                )

type QuickGraphStorage() =
    inherit BidirectionalGraph<int, QuickEdge>()
    
    let assertTrue condition = assert condition
    
    let nodeLabels = SortedDictionary<int, string>()
    
    let indices = Dictionary<string, (obj * (int -> unit))>()
    
    let weakEdges = HashSet<QuickEdge>()
    
    let mutable onEdgeRemovedListener = fun _ _ _ -> ()
    
    let denseNodesIndex = new DenseIdsProvider()
    
    member private this.DeserializeEdges (reader: StreamReader) =
        Seq.initInfinite (fun _ -> ReadHelper.tryReadLine reader)
        |> Seq.takeWhile (fun (success, _) -> success)
        |> Seq.iter 
            (
                fun (_, data) -> 
                    let splitted = data.Split ' '
                    
                    this.AddVertex (int splitted.[0]) |> ignore
                    this.AddVertex (int splitted.[2]) |> ignore
                    
                    (this :> IGraphStorage).AddEdge (int splitted.[0]) splitted.[1] (int splitted.[2]) |> assertTrue
            )
            
    member private this.DeserializeLabels (reader: StreamReader) =
        Seq.initInfinite (fun _ -> ReadHelper.tryReadLine reader)
        |> Seq.takeWhile (fun (success, _) -> success)
        |> Seq.iter 
            (
                fun (_, data) -> 
                    let key, value = ReadHelper.splitOnFirstOccurence data " "
                    let key = int key
                    
                    (this :> IGraphStorage).SetNodeLabel key value |> assertTrue
            )
    
    interface IGraphStorage with
        member this.SetOnEdgeRemovedListener (listener: int -> string -> int -> unit) =
            this.add_EdgeRemoved (fun edge -> listener (edge.Source) (edge.Tag) (edge.Target))
            
        member this.SetOnEdgeAddedListener (listener: int -> string -> int -> unit) =
            this.add_EdgeAdded (fun edge -> listener (edge.Source) (edge.Tag) (edge.Target))
            
        member this.SetOnNodeAddedListener (listener: int -> unit) =
            this.add_VertexAdded (fun vertex -> listener vertex)
            
        member this.CreateNode() = 
            let id = denseNodesIndex.GetFreeId()
            let success = this.AddVertex id 
            id
            
        member this.RemoveNode (id: int) =
            let status = this.RemoveVertex id
            denseNodesIndex.FreeId id
            
            if nodeLabels.ContainsKey id then
                nodeLabels.Remove id |> assertTrue
            
            indices.Values |> Seq.iter (fun (_, remover) -> remover id )
            status
            
        member this.SetNodeLabel (id: int) (label: string) =
            if nodeLabels.ContainsKey id then
                false
            else
                nodeLabels.Add (id, label)
                true
                
        member this.GetNodeLabel (id: int) =
            nodeLabels.TryGetValue id
            
        member this.AddWeakEdge source label target =
            let edge = QuickEdge(source, label, target)
            if not (this.ContainsEdge edge) then
                weakEdges.Add edge |> ignore
                this.AddEdge (edge)
            else
                true
        
        member this.ClearWeakEdges() =
            for edge in weakEdges do
                this.RemoveEdge edge |> (fun s -> assert s)
            
            weakEdges.Clear()
        
        member this.AddEdge source label target =
            let edge = QuickEdge(source, label, target)
            if not (this.ContainsEdge edge) then
                this.AddEdge (edge)
            else
                true
            
        member this.RemoveEdge source label target =
            this.RemoveEdge (QuickEdge(source, label, target))
    
        member this.OutgoingEdges (id: int) = 
            this.OutEdges id
            |> Seq.map (fun edge -> (edge.Tag, edge.Target))
            |> Seq.toArray
            
        member this.IncomingEdges (id: int) = 
            this.InEdges id
            |> Seq.map (fun edge -> (edge.Tag, edge.Source))
            |> Seq.toArray
        
        member this.CreateIndex<'key when 'key : equality> (name: string) =
            let index = new QuickGraphIndex<'key>()
            indices.Add (name, (index :> obj, index.RemoveFromIndex))
            true
            
        member this.CreateDenseIndex<'key when 'key : equality> (name: string) (indexer: 'key -> int) (deindexer: int -> 'key) =
            let index = new QuickGraphDenseIndex<'key>(indexer, deindexer)
            indices.Add (name, (index :> obj, index.RemoveFromIndex))
            true
            
        member this.GetIndex<'key when 'key : equality> (name: string) =
            let exists, (object, _) = indices.TryGetValue name
            (exists, object :?> QuickGraphIndex<'key> :> IGraphIndex<'key>)
            
        member this.GetDenseIndex<'key when 'key : equality> (name: string) =
            let exists, (object, _) = indices.TryGetValue name
            (exists, object :?> QuickGraphDenseIndex<'key> :> DenseGraphIndex<'key>)
        
        member this.DumpToDot (path: string) =
            use writer = new StreamWriter(path)
            
            writer.WriteLine "digraph G {"
            
            for edge in this.Edges do
                writer.WriteLine (sprintf "%i -> %i [label=\"%s\"];" edge.Source edge.Target edge.Tag)
            
            writer.WriteLine "}"
            
        member this.Serialize (writer: StreamWriter) =
            for pair in indices do
                let (index, _) = pair.Value
                    
                writer.WriteLine (sprintf "#index %s" pair.Key)
                
                (index :?> IQuickSerializable).Serialize writer
                
            writer.WriteLine "#graph"
            for edge in this.Edges do
                writer.WriteLine (sprintf "%i %s %i" edge.Source edge.Tag edge.Target)
                
            writer.WriteLine "#node_ids_provider"
            writer.WriteLine (denseNodesIndex.DumpStateToString())
            
            writer.WriteLine "#labels"
            for pair in nodeLabels do
                writer.WriteLine (sprintf "%i %s" pair.Key pair.Value)
            
        
        member this.Deserialize (reader: StreamReader) =
            while not reader.EndOfStream do
                let typeLine = reader.ReadLine()
                
                assert (typeLine.[0] = '#')
                
                let splitted = (typeLine.Split ' ')
                let blockType = splitted.[0]
                
                match blockType with
                | "#graph" -> 
                    this.DeserializeEdges reader
                | "#labels" ->
                    this.DeserializeLabels reader
                | "#node_ids_provider" ->
                    let data = reader.ReadLine()
                    denseNodesIndex.RestoreStateFromString data
                | "#index" ->
                    let name = splitted.[1]
                    ((fst indices.[(typeLine.Split ' ').[1]]) :?> IQuickSerializable).Deserialize reader (this.AddVertex >> ignore)
                    
