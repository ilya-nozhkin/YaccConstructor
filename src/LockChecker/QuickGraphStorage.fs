namespace LockChecker.Graph

open System.Collections.Generic
open QuickGraph

type QuickEdge(source: int, label: string, target: int) = 
    inherit TaggedEdge<int, string>(source, target, label)
    
    override this.Equals obj =
        let edge = obj :?> QuickEdge
        
        edge.Source = this.Source && edge.Target = this.Target && edge.Tag = this.Tag
        
    override this.GetHashCode() =
        this.Source.GetHashCode() * this.Tag.GetHashCode() * this.Target.GetHashCode()

type QuickGraphIndex<'key when 'key : equality>() = 
    let dictionary = Dictionary<'key, int>()
    let reverseDictionary = Dictionary<int, 'key>()
    
    member this.RemoveFromIndex (id: int) =
        let exists, key = reverseDictionary.TryGetValue id
        if exists then
            dictionary.Remove key |> ignore
            reverseDictionary.Remove id |> ignore
    
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

type QuickGraphStorage() =
    let graph = BidirectionalGraph<int, QuickEdge>()
    
    let mutable nodesCounter = 0
    
    let nodeLabels = SortedDictionary<int, string>()
    
    let indices = Dictionary<string, (obj * (int -> unit))>()
    
    interface IGraphStorage with
        member this.CreateNode() = 
            let id = nodesCounter
            let success = graph.AddVertex id 
            nodesCounter <- nodesCounter + 1
            id
            
        member this.RemoveNode (id: int) =
            let status = graph.RemoveVertex id
            
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
        
        member this.AddEdge source label target =
            let edge = QuickEdge(source, label, target)
            if not (graph.ContainsEdge edge) then
                graph.AddEdge (edge)
            else
                true
            
        member this.RemoveEdge source label target =
            graph.RemoveEdge (QuickEdge(source, label, target))
    
        member this.OutgoingEdges (id: int) = 
            graph.OutEdges id
            |> Seq.map (fun edge -> (edge.Tag, edge.Target))
            |> Seq.toArray
            
        member this.IncomingEdges (id: int) = 
            graph.InEdges id
            |> Seq.map (fun edge -> (edge.Tag, edge.Source))
            |> Seq.toArray
        
        member this.CreateIndex<'key when 'key : equality> (name: string) =
            let index = new QuickGraphIndex<'key>()
            indices.Add (name, (index :> obj, index.RemoveFromIndex))
            true
            
        member this.GetIndex<'key when 'key : equality> (name: string) =
            let exists, (object, _) = indices.TryGetValue name
            (exists, object :?> QuickGraphIndex<'key> :> IGraphIndex<'key>)
