namespace Yard.Generators.GLL.ParserCommon
open System.Collections.Generic
open Yard.Generators.Common.DataStructures
open AbstractAnalysis.Common

type ParserSourceGLL ( outNonterms        : (int<positionInGrammar> * int<positionInGrammar>) [] []
                     , startState         : int<positionInGrammar>
                     , finalStates        : HashSet<int<positionInGrammar>>
                     , nontermCount       : int
                     , terminalNums       : HashSet<int<token>>
                     , intToString        : Dictionary<int,string>
                     , anyNonterm         : int<positionInGrammar>
                     , stateAndTokenToNewState : Dictionary<int64, int<positionInGrammar>>
                     , stringToToken      : Dictionary<string,int<token>>
                     , multipleInEdges    : bool []
                     , ?rightSideToRule   : string -> int
                     ) =

    //let getTermsDictionaryKey (state: int<positionInGrammar>) token = 
    //    int( (int state <<< 16) ||| (token - outNonterms.Length) )
    
    let getTermsDictionaryKey (state: int<positionInGrammar>) (token: int<token>) : int64 =
        ((int64 state <<< 32) ||| (int64 (token - outNonterms.Length * 1<token>)))
    
    let stateOffset = 5
    let invalidState = -10<positionInGrammar>
    
    let compactStateAndTokenMap = 
        let counts = new SortedDictionary<int, int * int>()
        let mutable maxState = 0
        
        for pair in stateAndTokenToNewState do
            let mutable state, token = CommonFuns.unpack pair.Key
            token <- token + outNonterms.Length
            if (state + stateOffset) > maxState then
                maxState <- (state + stateOffset)
                
            let contains, minmax = counts.TryGetValue state
            if not contains then 
                counts.Add (state, (token, token))
            else
                let (min, max) = minmax
                if token > max then
                    counts.[state] <- (min, token)
                elif token < min then
                    counts.[state] <- (token, max)
                
        let stateMap = Array.init (maxState + 1) (
                           fun i -> 
                               let i = i - stateOffset
                               let contains, minmax = counts.TryGetValue i
                               if contains then
                                   let min, max = minmax
                                   let tokenMap = Array.create<int<positionInGrammar>> (max - min + 2) invalidState
                                   tokenMap.[0] <- (min - 1) * 1<positionInGrammar>
                                   tokenMap
                               else
                                   Array.zeroCreate<int<positionInGrammar>> 1
                       )
                       
                       
        for pair in stateAndTokenToNewState do
            let mutable state, token = CommonFuns.unpack pair.Key
            token <- token + outNonterms.Length
            state <- state + stateOffset
            let offset = stateMap.[state].[0]
            stateMap.[state].[token - (int offset)] <- pair.Value
        
        stateMap
    
    let strToToken str = 
        let isExist, value = stringToToken.TryGetValue(str)
        if isExist
        then
            value
        else
            //failwith "Such string is not in a grammar alphabet."
            -2<token>

    let rev (map : Map<int, string>) = 
            Map.fold(fun (m : Map<string, int>) k v -> m.Add(v, k)) Map.empty map

    member this.OutNonterms             = outNonterms
    member this.FinalStates             = finalStates
    member this.StartState              = startState
    member this.NonTermCount            = nontermCount
    member this.TerminalNums            = terminalNums
    member this.IntToString             = intToString
    member this.GetTermsDictionaryKey   = getTermsDictionaryKey
    member this.AnyNonterm              = anyNonterm
    
    member this.StateAndTokenToNewState (state: int<positionInGrammar>) (token: int<token>) =
        let intState = (int state) + stateOffset
        if (intState >= 0) && (intState < compactStateAndTokenMap.Length) then
            let arrayRef = compactStateAndTokenMap.[intState]
            let offset = int arrayRef.[0] 
            let id = (int token) - offset
            
            if (id >= 1) && (id < arrayRef.Length) then 
                arrayRef.[id]
            else 
                invalidState
        else
            invalidState
        
    member this.StringToToken           = strToToken
    member this.MultipleInEdges         = multipleInEdges
    //member this.RightSideToRule         = rightSideToRule.Value

    member this.NameToId = 
        rev (this.IntToString |> Seq.map (|KeyValue|)|> Map.ofSeq)