//this tables was generated by RACC
//source grammar:..\Tests\RACC\test_cls_with_head\test_cls_with_head.yrd
//date:3/27/2011 11:43:00 AM

#light "off"
module Yard.Generators.RACCGenerator.Tables_Cls_head

open Yard.Generators.RACCGenerator

type symbol =
    | T_MINUS
    | NT_s
    | NT_raccStart
let getTag smb =
    match smb with
    | T_MINUS -> 2
    | NT_s -> 1
    | NT_raccStart -> 0
let getName tag =
    match tag with
    | 2 -> T_MINUS
    | 1 -> NT_s
    | 0 -> NT_raccStart
let private autumataDict = 
dict [|(0,{ 
   DIDToStateMap = dict [|(0,(State 0));(1,(State 1));(2,DummyState)|];
   DStartState   = 0;
   DFinaleStates = Set.ofArray [|1|];
   DRules        = Set.ofArray [|{ 
   FromStateID = 0;
   Symbol      = (DSymbol 1);
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSmbS 0))|]
|];
   ToStateID   = 1;
}
;{ 
   FromStateID = 1;
   Symbol      = Dummy;
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSmbE 0))|]
|];
   ToStateID   = 2;
}
|];
}
);(1,{ 
   DIDToStateMap = dict [|(0,(State 0));(1,(State 1));(2,(State 2));(3,DummyState);(4,DummyState)|];
   DStartState   = 0;
   DFinaleStates = Set.ofArray [|1;2|];
   DRules        = Set.ofArray [|{ 
   FromStateID = 0;
   Symbol      = (DSymbol 2);
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSeqS 5));(FATrace (TSmbS 1))|]
|];
   ToStateID   = 1;
}
;{ 
   FromStateID = 1;
   Symbol      = (DSymbol 2);
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSmbE 1));(FATrace (TClsS 2));(FATrace (TClsE 2));(FATrace (TSeqE 5))|]
;List.ofArray [|(FATrace (TSmbE 1));(FATrace (TClsS 2));(FATrace (TSeqS 4));(FATrace (TSmbS 3))|]
|];
   ToStateID   = 2;
}
;{ 
   FromStateID = 1;
   Symbol      = Dummy;
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSmbE 1));(FATrace (TClsS 2));(FATrace (TClsE 2));(FATrace (TSeqE 5))|]
;List.ofArray [|(FATrace (TSmbE 1));(FATrace (TClsS 2));(FATrace (TSeqS 4));(FATrace (TSmbS 3))|]
|];
   ToStateID   = 3;
}
;{ 
   FromStateID = 2;
   Symbol      = (DSymbol 2);
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSmbE 3));(FATrace (TSeqE 4));(FATrace (TClsE 2));(FATrace (TSeqE 5))|]
;List.ofArray [|(FATrace (TSmbE 3));(FATrace (TSeqE 4));(FATrace (TSeqS 4));(FATrace (TSmbS 3))|]
|];
   ToStateID   = 2;
}
;{ 
   FromStateID = 2;
   Symbol      = Dummy;
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSmbE 3));(FATrace (TSeqE 4));(FATrace (TClsE 2));(FATrace (TSeqE 5))|]
;List.ofArray [|(FATrace (TSmbE 3));(FATrace (TSeqE 4));(FATrace (TSeqS 4));(FATrace (TSmbS 3))|]
|];
   ToStateID   = 4;
}
|];
}
)|]

let private gotoSet = 
    Set.ofArray [|((0, 0, 1), set [(0, 1)]);((0, 0, 2), set [(1, 1)]);((1, 0, 2), set [(1, 1)]);((1, 1, 2), set [(1, 2)]);((1, 2, 2), set [(1, 2)])|]
    |> dict
let tables = { gotoSet = gotoSet; automataDict = autumataDict }

