//this tables was generated by RACC
//source grammar:..\Tests\RACC\test_summator_1\test_summator_1.yrd
//date:3/27/2011 11:43:09 AM

#light "off"
module Yard.Generators.RACCGenerator.Tables_Summator_1

open Yard.Generators.RACCGenerator

type symbol =
    | T_PLUS
    | T_NUMBER
    | NT_e
    | NT_s
    | NT_raccStart
let getTag smb =
    match smb with
    | T_PLUS -> 4
    | T_NUMBER -> 3
    | NT_e -> 2
    | NT_s -> 1
    | NT_raccStart -> 0
let getName tag =
    match tag with
    | 4 -> T_PLUS
    | 3 -> T_NUMBER
    | 2 -> NT_e
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
   DIDToStateMap = dict [|(0,(State 0));(1,(State 1));(2,DummyState)|];
   DStartState   = 0;
   DFinaleStates = Set.ofArray [|1|];
   DRules        = Set.ofArray [|{ 
   FromStateID = 0;
   Symbol      = (DSymbol 2);
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSeqS 2));(FATrace (TSmbS 1))|]
|];
   ToStateID   = 1;
}
;{ 
   FromStateID = 1;
   Symbol      = Dummy;
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSmbE 1));(FATrace (TSeqE 2))|]
|];
   ToStateID   = 2;
}
|];
}
);(2,{ 
   DIDToStateMap = dict [|(0,(State 0));(1,(State 1));(2,(State 2));(3,(State 3));(4,(State 4));(5,DummyState);(6,DummyState)|];
   DStartState   = 0;
   DFinaleStates = Set.ofArray [|1;4|];
   DRules        = Set.ofArray [|{ 
   FromStateID = 0;
   Symbol      = (DSymbol 2);
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TAlt1S 9));(FATrace (TSeqS 4));(FATrace (TSmbS 3))|]
;List.ofArray [|(FATrace (TAlt2S 10));(FATrace (TSeqS 8));(FATrace (TSmbS 5))|]
|];
   ToStateID   = 2;
}
;{ 
   FromStateID = 0;
   Symbol      = (DSymbol 3);
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TAlt1S 9));(FATrace (TSeqS 4));(FATrace (TSmbS 3))|]
;List.ofArray [|(FATrace (TAlt2S 10));(FATrace (TSeqS 8));(FATrace (TSmbS 5))|]
|];
   ToStateID   = 1;
}
;{ 
   FromStateID = 1;
   Symbol      = Dummy;
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSmbE 3));(FATrace (TSeqE 4));(FATrace (TAlt1E 9))|]
|];
   ToStateID   = 5;
}
;{ 
   FromStateID = 2;
   Symbol      = (DSymbol 4);
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSmbE 5));(FATrace (TSmbS 6))|]
|];
   ToStateID   = 3;
}
;{ 
   FromStateID = 3;
   Symbol      = (DSymbol 3);
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSmbE 6));(FATrace (TSmbS 7))|]
|];
   ToStateID   = 4;
}
;{ 
   FromStateID = 4;
   Symbol      = Dummy;
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSmbE 7));(FATrace (TSeqE 8));(FATrace (TAlt2E 10))|]
|];
   ToStateID   = 6;
}
|];
}
)|]

let private gotoSet = 
    Set.ofArray [|((0, 0, 1), set [(0, 1)]);((0, 0, 2), set [(1, 1); (2, 2)]);((0, 0, 3), set [(2, 1)]);((1, 0, 2), set [(1, 1); (2, 2)]);((1, 0, 3), set [(2, 1)]);((2, 0, 2), set [(2, 2)]);((2, 0, 3), set [(2, 1)]);((2, 2, 4), set [(2, 3)]);((2, 3, 3), set [(2, 4)])|]
    |> dict
let tables = { gotoSet = gotoSet; automataDict = autumataDict }

