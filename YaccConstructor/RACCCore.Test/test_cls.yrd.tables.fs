//this tables was generated by RACC
//source grammar:..\Tests\RACC\test_cls\test_cls.yrd
//date:3/18/2011 15:27:51

#light "off"
module Yard.Generators.RACCGenerator.Tables_Cls

open Yard.Generators.RACCGenerator

let private autumataDict = 
dict [|("raccStart",{ 
   DIDToStateMap = dict [|(0,(State 0));(1,(State 1));(2,DummyState)|];
   DStartState   = 0;
   DFinaleStates = Set.ofArray [|1|];
   DRules        = Set.ofArray [|{ 
   FromStateID = 0;
   Symbol      = (DSymbol "s");
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
);("s",{ 
   DIDToStateMap = dict [|(0,(State 0));(1,(State 1));(2,DummyState);(3,DummyState)|];
   DStartState   = 1;
   DFinaleStates = Set.ofArray [|0;1|];
   DRules        = Set.ofArray [|{ 
   FromStateID = 0;
   Symbol      = (DSymbol "MULT");
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSmbE 2));(FATrace (TSeqE 3));(FATrace (TClsE 1));(FATrace (TSeqE 4))|]
;List.ofArray [|(FATrace (TSmbE 2));(FATrace (TSeqE 3));(FATrace (TSeqS 3));(FATrace (TSmbS 2))|]
|];
   ToStateID   = 0;
}
;{ 
   FromStateID = 0;
   Symbol      = Dummy;
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSmbE 2));(FATrace (TSeqE 3));(FATrace (TClsE 1));(FATrace (TSeqE 4))|]
;List.ofArray [|(FATrace (TSmbE 2));(FATrace (TSeqE 3));(FATrace (TSeqS 3));(FATrace (TSmbS 2))|]
|];
   ToStateID   = 2;
}
;{ 
   FromStateID = 1;
   Symbol      = (DSymbol "MULT");
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSeqS 4));(FATrace (TClsS 1));(FATrace (TClsE 1));(FATrace (TSeqE 4))|]
;List.ofArray [|(FATrace (TSeqS 4));(FATrace (TClsS 1));(FATrace (TSeqS 3));(FATrace (TSmbS 2))|]
|];
   ToStateID   = 0;
}
;{ 
   FromStateID = 1;
   Symbol      = Dummy;
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSeqS 4));(FATrace (TClsS 1));(FATrace (TClsE 1));(FATrace (TSeqE 4))|]
;List.ofArray [|(FATrace (TSeqS 4));(FATrace (TClsS 1));(FATrace (TSeqS 3));(FATrace (TSmbS 2))|]
|];
   ToStateID   = 3;
}
|];
}
)|]

let private gotoSet = 
    Set.ofArray [|(("raccStart",0,"Dummy"),Set.ofArray [|("s",2)|]);(("raccStart",0,"MULT"),Set.ofArray [|("s",0)|]);(("raccStart",0,"s"),Set.ofArray [|("raccStart",1)|]);(("raccStart",1,"Dummy"),Set.ofArray [|("raccStart",2)|]);(("s",0,"Dummy"),Set.ofArray [|("s",2)|]);(("s",0,"MULT"),Set.ofArray [|("s",0)|]);(("s",1,"Dummy"),Set.ofArray [|("s",3)|]);(("s",1,"MULT"),Set.ofArray [|("s",0)|])|]
    |> dict
let tables = { gotoSet = gotoSet; automataDict = autumataDict }

