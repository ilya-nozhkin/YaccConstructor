//this tables was generated by RACC
//source grammar:..\Tests\RACC\test_summator_1\test_summator_1.yrd
//date:3/18/2011 15:27:58

#light "off"
module Yard.Generators.RACCGenerator.Tables_Summator_1

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
   DIDToStateMap = dict [|(0,(State 0));(1,(State 1));(2,DummyState)|];
   DStartState   = 0;
   DFinaleStates = Set.ofArray [|1|];
   DRules        = Set.ofArray [|{ 
   FromStateID = 0;
   Symbol      = (DSymbol "e");
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
);("e",{ 
   DIDToStateMap = dict [|(0,(State 0));(1,(State 1));(2,(State 2));(3,(State 3));(4,(State 4));(5,DummyState);(6,DummyState)|];
   DStartState   = 0;
   DFinaleStates = Set.ofArray [|1;4|];
   DRules        = Set.ofArray [|{ 
   FromStateID = 0;
   Symbol      = (DSymbol "NUMBER");
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TAlt1S 9));(FATrace (TSeqS 4));(FATrace (TSmbS 3))|]
;List.ofArray [|(FATrace (TAlt2S 10));(FATrace (TSeqS 8));(FATrace (TSmbS 5))|]
|];
   ToStateID   = 1;
}
;{ 
   FromStateID = 0;
   Symbol      = (DSymbol "e");
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TAlt1S 9));(FATrace (TSeqS 4));(FATrace (TSmbS 3))|]
;List.ofArray [|(FATrace (TAlt2S 10));(FATrace (TSeqS 8));(FATrace (TSmbS 5))|]
|];
   ToStateID   = 2;
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
   Symbol      = (DSymbol "PLUS");
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSmbE 5));(FATrace (TSmbS 6))|]
|];
   ToStateID   = 3;
}
;{ 
   FromStateID = 3;
   Symbol      = (DSymbol "NUMBER");
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
    Set.ofArray [|(("e",0,"NUMBER"),Set.ofArray [|("e",1)|]);(("e",0,"e"),Set.ofArray [|("e",2)|]);(("e",1,"Dummy"),Set.ofArray [|("e",5)|]);(("e",2,"PLUS"),Set.ofArray [|("e",3)|]);(("e",3,"NUMBER"),Set.ofArray [|("e",4)|]);(("e",4,"Dummy"),Set.ofArray [|("e",6)|]);(("raccStart",0,"NUMBER"),Set.ofArray [|("e",1)|]);(("raccStart",0,"e"),Set.ofArray [|("e",2);("s",1)|]);(("raccStart",0,"s"),Set.ofArray [|("raccStart",1)|]);(("raccStart",1,"Dummy"),Set.ofArray [|("raccStart",2)|]);(("s",0,"NUMBER"),Set.ofArray [|("e",1)|]);(("s",0,"e"),Set.ofArray [|("e",2);("s",1)|]);(("s",1,"Dummy"),Set.ofArray [|("s",2)|])|]
    |> dict
let tables = { gotoSet = gotoSet; automataDict = autumataDict }

