//this tables was generated by RACC
//source grammar:..\Tests\RACC\test_alt\\test_alt.yrd
//date:12/17/2010 6:48:53 PM

#light "off"
module Yard.Generators.RACCGenerator.Tables

open Yard.Generators.RACCGenerator

let autumataDict = 
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
   DIDToStateMap = dict [|(0,(State 0));(1,DummyState)|];
   DStartState   = 0;
   DFinaleStates = Set.ofArray [|0|];
   DRules        = Set.ofArray [|{ 
   FromStateID = 0;
   Symbol      = (DSymbol "MINUS");
   Label       = Set.ofArray [|
 List.ofArray [|(FATrace (TSeqS 8));(FATrace (TClsS 1));(FATrace (TAlt1S 6));(FATrace (TSeqS 3));(FATrace (TSmbS 2))|]
;List.ofArray [|(FATrace (TSeqS 8));(FATrace (TClsS 1));(FATrace (TAlt2S 7));(FATrace (TSeqS 5));(FATrace (TSmbS 4))|]
;List.ofArray [|(FATrace (TSeqS 8));(FATrace (TClsS 1));(FATrace (TClsE 1));(FATrace (TSeqE 8))|]
;List.ofArray [|(FATrace (TSmbE 2));(FATrace (TSeqE 3));(FATrace (TAlt1E 6));(FATrace (TAlt1S 6));(FATrace (TSeqS 3));(FATrace (TSmbS 2))|]
;List.ofArray [|(FATrace (TSmbE 2));(FATrace (TSeqE 3));(FATrace (TAlt1E 6));(FATrace (TAlt2S 7));(FATrace (TSeqS 5));(FATrace (TSmbS 4))|]
;List.ofArray [|(FATrace (TSmbE 2));(FATrace (TSeqE 3));(FATrace (TAlt1E 6));(FATrace (TClsE 1));(FATrace (TSeqE 8))|]
;List.ofArray [|(FATrace (TSmbE 4));(FATrace (TSeqE 5));(FATrace (TAlt2E 7));(FATrace (TAlt1S 6));(FATrace (TSeqS 3));(FATrace (TSmbS 2))|]
;List.ofArray [|(FATrace (TSmbE 4));(FATrace (TSeqE 5));(FATrace (TAlt2E 7));(FATrace (TAlt2S 7));(FATrace (TSeqS 5));(FATrace (TSmbS 4))|]
;List.ofArray [|(FATrace (TSmbE 4));(FATrace (TSeqE 5));(FATrace (TAlt2E 7));(FATrace (TClsE 1));(FATrace (TSeqE 8))|]
|];
   ToStateID   = 0;
}
;{ 
   FromStateID = 0;
   Symbol      = (DSymbol "PLUS");
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSeqS 8));(FATrace (TClsS 1));(FATrace (TAlt1S 6));(FATrace (TSeqS 3));(FATrace (TSmbS 2))|]
;List.ofArray [|(FATrace (TSeqS 8));(FATrace (TClsS 1));(FATrace (TAlt2S 7));(FATrace (TSeqS 5));(FATrace (TSmbS 4))|]
;List.ofArray [|(FATrace (TSeqS 8));(FATrace (TClsS 1));(FATrace (TClsE 1));(FATrace (TSeqE 8))|]
;List.ofArray [|(FATrace (TSmbE 2));(FATrace (TSeqE 3));(FATrace (TAlt1E 6));(FATrace (TAlt1S 6));(FATrace (TSeqS 3));(FATrace (TSmbS 2))|]
;List.ofArray [|(FATrace (TSmbE 2));(FATrace (TSeqE 3));(FATrace (TAlt1E 6));(FATrace (TAlt2S 7));(FATrace (TSeqS 5));(FATrace (TSmbS 4))|]
;List.ofArray [|(FATrace (TSmbE 2));(FATrace (TSeqE 3));(FATrace (TAlt1E 6));(FATrace (TClsE 1));(FATrace (TSeqE 8))|]
;List.ofArray [|(FATrace (TSmbE 4));(FATrace (TSeqE 5));(FATrace (TAlt2E 7));(FATrace (TAlt1S 6));(FATrace (TSeqS 3));(FATrace (TSmbS 2))|]
;List.ofArray [|(FATrace (TSmbE 4));(FATrace (TSeqE 5));(FATrace (TAlt2E 7));(FATrace (TAlt2S 7));(FATrace (TSeqS 5));(FATrace (TSmbS 4))|]
;List.ofArray [|(FATrace (TSmbE 4));(FATrace (TSeqE 5));(FATrace (TAlt2E 7));(FATrace (TClsE 1));(FATrace (TSeqE 8))|]
|];
   ToStateID   = 0;
}
;{ 
   FromStateID = 0;
   Symbol      = Dummy;
   Label       = Set.ofArray [|List.ofArray [|(FATrace (TSeqS 8));(FATrace (TClsS 1));(FATrace (TAlt1S 6));(FATrace (TSeqS 3));(FATrace (TSmbS 2))|]
;List.ofArray [|(FATrace (TSeqS 8));(FATrace (TClsS 1));(FATrace (TAlt2S 7));(FATrace (TSeqS 5));(FATrace (TSmbS 4))|]
;List.ofArray [|(FATrace (TSeqS 8));(FATrace (TClsS 1));(FATrace (TClsE 1));(FATrace (TSeqE 8))|]
;List.ofArray [|(FATrace (TSmbE 2));(FATrace (TSeqE 3));(FATrace (TAlt1E 6));(FATrace (TAlt1S 6));(FATrace (TSeqS 3));(FATrace (TSmbS 2))|]
;List.ofArray [|(FATrace (TSmbE 2));(FATrace (TSeqE 3));(FATrace (TAlt1E 6));(FATrace (TAlt2S 7));(FATrace (TSeqS 5));(FATrace (TSmbS 4))|]
;List.ofArray [|(FATrace (TSmbE 2));(FATrace (TSeqE 3));(FATrace (TAlt1E 6));(FATrace (TClsE 1));(FATrace (TSeqE 8))|]
;List.ofArray [|(FATrace (TSmbE 4));(FATrace (TSeqE 5));(FATrace (TAlt2E 7));(FATrace (TAlt1S 6));(FATrace (TSeqS 3));(FATrace (TSmbS 2))|]
;List.ofArray [|(FATrace (TSmbE 4));(FATrace (TSeqE 5));(FATrace (TAlt2E 7));(FATrace (TAlt2S 7));(FATrace (TSeqS 5));(FATrace (TSmbS 4))|]
;List.ofArray [|(FATrace (TSmbE 4));(FATrace (TSeqE 5));(FATrace (TAlt2E 7));(FATrace (TClsE 1));(FATrace (TSeqE 8))|]
|];
   ToStateID   = 1;
}
|];
}
)|]

let gotoSet = 
    Set.ofArray [|(-1144264172,Set.ofArray [|("s",0)|]);(-1239003080,Set.ofArray [|("raccStart",2)|]);(-1239003111,Set.ofArray [|("s",1)|]);(-635149922,Set.ofArray [|("raccStart",1)|]);(-946926030,Set.ofArray [|("s",0)|]);(1723491585,Set.ofArray [|("s",0)|]);(1800920844,Set.ofArray [|("s",1)|]);(452886823,Set.ofArray [|("s",0)|])|]
    |> dict
