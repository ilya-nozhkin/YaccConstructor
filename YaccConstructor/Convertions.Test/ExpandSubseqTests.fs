﻿//  ExpandInnerAltTests.fs contains unuit test for ExpandInnerAlt conversions
//
//  Copyright 2012 Semen Grigorev <rsdpisuy@gmail.com>
//
//  This file is part of YaccConctructor.
//
//  YaccConstructor is free software:you can redistribute it and/or modify
//  it under the terms of the GNU General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  This program is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU General Public License for more details.
//
//  You should have received a copy of the GNU General Public License
//  along with this program.  If not, see <http://www.gnu.org/licenses/>.


module ExpandSubseqTests

open Yard.Core
open Yard.Core.IL
open Yard.Core.IL.Production
open Yard.Core.IL.Definition
open Convertions.TransformAux
open NUnit.Framework
open ConvertionsTests

[<TestFixture>]
type ``Expand subseq tests`` () =
    let basePath = System.IO.Path.Combine(convertionTestPath, "ExpandSubseq")
    let fe = getFrontend("YardFrontend")
    let conversion = "ExpandBrackets"
    [<Test>]
    member test.``Subseq 1`` () =
        Namer.resetRuleEnumerator()
        let loadIL = fe.ParseGrammar (System.IO.Path.Combine(basePath,"subseq1.yrd"))
        let result = ConvertionsManager.ApplyConvertion conversion loadIL
        let expected = 
            {
                info = {fileName = ""}
                head = None
                grammar =
                     [{
                            name = "s"
                            args = []
                            body = PSeq([{dummyRule with rule = PRef (("yard_exp_brackets_1", (0, 0)),None)}],None, None)
                            _public = true
                            metaArgs = []
                         };
                         {
                            name = "yard_exp_brackets_1"
                            args = []
                            body =
                             (PSeq ([{dummyRule with rule = PRef (("x", (7, 8)),None)}
                                    ;{dummyRule with rule = PRef (("y", (9, 10)),None)}],None,None))
                            _public = false
                            metaArgs = []}]
                foot = None
                options = Map.empty
            }

        expected |> treeDump.Generate |> string |> printfn "%s"
        printfn "%s" "************************"
        result |> treeDump.Generate |> string |> printfn "%s"
        Assert.IsTrue(ILComparators.GrammarEqualsWithoutLineNumbers expected.grammar result.grammar)

    [<Test>]
    member test.``Subseq 2`` () =
        Namer.resetRuleEnumerator()
        let loadIL = fe.ParseGrammar (System.IO.Path.Combine(basePath,"subseq2.yrd"))
        let result = ConvertionsManager.ApplyConvertion conversion loadIL
        let expected = 
            {
                info = {fileName = ""}
                head = None
                grammar =
                     [{
                            name = "s"
                            args = []
                            body =
                                PSeq([{dummyRule with rule = PRef (("yard_exp_brackets_1", (0, 0)),None)}
                                     ;{dummyRule with rule = PRef (("yard_exp_brackets_2", (0, 0)),None)}],None, None)                        
                            _public = true
                            metaArgs = []
                         };
                         {
                            name = "yard_exp_brackets_1"
                            args = []
                            body =
                             PSeq ([{dummyRule with rule = PRef (("x", (7, 8)),None)}
                                   ;{dummyRule with rule = PRef (("y", (9, 10)),None)}],None,None)
                            _public = false
                            metaArgs = []
                         };
                         {
                            name = "yard_exp_brackets_2"
                            args = []
                            body =
                             (PSeq ([{dummyRule with rule = PRef (("n", (7, 8)),None)}
                                    ;{dummyRule with rule = PRef (("m", (9, 10)),None)}],None,None))
                            _public = false
                            metaArgs = []}]
                foot = None
                options = Map.empty
            }

        expected |> treeDump.Generate |> string |> printfn "%s"
        printfn "%s" "************************"
        result |> treeDump.Generate |> string |> printfn "%s"
        Assert.IsTrue(ILComparators.GrammarEqualsWithoutLineNumbers expected.grammar result.grammar)
    
    [<Test>]
    member test.``Inner subseq`` () =
        Namer.resetRuleEnumerator()
        let loadIL = fe.ParseGrammar (System.IO.Path.Combine(basePath,"innerSubseq.yrd"))
        let result = ConvertionsManager.ApplyConvertion conversion loadIL
        let expected = 
            {
                info = {fileName = ""}
                head = None
                grammar =
                     [{
                            name = "s"
                            args = []
                            body = PSeq([{dummyRule with rule = PRef (("yard_exp_brackets_1", (0, 0)),None)}],None, None)
                            _public = true
                            metaArgs = []
                         };
                         {
                            name = "yard_exp_brackets_1"
                            args = []
                            body =
                             PSeq ([{dummyRule with rule = PRef (("x", (7, 8)),None)}
                                   ; {dummyRule with rule = PRef (("yard_exp_brackets_2", (9, 10)),None)}
                                   ; {dummyRule with rule = PRef (("y", (7, 8)),None)}],None,None)
                            _public = false
                            metaArgs = []
                         };
                         {
                            name = "yard_exp_brackets_2"
                            args = []
                            body =
                             PSeq ([{dummyRule with rule = PRef (("n", (7, 8)),None)}
                                   ;{dummyRule with rule = PRef (("m", (9, 10)),None)}],None,None)
                            _public = false
                            metaArgs = []}]
                foot = None
                options = Map.empty
            }

        expected |> treeDump.Generate |> string |> printfn "%s"
        printfn "%s" "************************"
        result |> treeDump.Generate |> string |> printfn "%s"
        Assert.IsTrue(ILComparators.GrammarEqualsWithoutLineNumbers expected.grammar result.grammar)