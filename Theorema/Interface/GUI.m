(* Theorema 
    Copyright (C) 2010 The Theorema Group

    This file is part of Theorema 2.0
    
    Theorema 2.0 is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Theorema 2.0 is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program. If not, see <http://www.gnu.org/licenses/>.
*)

BeginPackage[ "Theorema`Interface`GUI`"];

Needs[ "Theorema`Common`"]
Needs[ "Theorema`Language`"]
Needs[ "Theorema`Provers`"]
Needs[ "Theorema`Interface`Language`"]

Begin[ "`Private`"]

closeTheoremaCommander[];

(* ::Section:: *)
(* initGUI *)


initGUI[] := 
	Module[{},
		(*
		   In $tmaBuiltins
		   o) nesting gives the nested structure for display
		   o) each entry has the form
		      {key, box display, default active for proving, default active for computation, default active for solving},
		      where "key" is the corresponding key used in activeComputation *)
        $tmaBuiltins = {
        	{"Sets", 
        		{"IsElement", RowBox[{"x","\[Element]","A"}], False, True, False},
        		{"SetEqual", RowBox[{"A","\[Equal]","B"}], False, True, False},
                {"SubsetEqual", RowBox[{"A","\[SubsetEqual]","B"}], False, True, False},
                {"SupersetEqual", RowBox[{"A","\[SupersetEqual]","B"}], False, True, False},
                {"Subset", RowBox[{"A","\[Subset]","B"}], False, True, False},
                {"Superset", RowBox[{"A","\[Superset]","B"}], False, True, False},
				{"Union", RowBox[{"A","\[Union]","B"}], False, True, False},
        		{"Intersection", RowBox[{"A","\[Intersection]","B"}], False, True, False},
                {"Difference", RowBox[{"A","\[Backslash]","B"}], False, True, False},
                {"SymmetricDifference", RowBox[{"A","\[EmptyUpTriangle]","B"}], False, True, False},
                {"CartesianProduct", RowBox[{"A","\[Cross]","B"}], False, True, False},
                {"Cardinality", RowBox[{"\[LeftBracketingBar]", "A", "\[RightBracketingBar]"}], False, True, False},
                {"PowerSet", RowBox[{"\[ScriptCapitalP]","[", "A", "]"}], False, True, False},
                {"AnElement", RowBox[{"\[AE]","[", "A", "]"}], False, True, False},
                {"UnionOf", RowBox[{"\[Union]",SubscriptBox["A","i"]}], False, True, False},
        		{"IntersectionOf", RowBox[{"\[Intersection]",SubscriptBox["A","i"]}], False, True, False},
                {"MaximumElementSet", RowBox[{"max","[", "A", "]"}], False, True, False},
                {"MinimumElementSet", RowBox[{"min","[", "A", "]"}], False, True, False},
                {"MaximumOf", RowBox[{"max",SubscriptBox["A","i"]}], False, True, False},
                {"MinimumOf", RowBox[{"min",SubscriptBox["A","i"]}], False, True, False},
                {"ArgMax", RowBox[{"argmax",SubscriptBox["A","i"]}], False, True, False},
                {"ArgMin", RowBox[{"argmin",SubscriptBox["A","i"]}], False, True, False},
                {"TheArgMax", RowBox[{"theargmax",SubscriptBox["A","i"]}], False, True, False},
                {"TheArgMin", RowBox[{"theargmin",SubscriptBox["A","i"]}], False, True, False}
        	},
        	{"Tuples",
        		{"Subscript", SubscriptBox[ "T", "i"], False, True, False},
                {"TupleEqual", RowBox[ {"T","\[Equal]","S"}], False, True, False},
                {"elemTuple", RowBox[ {"e",TagBox["\:22ff",Identity,SyntaxForm->"a+b"],"T"}], False, True, False},
        		{"Length", RowBox[{"\[LeftBracketingBar]", "T", "\[RightBracketingBar]"}], False, True, False},
                {"Insert", SubscriptBox[ "T",RowBox[{"e","\[Rule]","i"}]], False, True, False},
                {"Delete", SubscriptBox[ "T", RowBox[{RowBox[{"e", ",", "\[Ellipsis]"}], "\[LeftArrowBar]"}]], False, True, False},
                {"DeleteAt", SubscriptBox[ "T", RowBox[{"i", "\[LeftArrow]"}]], False, True, False},
        	    {"Replace", SubscriptBox[ "T", RowBox[{RowBox[{RowBox[{"e", ",", "\[Ellipsis]"}], "\[LeftArrowBar]", "newe"}], ",", "\[Ellipsis]"}]], False, True, False},
                {"ReplacePart", SubscriptBox[ "T", RowBox[{RowBox[{"i", "\[LeftArrow]", "e"}], ",", "\[Ellipsis]"}] ], False, True, False},
			    {"appendElem", RowBox[{"T", "\:293a", "e"}], False, True, False},
        		{"prependElem", RowBox[{"e", "\:293b", "T"}], False, True, False},
        		{"joinTuples", RowBox[{"T", "\:22c8", "S"}], False, True, False},
        		{"Max", RowBox[{"max","[","T","]"}], False, True, False},
        		{"Min", RowBox[{"min","[","T","]"}], False, True, False}
        	},
        	{"Arithmetic",
        		{"Plus", RowBox[{"A","+","B"}], False, True, False},
         		{"Minus", RowBox[{"-","A"}], False, True, False},
	       		{"Times", RowBox[{"A","*","B"}], False, True, False},
	       		{"MultInverse", SuperscriptBox[ "A", "-1"], False, True, False},
        		{"Power", SuperscriptBox[ "A", "B"], False, True, False},
        		{"Radical", RadicalBox[ "A", "B"], False, True, False},
        		{"Factorial", RowBox[ {"A", "!"}], False, True, False},
        		{"Equal", RowBox[{"A","=","B"}], False, True, False},
        		{"Less", RowBox[{"A","<","B"}], False, True, False},
        		{"LessEqual", RowBox[{"A","\[LessEqual]","B"}], False, True, False},
        		{"Greater", RowBox[{"A",">","B"}], False, True, False},
        		{"GreaterEqual", RowBox[{"A","\[GreaterEqual]","B"}], False, True, False},
        		{"AbsValue", RowBox[{"\[LeftBracketingBar]", "A", "\[RightBracketingBar]"}], False, True, False},
        		{"SumOf", RowBox[{"\[Sum]",SubscriptBox["A","i"]}], False, True, False},
        		{"ProductOf", RowBox[{"\[Product]",SubscriptBox["A","i"]}], False, True, False}
        	},
        	{"Logic", 
        		{"Not", RowBox[{"\[Not]","P"}], True, True, False},
        		{"And", RowBox[{"P", "\[And]","Q"}], True, True, False},
        		{"Or", RowBox[{"P", "\[Or]","Q"}], True, True, False},
        		{"Implies", RowBox[{"P", "\[Implies]","Q"}], True, True, False},
        		{"Iff", RowBox[{"P", "\[Equivalent]","Q"}], True, True, False},
        		{"Nand", RowBox[{"P", "\[Nand]","Q"}], True, True, False},
        		{"Nor", RowBox[{"P", "\[Nor]","Q"}], True, True, False},
        		{"Xor", RowBox[{"P", "\[Xor]","Q"}], True, True, False},
        		{"Xnor", RowBox[{"P", "\[Xnor]","Q"}], True, True, False},
        		{"Forall", RowBox[{"\[ForAll]","P"}], False, True, False},
        		{"Exists", RowBox[{"\[Exists]","P"}], False, True, False},
        		{"Equal", RowBox[{"A","=","B"}], True, True, False},
        		{"Let", UnderscriptBox["let",RowBox[{"A","=","\[Ellipsis]"}]], False, True, False},
        		{"Componentwise", RowBox[{"P", "@", "A"}], False, True, False},
        		{"Such", RowBox[{UnderscriptBox["\[CurlyEpsilon]","x"],"P"}], False, True, False},
        		{"SuchUnique", RowBox[{UnderscriptBox["the","x"],"P"}], False, True, False}
        	},
        	{"Domains",
        		{"isInteger", RowBox[{"isInteger","[","A","]"}], False, True, True},
        		{"isRational", RowBox[{"isRational","[","A","]"}], False, True, True},
        		{"isReal", RowBox[{"isReal","[","A","]"}], False, True, True},
        		{"isComplex", RowBox[{"isComplex","[","A","]"}], False, True, True},
        		{"isComplexP", RowBox[{"isComplexP","[","A","]"}], False, True, True},
        		{"isSet", RowBox[{"isSet","[","A","]"}], False, True, True},
        		{"isTuple", RowBox[{"isTuple","[","A","]"}], False, True, True},
        		{"IntegerQuotientRing", SubscriptBox["\[DoubleStruckCapitalZ]", "m"], False, True, True},
        		{"IntegerQuotientRingPM", SubsuperscriptBox["\[DoubleStruckCapitalZ]", "m", "\[PlusMinus]"], False, True, True},
        		{"IntegerInterval", RowBox[{"\[DoubleStruckCapitalZ]"}], False, True, True},
        		{"RationalInterval", RowBox[{"\[DoubleStruckCapitalQ]"}], False, True, True},
        		{"RealInterval", RowBox[{"\[DoubleStruckCapitalR]"}], False, True, True},
        		{"\[DoubleStruckCapitalC]", RowBox[{"\[DoubleStruckCapitalC]"}], False, True, True},
        		{"\[DoubleStruckCapitalC]P", SubscriptBox["\[DoubleStruckCapitalC]", "P"], False, True, True}
        	},
        	{"Programming",
        		{"CaseDistinction", RowBox[{"\[Piecewise]",GridBox[{{"A"},{"B"}}]}], False, True, False},
        		{"Module", RowBox[{"Module","[","\[Ellipsis]","]"}], False, True, False},
        		{"Do", RowBox[{"Do","[","\[Ellipsis]","]"}], False, True, False},
        		{"While", RowBox[{"While","[","\[Ellipsis]","]"}], False, True, False},
        		{"For", RowBox[{"For","[","\[Ellipsis]","]"}], False, True, False},
        		{"Which", RowBox[{"Which","[","\[Ellipsis]","]"}], False, True, False},
        		{"Switch", RowBox[{"Switch","[","\[Ellipsis]","]"}], False, True, False}
        	}
        };
        (* Init views in commander *)
        $tcActivitiesView = 1;
        $tcActionView = 1;
        (* Init status of opener views *)
        Scan[ ToExpression, Map[ "$builtinStructState$" <> # <> "=True"&, Map[ First, $tmaBuiltins]]];
        (*Scan[ ToExpression, Map[ "$tcSessMathOpener$" <> # <> "=True"&, Map[ First, allFormulae]]];*)
		$kbStruct = {};
		$ruleFilterKW = "";
		$kbFilterKW = "";
		$initLabel = "???";
		$labelSeparator = ",";
		$cellTagKeySeparator = ":";
		$traceUserDef = False;
		$TMAcomputationDemoMode = False;
		Clear[ kbSelectProve, kbSelectSolve];
		kbSelectProve[_] := False;
		kbSelectSolve[_] := False;
		$selectedProofGoal = {};
		$selectedProofKB = {};
		$selectedSearchDepth = 30;
		$maxSearchDepth = 200;
		$selectedSearchTime = 360;
		$maxSearchTime = 1000;
		initBuiltins[ {"prove", "compute", "solve"}];
		$selectedRuleSet = Hold[ basicTheoremaLanguageRules];
		$selectedStrategy = applyOnceAndLevelSaturation;
		Scan[ setRulesDefaults[ #[[1]]]&, $registeredRuleSets];
		$CtrlActive = 0;
		$ShiftActive = 0;
		$TMAactDecl = "";
		$proofTreeScale = 1;
		$replExistProof = 0;
		$numExistProofs = -1;
		$TmaLanguage = $Language;
	]

initBuiltins[ l_List] :=
    Module[ {bui},
        bui = Cases[ $tmaBuiltins, {_String, _, _Symbol, _Symbol, _Symbol}, Infinity];
        If[ MemberQ[ l, "prove"],
            Scan[ (buiActProve[#[[1]]] = #[[3]])&, bui]
        ];
        If[ MemberQ[ l, "compute"],
            Scan[ (buiActComputation[#[[1]]] = #[[4]])&, bui]
        ];
        If[ MemberQ[ l, "solve"],
            Scan[ (buiActSolve[#[[1]]] = #[[5]])&, bui]
        ];
    ]
initBuiltins[ args___] := unexpected[ initBuiltins, {args}]

setRulesDefaults[ Hold[ rs_]] :=
	Module[ {list},
		list = Cases[ rs, {_Symbol, _, _, _Integer, ___}, Infinity];
		Scan[
			ruleActive[ #[[1]]] = #[[2]];
    		ruleTextActive[ #[[1]]] = #[[3]];
    		rulePriority[ #[[1]]] = #[[4]];&, list];		
	]

initGUI[];


(* ::Section:: *)
(* theoremaCommander *)

openTheoremaGUI[ ] := openTheoremaCommander[]
openTheoremaGUI[ args___] := unexpected[ openTheoremaGUI, {args}]


(*
	The style sheet defines Deployed->False unlike in usual palettes. This is necessary in order make Button[ ..., Active->False] or
	Hyperlink[ ..., Active->False] work. Deployed->True would force all links and buttons to be active.
	We have to keep an eye on that whether Deployed->False has other negative effects on the window's behaviour.
*)
openTheoremaCommander[ ] /; $Notebooks :=
    Module[ {},
        $TMAcommander = CreatePalette[ Dynamic[
        	Refresh[
        	activitiesView[
        		(* activities buttons *)
        		{translate["tcSessionTabLabel"], translate["tcProveTabLabel"], translate["tcComputeTabLabel"], translate["tcSolveTabLabel"], 
        			translate["tcInformTabLabel"]},
        		(* for each activity the respective action buttons *)
        		{
        			(* session *){translate["tcSessTabComposeTabLabel"], translate["tcSessTabInspectTabLabel"], translate["tcSessTabArchTabLabel"]},
        			(* prove *)  {translate["tcProveTabGoalTabLabel"], translate["tcProveTabKBTabLabel"], translate["tcProveTabBuiltinTabLabel"],
        				translate["tcProveTabProverTabLabel"], translate["tcProveTabSubmitTabLabel"], translate["tcProveTabInspectTabLabel"]},
        			(* compute *){translate["tcComputeTabNewTabLabel"], translate["tcComputeTabKBTabLabel"], translate["tcComputeTabBuiltinTabLabel"], translate["tcComputeTabSetupTabLabel"]},
        			(* solve *)  {translate["tcSolveTabKBTabLabel"], translate["tcSolveTabBuiltinTabLabel"], translate["tcSolveTabSetupTabLabel"]},
        			(* inform *)  {translate["tcInformTabLicenseTabLabel"], translate["tcInformTabAboutTabLabel"], translate["tcInformTabSetupTabLabel"]},
        			(* setup *)  { }
        		},
        		(* for each activity and each action the respective content *)
        		{
        			(* session *){sessionCompose[], sessionInspect[], sessionArchive[]},
        			(* prove *)  {Dynamic[ Refresh[ displaySelectedGoal[], UpdateInterval -> 2]],
        				Dynamic[ Refresh[ displayKBBrowser[ "prove"], TrackedSymbols :> {$kbFilterKW, $tcKBBrowseSelection, $kbStruct, kbSelectProve}]],
        				Dynamic[ Refresh[ displayBuiltinBrowser[ "prove"], TrackedSymbols :> {buiActProve}]],
        				Dynamic[ Refresh[ selectProver[], TrackedSymbols :> {$selectedRuleSet, $selectedStrategy, $ruleFilterKW}]],
        				Dynamic[ Refresh[ submitProveTask[], TrackedSymbols :> {$selectedProofGoal, $selectedProofKB, $selectedSearchDepth, $selectedSearchTime}]],
        				Dynamic[ Refresh[ proofNavigation[ $TMAproofTree], TrackedSymbols :> {$TMAproofTree, $TMAproofSearchRunning, $TMAproofNotebook, ruleTextActive, $proofTreeScale, $selectedProofStep}]]},
        			(* compute *){compNew[],
        				Dynamic[ Refresh[ displayKBBrowser[ "compute"], TrackedSymbols :> {$kbFilterKW, $kbStruct, $tcKBBrowseSelection}]],
        				displayBuiltinBrowser[ "compute"](*Dynamic[ Refresh[ displayBuiltinBrowser[ "compute"], TrackedSymbols :> {buiActComputation}]]*),
        				compSetup[]},
        			(* solve *)  {Dynamic[Refresh[ displayKBBrowser[ "solve"], TrackedSymbols :> {$kbFilterKW, $kbStruct, $tcKBBrowseSelection}]],
        				Dynamic[ Refresh[ displayBuiltinBrowser[ "solve"], TrackedSymbols :> {buiActSolve}]],
        				solveSetup[]},
        			(* inform *)  {licenseTab[], aboutTab[], setPreferences[]}
        		}
        	], TrackedSymbols :> {$TmaLanguage}]],
        	StyleDefinitions -> makeColoredStylesheet[ "GUI"],
        	WindowTitle -> translate["Theorema Commander"],
        	WindowFloating -> Automatic,
        	WindowElements -> {"StatusArea", "MagnificationPopUp"}]
    ]
openTheoremaCommander[ args___] := unexpected[ openTheoremaCommander, {args}]

emptyPane[ text_String:""] := Pane[ text, Alignment -> {Center, Center}]
emptyPane[ text_String:"", size_] := Pane[ text, size, Alignment -> {Left, Top}]
emptyPane[ args___] := unexpected[ emptyPane, {args}]

getTheoremaCommander[ ] := $TMAcommander
getTheoremaCommander[ args___] := unexpected[ getTheoremaCommander, {args}]

closeTheoremaCommander[ ] := 
	If[ ValueQ[ $TMAcommander],
		NotebookClose[ $TMAcommander];
		Clear[ $TMAcommander];
	]
closeTheoremaCommander[ args___] := unexpected[ closeTheoremaCommander, {args}]

activitiesView[ activitiesLab:{__String}, actionLabs:{{___String}..}, views:{{__}..}] :=
        Dynamic[
        Grid[{{
        	Button[ Style[ "\:2328", Large, FontColor -> TMAcolor[0]], virtualKeyboard[],
        		Background -> TMAcolor[1], Appearance -> Frameless, FrameMargins -> 0, ContentPadding -> False], 
        	Row[ MapIndexed[
                Button[ Mouseover[ Style[ #1, "TabLabel2"], Style[ #1, "TabLabel2Over"]], $tcActionView = #2[[1]],
                	Background -> If[ $tcActionView === #2[[1]], TMAcolor[0], TMAcolor[5]]] &,
                actionLabs[[ $tcActivitiesView]]]]},
        	{Column[ MapIndexed[
                Button[ Mouseover[ Style[ #1, "TabLabel1"], Style[ #1, "TabLabel1Over"]], ($tcActionView = 1; $tcActivitiesView = #2[[1]]),
                	Background -> If[ $tcActivitiesView === #2[[1]], TMAcolor[0], TMAcolor[5]]] &,
                activitiesLab], Center, Spacings -> {0, {0, {2 -> 1, -2 -> 5}}}],
                Pane[ views[[$tcActivitiesView, $tcActionView]], {400, 600}, ImageSizeAction -> "Scrollable", Scrollbars -> Automatic,
                    ImageMargins -> 0, FrameMargins -> 10]}},
            Alignment -> {{Center, Left}, {Center, Top}}, Spacings -> {0, 0}, Background -> TMAcolor[1]]
        ]
activitiesView[ args___] := unexpected[ activitiesView, {args}]

(* ::Subsubsection:: *)
(* virtualKeyboard *)


virtualKeyboard[ ] /; $Notebooks :=
        CreatePalette[ Dynamic[ 
        	Row[{
        		Grid[ Table[ formButton[ i, j, FromDigits[ {$CtrlActive, $ShiftActive}, 2]], {i, 2}, {j, 5}], Spacings -> {0.2, 0.25}],
        		Column[{
        			Grid[ Table[ charButton[ i, j, FromDigits[ {$CtrlActive, $ShiftActive}, 2]], {i, 3}, {j, 11}], Spacings -> {0.2, 0.25}],
        			Row[ {Button[ "\[ShiftKey]", $ShiftActive = Mod[ $ShiftActive+1, 2], BaseStyle -> If[ $ShiftActive === 1, "KBButtonPress", "KBButton"], ImageSize -> {61, 30}],
        				Button[ "\[ControlKey]", $CtrlActive = Mod[ $CtrlActive+1, 2], BaseStyle -> If[ $CtrlActive === 1, "KBButtonPress", "KBButton"], ImageSize -> {61, 30}],
        				makeVkbButton[ "\[SpaceKey]", " ", ImageSize -> {80, 30}],
        				Button[ "\[ControlKey]", $CtrlActive = Mod[ $CtrlActive+1, 2], BaseStyle -> If[ $CtrlActive === 1, "KBButtonPress", "KBButton"], ImageSize -> {61, 30}],
        				Button[ "\[ShiftKey]", $ShiftActive = Mod[ $ShiftActive+1, 2], BaseStyle -> If[ $ShiftActive === 1, "KBButtonPress", "KBButton"], ImageSize -> {61, 30}]
        				}, Spacer[1]]
        			}],
        		Grid[ Table[ numButton[ i, j, FromDigits[ {$CtrlActive, $ShiftActive}, 2]], {i, 4}, {j, 4}], Spacings -> {0.2, 0.25}],
        		Grid[ Table[ symButton[ i, j, FromDigits[ {$CtrlActive, $ShiftActive}, 2]], {i, 4}, {j, 4}], Spacings -> {0.2, 0.25}]
        }, Spacer[5]]],
        StyleDefinitions -> FileNameJoin[{"Theorema", "Keyboard.nb"}],
        WindowTitle -> translate["Virtual Keyboard"]]
virtualKeyboard[ args___] := unexpected[ virtualKeyboard, {args}]

formButton[ i_Integer, j_Integer, code_Integer] := vkbButton[ i, j, code, $formBlockMap, ImageSize -> {80, 60}]
formButton[ args___] := unexpected[ formButton, {args}]

charButton[ i_Integer, j_Integer, code_Integer] := vkbButton[ i, j, code, $charBlockMap]
charButton[ args___] := unexpected[ charButton, {args}]

numButton[ i_Integer, j_Integer, code_Integer] := vkbButton[ i, j, code, $numBlockMap]
numButton[ args___] := unexpected[ numButton, {args}]

symButton[ i_Integer, j_Integer, code_Integer] := vkbButton[ i, j, code, $symBlockMap]
symButton[ args___] := unexpected[ symButton, {args}]

vkbButton[ i_Integer, j_Integer, code_Integer, map_List, opts___?OptionQ] :=
	Module[ {key = Replace[ {i,j}, map]},
    	Apply[ makeVkbButton[ ##, opts]&, Part[ key, code+1]]
	]
vkbButton[ args___] := unexpected[ vkbButton, {args}]

Options[ makeVkbButton] = {ImageSize -> {30, 30}};
SetAttributes[ makeVkbButton, HoldAll]

makeVkbButton[ opts___?OptionQ] := 
	Module[ {size},
		{size} = {ImageSize} /. {opts} /. Options[ makeVkbButton];
		Pane[ "", size]
	]
makeVkbButton[ "EnterKey", opts___?OptionQ] :=
	makeVkbButton[ "\[ReturnIndicator]", 
		buttonOp -> FrontEndExecute[ SelectionMove[ InputNotebook[], All, Cell]; SelectionEvaluate[ InputNotebook[]]],
		opts]
    
makeVkbButton[ "DeleteKey", opts___?OptionQ] := 
	makeVkbButton[ "\[DeleteKey]", 
		buttonOp -> FrontEndExecute[ SelectionMove[ InputNotebook[], Previous, Character]; SelectionMove[ InputNotebook[], All, Character]; NotebookDelete[ InputNotebook[]]],
		opts]

makeVkbButton[ label_, buttonOp -> buttonFun_, opts___?OptionQ] :=
    DynamicModule[ {bs = "KBButton", size},
    	{size} = {ImageSize} /. {opts} /. Options[ makeVkbButton];
    	EventHandler[
    		Annotation[
    			Button[ Pane[ label, ImageSizeAction -> "ShrinkToFit", ImageSize -> size-2],
    				buttonFun,
    				BaseStyle -> Dynamic[ If[ MouseAnnotation[] === label && bs === "KBButton",
    					"KBButtonOver",
    					bs]],
    				ImageSize -> size
    				],
    			label, "Mouse"],
    		{"MouseDown" :> (bs = "KBButtonPress";),
    		 "MouseUp" :> (bs = "KBButton";)},
    		PassEventsDown -> True
    	]
    ]

makeVkbButton[ label_, opts___?OptionQ] := makeVkbButton[ label, label, opts]

makeVkbButton[ label_, insert_, opts___?OptionQ] :=
	makeVkbButton[ label, 
		buttonOp -> FrontEndExecute[ NotebookApply[ InputNotebook[], insert, Placeholder]],
		opts]
    
makeVkbButton[ label_, insert_, help_, alias_, opts___?OptionQ] :=
    DynamicModule[ {bs = "KBButton", size},
    	{size} = {ImageSize} /. {opts} /. Options[ makeVkbButton];
    	EventHandler[
    		Tooltip[ Annotation[
    			Button[ Pane[ label, ImageSizeAction -> "ShrinkToFit", ImageSize -> size-2],
    				FrontEndExecute[ NotebookApply[ InputNotebook[], insert, Placeholder]],
    				BaseStyle -> Dynamic[ If[ MouseAnnotation[] === label && bs === "KBButton",
    					"KBButtonOver",
    					bs]],
    				ImageSize -> size
    				],
    			label, "Mouse"],
    		"\[EscapeKey]"<> alias <>"\[EscapeKey]", TooltipDelay -> 0.5],
    		{"MouseDown" :> (bs = "KBButtonPress";),
    		 "MouseUp" :> (bs = "KBButton";)},
    		PassEventsDown -> True
    	]
    ]
makeVkbButton[ args___] := unexpected[ makeVkbButton, {args}]

$formBlockMap = {
	{1, 1} -> { langButtonData[ "FORALL1"], {}, {}, {}},
	{1, 2} -> { langButtonData[ "FORALL2"], {}, {}, {}},
	{1, 3} -> { langButtonData[ "AND2"], {}, {}, {}},
	{1, 4} -> { langButtonData[ "IMPL2"], {}, {}, {}},
	{1, 5} -> { langButtonData[ "EQDEF"], {}, {}, {}},
	{2, 1} -> { langButtonData[ "EXISTS1"], {}, {}, {}},
	{2, 2} -> { langButtonData[ "EXISTS2"], {}, {}, {}},
	{2, 3} -> { langButtonData[ "OR2"], {}, {}, {}},
	{2, 4} -> { langButtonData[ "EQUIV2"], {}, {}, {}},
	{2, 5} -> { langButtonData[ "EQUIVDEF"], {}, {}, {}},
	{i_, j_} -> Table[ {}, {4}]
};

$charBlockMap = {
	{1, 1} -> { {"\[EscapeKey]", "\[AliasDelimiter]"}, {"\[EscapeKey]", "\[AliasDelimiter]"}, {"\[EscapeKey]", "\[AliasDelimiter]"}, {"\[EscapeKey]", "\[AliasDelimiter]"}},
	{1, 2} -> { {"q"}, {"Q"}, {}, {}},
	{1, 3} -> { {"w"}, {"W"}, {}, {}},
	{1, 4} -> { {"e"}, {"E"}, {}, {}},
	{1, 5} -> { {"r"}, {"R"}, {}, {}},
	{1, 6} -> { {"t"}, {"T"}, {}, {}},
	{1, 7} -> { {"y"}, {"Y"}, {}, {}},
	{1, 8} -> { {"u"}, {"U"}, {}, {}},
	{1, 9} -> { {"i"}, {"I"}, {}, {}},
	{1, 10} -> { {"o"}, {"O"}, {}, {}},
	{1, 11} -> { {"p"}, {"P"}, {}, {}},
	{2, 2} -> { {"a"}, {"A"}, {}, {}},
	{2, 3} -> { {"s"}, {"S"}, {}, {}},
	{2, 4} -> { {"d"}, {"D"}, {}, {}},
	{2, 5} -> { {"f"}, {"F"}, {}, {}},
	{2, 6} -> { {"g"}, {"G"}, {}, {}},
	{2, 7} -> { {"h"}, {"H"}, {}, {}},
	{2, 8} -> { {"j"}, {"J"}, {}, {}},
	{2, 9} -> { {"k"}, {"K"}, {}, {}},
	{2, 10} -> { {"l"}, {"L"}, {}, {}},
	{2, 11} -> { {"EnterKey"}, {"EnterKey"}, {"EnterKey"}, {"EnterKey"}},
	{3, 2} -> { {"z"}, {"Z"}, {}, {}},
	{3, 3} -> { {"x"}, {"X"}, {}, {}},
	{3, 4} -> { {"c"}, {"C"}, {}, {}},
	{3, 5} -> { {"v"}, {"V"}, {}, {}},
	{3, 6} -> { {"b"}, {"B"}, {}, {}},
	{3, 7} -> { {"n"}, {"N"}, {}, {}},
	{3, 8} -> { {"m"}, {"M"}, {}, {}},
	{3, 9} -> { {"["}, {"{"}, {}, {}},
	{3, 10} -> { {"]"}, {"}"}, {}, {}},
	{3, 11} -> { {"DeleteKey"}, {"DeleteKey"}, {"DeleteKey"}, {"DeleteKey"}},
	{i_, j_} -> Table[ {}, {4}]
};

$numBlockMap = {
	{1, 1} -> { {7}, {"!"}, {}, {}},
	{1, 2} -> { {8}, {"@"}, {}, {}},
	{1, 3} -> { {9}, {"#"}, {}, {}},
	{1, 4} -> { {"+"}, {"#"}, {}, {}},
	{2, 1} -> { {4}, {"$"}, {}, {}},
	{2, 2} -> { {5}, {"%"}, {}, {}},
	{2, 3} -> { {6}, {"^"}, {}, {}},
	{2, 4} -> { {"-"}, {"^"}, {}, {}},
	{3, 1} -> { {1}, {"&"}, {}, {}},
	{3, 2} -> { {2}, {"*"}, {}, {}},
	{3, 3} -> { {3}, {"("}, {}, {}},
	{3, 4} -> { {"*"}, {"("}, {}, {}},
	{4, 1} -> { {0}, {")"}, {}, {}},
	{4, 2} -> { {"."}, {"_"}, {}, {}},
	{4, 4} -> { {"/"}, {"+"}, {}, {}},
	{i_, j_} -> Table[ {}, {4}]

};

$symBlockMap = {
	{1, 1} -> { {"/"}, {"?"}, {}, {}},
	{1, 2} -> { {","}, {"<"}, {}, {}},
	{1, 3} -> { {"."}, {">"}, {}, {}},
	{1, 4} -> { {}, {}, {}, {}},
	{2, 1} -> { {}, {}, {}, {}},
	{2, 2} -> { {"\\"}, {"|"}, {}, {}},
	{2, 3} -> { {";"}, {":"}, {}, {}},
	{2, 4} -> { {"'"}, {"\""}, {}, {}},
	{3, 1} -> { {"`"}, {"~"}, {}, {}},
	{i_, j_} -> Table[ {}, {4}]
};



(* ::Subsubsection:: *)
(* displaySelectedGoal *)


displaySelectedGoal[ ] :=
    Module[ { sel, goal},
    	$proofInitNotebook = InputNotebook[];
    	sel = NotebookRead[ $proofInitNotebook];
    	goal = findSelectedFormula[ sel, CurrentValue[ $proofInitNotebook, "NotebookFullFileName"]];
        If[ goal === {},
            translate["noGoal"],
            With[ {selGoal = goal[[1]]},
            	Column[ {
            		Button[ translate[ "OKnext"], $selectedProofGoal = selGoal; $tcActionView++; $replExistProof=0;],
            		displayLabeledFormula[ selGoal, {1}]
            		}]
            ]
        ]
    ]
displaySelectedGoal[ goal_] :=
    Module[ { },
        If[ goal === {},
            translate["noGoal"],
            displayLabeledFormula[ goal, {1}]
        ]
    ]
displaySelectedGoal[args___] := unexpected[ displaySelectedGoal, {args}]

displayLabeledFormula[ f:FML$[ key_, form_, lab_, ___], {i_Integer}] := 
	Module[ {src, nb, labDisp = makeLabel[ lab], orig = getOptionalComponent[ f, "origForm"],
		formDisp = Style[ theoremaDisplay[ form], "DisplayFormula", LineBreakWithin -> False]},
		src = StringReplace[ key[[2]], "Source" <> $cellTagKeySeparator -> "", 1];
		nb = sourceToNotebookFile[ src];
		If[ orig =!= {},
            formDisp = Tooltip[ formDisp, theoremaDisplay[ orig]]
    	];
		Labeled[ 
			Panel[ formDisp, 
				FrameMargins -> 1, ImageSize -> {{360, 1000}, Automatic},
				Background -> Append[ TMAcolor[13], If[ OddQ[ i], 0.05, 0.15]]],
			If[ nb =!= $Failed,
				Hyperlink[ Style[ labDisp, "FormulaLabel"], {nb, key[[1]]}],
				Tooltip[ Style[ labDisp, "FormulaLabel"], translate[ "noNB"] <> " :" <> src]],
			{{Top, Left}},
			Spacings -> {Automatic, 0}
		]
	]
displayLabeledFormula[ args___] := unexpected[ displayLabeledFormula, {args}]

displaySelectedKB[ kb_List] :=
	Module[ {},
        If[ kb === {},
            translate["noKB"],
            Column[ displayLabeledFormulaList[ kb], Left, 0.2]
        ]
    ]
displaySelectedKB[ args___] := unexpected[ displaySelectedKB, {args}]

displayLabeledFormulaList[ l_List] := MapIndexed[ displayLabeledFormula, l]
displayLabeledFormulaList[ args___] := unexpected[ displayLabeledFormulaList, {args}]

sourceToNotebookFile[ s_String] :=
	Module[ {fn, absfn},
        Which[ FileExtension[ s] === "nb",
            fn = s,
            StringQ[ fn = Quiet[ ContextToFileName[ s]]],
            fn = StringReplacePart[ Last[ FileNameSplit[ fn]], "nb", -1],
            True,
            Return[ $Failed]
        ];
        absfn = Block[ {$Path = $TheoremaArchivePath}, FindFile[ fn]]
    ]
sourceToNotebookFile[ args___] := unexpected[ sourceToNotebookFile, {args}]

 


(* ::Subsubsection:: *)
(* extractKBStruct *)


(*
extract hierarchically structured knowledge from a notebook
*)

extractKBStruct[ nb_NotebookObject] := extractKBStruct[ NotebookGet[ nb]]

extractKBStruct[ Notebook[ l_List, __?OptionQ]] := extractKBStruct[ Notebook[ l]] (* process the notebook cells only, without any notebook options *)
	
extractKBStruct[ nb_Notebook] :=
    Module[ {posTit = Cases[ Position[ nb, Cell[ _, "Title", ___]], {a___, 1}],
      posSec =  Cases[ Position[ nb, Cell[ _, "Section", ___]], {a___, 1}], 
      posSubsec = Cases[ Position[ nb, Cell[ _, "Subsection", ___]], {a___, 1}], 
      posSubsubsec = Cases[ Position[ nb, Cell[ _, "Subsubsection", ___]], {a___, 1}], 
      posSubsubsubsec = Cases[ Position[ nb, Cell[ _, "Subsubsubsection", ___]], {a___, 1}], 
      posEnv = Cases[ Position[ nb, Cell[ _, "EnvironmentHeader", ___]], {a___, 1}], 
      posInp = Position[ nb, Cell[ _, "FormalTextInputFormula", ___]], inputs, depth, sub, root, heads, isolated},
      (* extract all positions of relevant cells
         join possible containers with decreasing level of nesting *)
        heads = Join[ posEnv, posSubsubsubsec, posSubsubsec, posSubsec, posSec, posTit];
        (* build up a nested list structure representing the nested cell structure 
           start with singleton lists containing a header and add input cells to the respective group *)
        {inputs, isolated} = Fold[ arrangeInput, {Map[List, heads], {}}, posInp];
        depth = Union[ Map[ Length[ #[[1]]]&, inputs]];
        (* go through all groups starting with the most deeply nested one *)
        While[ Length[ depth] > 1,
            (* the most deeply nested ones are the possible candidates to be joined to other groups *)
         sub = Select[ inputs, Length[ #[[1]]] == depth[[-1]] &];
         (* the less deeply nested ones are groups to which subitems may be added *)
         root = Select[ inputs, Length[#[[1]]] < depth[[-1]] &];
         (* one after the other add lower priority groups to higher priority ones *)
         inputs = Fold[ arrangeSub, root, sub];
         depth = Drop[ depth, -1];
         ];
         (* finally, add isolated nodes at the beginning *)
        Join[ isolated, inputs]
    ]

extractKBStruct[ args___] := unexpected[ extractKBStruct, {args}]


(* ::Subsubsection:: *)
(* arrange items *)


arrangeInput[{struct_, isolated_}, item_] :=
(* given a structured list and a list of isolated items,
   add a new input cell item at the appropriate position
   struct is a list of lists, each sublist represents a group and starts with the group header,
   each entry is a position specification list
   groups are sorted so that low-level groups come first *)
    Module[ {l, root, pos},
    	(* go through all groups to find the one on the right level *)
        pos = Do[
          root = Drop[struct[[i, 1]], -1];
          l = Length[root];
          (* if the position specification of a group header (dropping its last position)
             coincides with the starting part of the item, then this is the right group,
             i.e. the closest enclosing group *)
          If[ Length[item] > l && Take[item, l] == root,
              Return[i]
          ],
          {i, Length[struct]}];
          (* if we have found a fitting group (Return[i] from the loop) we insert 
             at the end in that group, otherwise we add to the list of isolated nodes *)
        If[ NumberQ[pos],
            {Insert[struct, item, {pos, -1}], isolated},
            {struct, Insert[isolated, {item}, -1]}
        ]
    ]
arrangeInput[args___] := unexpected[arrangeInput, {args}]

arrangeSub[struct_, item : {head_, ___}] :=
(* given a structured list,
   add a group item at the appropriate position
   struct is a list of lists, each sublist represents a group and starts with the group header,
   each entry is a position specification list
   groups are sorted so that low-level groups come first   
   Works like arrangeInput, only that we compare by taking the group header representing the item *)
    Module[ {l, root, pos},
    	(* go through all groups to find the one on the right level *)
        pos = Do[
          root = Drop[struct[[i, 1]], -1];
          l = Length[root];
          If[ Length[head] > l && Take[head, l] == root,
              Return[i]
          ],
          {i, Length[struct]}];
          (* if we have found a fitting group (Return[i] from the loop) we insert 
             into that group keeping the sorted order, otherwise make a new group and insert it at the beginning *)
        If[ NumberQ[pos],
            insertSorted[struct, item, pos],
            Insert[struct, {item}, 1]
        ]
    ]
arrangeSub[args___] := unexpected[arrangeSub, {args}]

insertSorted[struct_, item:{head_, ___}, pos_Integer] :=
(* insert item into the sorted list that occurs at position pos in struct *)
    Module[ {p = -1, h},
        Do[
        	(* go through all elements in the sublist at position pos
        	   if an element is a list of integers it represents a position,
        	   otherwise it represents a group of positions, and we select the group header at position 1 *)
            If[ !MatchQ[ h = struct[[pos, i]], {__Integer}],
                h = h[[1]]
            ];
            (* we compare the last entry in the position spec: if the elements pos is greater than the item's
               then we need to insert before that one *)
            If[ h[[ Length[h]]] > head[[ Length[h]]],
                p = i;
                Return[]
            ],
        (* we start comparing at position 2 because we never insert before the group header *)
        {i, 2, Length[struct[[pos]]]}];
        (* if we haven't found a position (Return[i] in the loop) then we insert at position -1, i.e. at the end *)
        Insert[ struct, item, {pos, p}]
    ]
insertSorted[args___] := unexpected[insertSorted, {args}]


(* ::Subsubsection:: *)
(* structView *)


Clear[ structView];

(* produce a list containing the structured view corresponding to notebook file and a list of all cell tags contained
   recursively process the nested list structure generated by extractKBStruct
   result {} means empty structure -> ignore and don't display
   parameter 'task' decides whether the view is generated for the prove tab or the compute tab *)
   
(* group with header and content *)   
structView[ file_, {head:Cell[ sec_, style:"Title"|"Section"|"Subsection"|"Subsubsection"|"Subsubsubsection"|"EnvironmentHeader", opts___], rest___}, tags_, headers_List, task_] :=
    Module[ {content, views, compTags, structControl},
    	(* process content componentwise
    	   during recursion, we collect all cell tags from cells contained in that group 
    	   Transpose -> pos 1 contains the list of subviews
    	   pos 2 contains the list of tags in subgroups *)
    	content = DeleteCases[ Map[ structView[ file, #, tags, Append[ headers, sec], task] &, {rest}], {}];
    	If[ content === {},
    		(* If content is empty then ignore entire unit *)
    		{},
    		(* else *)
        	{views, compTags} = Transpose[ content];
        	compTags = Apply[Union, compTags];
        	(* generate an opener view with the view of the header and the content as a column
           		a global symbol with unique name is generated, whose value stores the state of the opener.
           		The default for Title/Section/Subsection groups is "open", deeper levels are closed by default. *)
        	structControl = "Theorema`Interface`GUI`Private`$kbStructState$" <> ToString[ Hash[ FileBaseName[ file]]] <> "$" <> ToString[ CellID /. {opts}];
        	If[ MemberQ[ {"Title", "Section", "Subsection"}, style] && MatchQ[ ToExpression[ structControl], _Symbol],
        		ToExpression[ structControl <> "=True"]
        	];
        	{OpenerView[ {headerView[ file, head, compTags, task], Column[ views]}, 
        		ToExpression[ StringReplace[ "Dynamic[NEWSYM]", "NEWSYM" -> structControl]]], 
         	compTags}
    	]
    ]
    
(* list processed componentwise *) 
structView[ file_, item_List, tags_, headers_List, task_] :=
    Module[ {content, views, compTags},
     	(* process content componentwise
    	   during recursion, we collect all cell tags from cells contained in that group 
    	   Transpose -> pos 1 contains the list of subviews
    	   pos 2 contains the list of tags in subgroups *)
    	content = DeleteCases[ Map[ structView[ file, #, tags, headers, task] &, item], {}];
    	If[ content === {},
    		{},
    		(* else *)
        	{views, compTags} = Transpose[ content];
        	compTags = Apply[Union, compTags];
        	(* generate a column and return the collected tags also *)
        	{Column[ views], compTags}
    	]
    ]

(* input cell with cell tags *)
structView[ file_, Cell[ content_, "FormalTextInputFormula", a___, CellTags -> cellTags_, b___], tags_, headers_List, task_] :=
    Module[ { isEval, formPos, cleanCellTags, keyTags, formulaLabel, idLabel, nbAvail},
        cleanCellTags = getCleanCellTags[ cellTags];
        (* If keyword does not match, return {} -> ignore *)
        If[ StringLength[ $kbFilterKW] > 2 && testNoMatch[ Apply[ StringJoin, Riffle[ Join[ headers, cleanCellTags], ":"]], "*" <> $kbFilterKW <> "*"],
        	Return[ {}]
        ];
        (* keyTags are those cell tags that are used to uniquely identify the formula in the KB *)
        keyTags = getKeyTags[ cellTags, file];
        (* check whether cell has been evaluated -> formula is in KB? *)
        formPos = Position[ {$tmaEnv, $tmaArch}, FML$[ keyTags, _, __], {2}, 1];
        isEval = formPos =!= {};
        (* Join list of CellTags, use $labelSeparator. *)
        If[ cleanCellTags === {},
            formulaLabel = cellTagsToString[ cellTags];
			idLabel = formulaLabel,
            formulaLabel = cellTagsToString[ cleanCellTags];
			idLabel = getCellIDLabel[ keyTags];
        ];
        (*
        If we load an archive without corresponding notebook available, then $kbStruct contains the archive name instead of the notebook name.
        Hence, 'file' will then be the archive instead of the notebook.
        Instead of hyperlinking into the notebook, we then present a window showing the original cell content. *)
        nbAvail = FileExistsQ[ file] && FileExtension[ file] === "nb";
        (* generate a checkbox and display the label
           checkbox sets the value of the global function kbSelectProve[labels] (kbSelectCompute[labels] resp. for the compute tab),
           enabled only if the formula has been evaluated 
           label is a hyperlink to the notebook or a button that opens a new window displaying the formula *)
        {Switch[ task,
            "prove",
            Row[ {Checkbox[ Dynamic[ kbSelectProve[ "KEY"]], Enabled -> isEval] /. "KEY" -> keyTags, 
                Tooltip[ Hyperlink[ Style[ formulaLabel, If[ isEval,
                                                       "FormalTextInputFormula",
                                                       "FormalTextInputFormulaUneval"
                                                   ]], {file, idLabel}, Enabled -> nbAvail, ActiveStyle -> If[ nbAvail, "HyperlinkActive", None]],
                             If[ isEval,
                             	theoremaDisplay[ Extract[ {$tmaEnv, $tmaArch}, Append[ formPos[[1]], 2]]],
                             	displayCellContent[ content]]
                    ],
                    If[ isEval, 
                    	"", 
                    	(* else: unevaluated -> put remoteEval button *)
                    	With[ {tag = idLabel}, 
                    		Button[ Style[ "\[ReturnIndicator]", "FormalTextInputFormulaUneval", FontSlant -> "Plain"], remoteEvalFormula[ file, tag], Appearance -> None]
                    	]
                    ]},
                Spacer[10]],
            "compute",
            Row[ {Checkbox[ Dynamic[ kbSelectCompute["KEY"]], Enabled -> isEval] /. "KEY" -> keyTags,
                Tooltip[ Hyperlink[ Style[ formulaLabel, If[ isEval,
                                                       "FormalTextInputFormula",
                                                       "FormalTextInputFormulaUneval"
                                                   ]], {file, idLabel}, Enabled -> nbAvail, ActiveStyle -> If[ nbAvail, "HyperlinkActive", None]],
                             If[ isEval,
                             	theoremaDisplay[ Extract[ {$tmaEnv, $tmaArch}, Append[ formPos[[1]], 2]]],
                             	displayCellContent[ content]]
                    ],
                    If[ isEval, 
                    	"", 
                    	(* else: unevaluated -> put remoteEval button *)
                    	With[ {tag = idLabel}, 
                    		Button[ Style[ "\[ReturnIndicator]", "FormalTextInputFormulaUneval", FontSlant -> "Plain"], remoteEvalFormula[ file, tag], Appearance -> None]
                    	]
                    ]},
                Spacer[10]],
            "solve",
            Row[ {Checkbox[ Dynamic[ kbSelectSolve[ "KEY"]], Enabled -> isEval] /. "KEY" -> keyTags, 
                Tooltip[ Hyperlink[ Style[ formulaLabel, If[ isEval,
                                                       "FormalTextInputFormula",
                                                       "FormalTextInputFormulaUneval"
                                                   ]], {file, idLabel}, Enabled -> nbAvail, ActiveStyle -> If[ nbAvail, "HyperlinkActive", None]],
                             If[ isEval,
                             	theoremaDisplay[ Extract[ {$tmaEnv, $tmaArch}, Append[ formPos[[1]], 2]]],
                             	displayCellContent[ content]]
                    ],
                    If[ isEval, 
                    	"", 
                    	(* else: unevaluated -> put remoteEval button *)
                    	With[ {tag = idLabel}, 
                    		Button[ Style[ "\[ReturnIndicator]", "FormalTextInputFormulaUneval", FontSlant -> "Plain"], remoteEvalFormula[ file, tag], Appearance -> None]
                    	]
                    ]},
                Spacer[10]]    
            ], {keyTags}}
    ]

(* input cell without cell tags -> ignore *)
structView[ file_, Cell[ content_, "FormalTextInputFormula", ___], tags_, headers_List, task_] := {}

structView[ args___] := unexpected[ structView, {args}]

(* header view *)
headerView[ file_, Cell[ content_String, style_, ___], tags_, task_] :=
(* tags contains all tags contained in the group
   generate a checkbox for the whole group and the header from the cell
   checkbox does not have an associated variable whose value the box represents
   instead, the checkbox is checked if all tags containd in the group are checked,
   checking the box calls function setAll in order to set/unset all tags contained in the group *)
Module[ {trim = StringReplace[ content, "\n"|"\t" -> " "]},
   	Switch[ task,
    	"prove",
        Row[ {Checkbox[ Dynamic[ allTrue[ tags, kbSelectProve], setAll[ tags, kbSelectProve, #] &]], Style[ trim, style]}, Spacer[10]],
        "compute",
        Row[ {Checkbox[ Dynamic[ allTrue[ tags, kbSelectCompute], setAll[ tags, kbSelectCompute, #] &]], Style[ trim, style]}, Spacer[10]],
        "solve",
        Row[ {Checkbox[ Dynamic[ allTrue[ tags, kbSelectSolve], setAll[ tags, kbSelectSolve, #] &]], Style[ trim, style]}, Spacer[10]]        
    ]
]
headerView[ file_, Cell[ content_TextData, style_, ___], tags_, task_] := headerView[ file, Cell[ formattedCellToString[ content], style], tags, task]
headerView[ args___] := unexpected[ headerView, {args}]

displayCellContent[ BoxData[ b_]] := DisplayForm[ b]
displayCellContent[ c_] := DisplayForm[ c]
displayCellContent[ args___] := unexpected[ displayCellContent, {args}]

formattedCellToString[ TextData[ l_List]] := Apply[ StringJoin, Map[ textDataToString, l]]
formattedCellToString[ d_] := textDataToString[ d]
formattedCellToString[ args___] := unexpected[ formattedCellToString, {args}]

textDataToString[ s_String] := StringReplace[ s, "\n"|"\t" -> " "]
textDataToString[ StyleBox[ s_String, ___]] := textDataToString[ s]
textDataToString[ Cell[ BoxData[ b_], ___]] := "\!\(" <> ToString[ InputForm[ b]] <> "\)"
textDataToString[ _] := "\[DownQuestion]?"
textDataToString[ args___] := unexpected[ textDataToString, {args}]

remoteEvalFormula[ file_, tag_] :=
	Module[{nb},
		NotebookLocate[ {file, tag}];
		nb = Select[ Notebooks[], CurrentValue[ #, "NotebookFullFileName"] === file &, 1];
		Scan[ SelectionEvaluate, nb]
	]
remoteEvalFormula[ args___] := unexpected[ remoteEvalFormula, {args}]


(* ::Subsubsection:: *)
(* updateKBBrowser *)


(* global variable $kbStruct contains the knowledge structure
   for each notebook ever evaluated in the session it contains an entry
   filename -> struct, where
   filename is the full filename of the notebook and
   struct is the nested cell structure containing the cells at those positions obtained by extractKBStruct *)
updateKBBrowser[ file_] :=
    Module[ {pos, new, nbExpr},
        pos = Position[ $kbStruct, file -> _, {1}, 1];
        (* We don't extract the entire cells, we throw away all options except CellTags and CellID in order to not blow up $kbStruct too much *)
        nbExpr = Cases[ $TMAcurrentEvalNB, {file, e_} -> e, {1}, 1];
        If[ nbExpr === {},
        	(* the corresponding notebook has not been evaluated yet *)
        	Return[]
        ];
        (* This is a good place to check for well-formedness of the notebook (multiple labels, etc.). *)
        ensureNotebookIntegrity[ file];
        $tmaNbUpdateQueue = DeleteCases[ $tmaNbUpdateQueue, {file, _}, {1}, 1];
        new = With[ {nb = First[ nbExpr]},
                          extractKBStruct[ nb] /. l_?VectorQ :> (Extract[ nb, l] /. {c:Cell[ _, _, ___] :> DeleteCases[ c, Except[ CellTags|CellID] -> _]})
                      ];
        (* if there is already an entry for that notebook then replace the structure,
           otherwise add new entry *)
        If[ pos === {},
            AppendTo[ $kbStruct, file -> new],
            (* For some strange reasons, using 
               $kbStruct = ReplacePart[ $kbStruct, pos[[1]] -> )(file -> new)]
               does not trigger the commander to refresh although it should listen to $kbStruct. Using the indexed assignment works ... *)
            $kbStruct[[pos[[1,1]]]] = file -> new;
        ];
        (* set $tcKBBrowseSelection such that the tab corresponding ot this notebook will be displayed in the knowledge browser *)
        Scan[ ($tcKBBrowseSelection[ #] = file)&, {"prove", "compute", "solve"}]
    ]
updateKBBrowser[args___] := unexpected[ updateKBBrowser, {args}]


(* ::Subsubsection:: *)
(* displayKBBrowser *)

displayKBBrowser[ task_String] :=
    Module[ {cells, view, allNB},
        If[ $kbStruct === {} || !ValueQ[ $tcKBBrowseSelection[ task]],
            Row[ {emptyPane[ translate[ "noKnowl"]], makeUpdateArea[]}, Spacer[3]],
            (* generate tabs for each notebook,
               tab label contains a short form of the filename, tab contains a Pane containing the structured view *)
            allNB = Map[ First, $kbStruct];
            cells = Replace[ $tcKBBrowseSelection[ task], $kbStruct];
            Assert[ ListQ[ cells]];
            view = structView[ $tcKBBrowseSelection[ task], cells, {}, {}, task];
            If[ view === {},
            	view = translate[ "noKnowl"],
            	(* else *)
            	view = view[[1]]
            ];
            If[ task === "prove",
                $selectedProofKB = Select[ $tmaEnv, kbSelectProve[ #[[1]]]&];
            ];
            Column[{
            	Button[ translate[ "OKnext"], $tcActionView++, ImageSize -> 360],
            	Row[{
            		With[ {label = Row[ {translate[ "FilteredBy"] <> ": ", InputField[ $kbFilterKW, String]}]},
						Button[ label,
							CreateDialog[{
								Row[ {translate[ "Keyword"] <> ": ", InputField[ Dynamic[ $kbFilterKW], String, ContinuousAction -> True]}],
								DefaultButton[ DialogReturn[]]},
								WindowTitle-> translate[ "FilterKBWindow"]
							],
							Appearance -> "Frameless"
						]
					], 
					Button[ translate[ "ShowAll"], $kbFilterKW = ""]}, 
					Spacer[2]
				],
				If[ Apply[ Plus, Map[ StringLength[ FileBaseName[ #]]&, allNB]] > 50,
					(* button labels sum up to more than 50 chars long -> buttons become too wide -> provide a menu *)
					Row[ {PopupMenu[ Dynamic[ $tcKBBrowseSelection[ task]], Map[ First[#] -> Tooltip[ FileBaseName[ First[#]], First[#]]&, $kbStruct]],
						makeUpdateArea[]}, Spacer[3]],
					(* else: select with buttons ala TabView *)
					Row[{
						Row[ Map[ Button[ 
							Tooltip[ Style[ FileBaseName[ #], FontColor -> If[ $tcKBBrowseSelection[ task] === #, TMAcolor[4], TMAcolor[13]]], #], 
							$tcKBBrowseSelection[ task] = #, 
							Background -> If[ $tcKBBrowseSelection[ task] === #, TMAcolor[6], TMAcolor[0]], 
							FrameMargins -> 2, ImageMargins -> 0, ImageSize -> Automatic]&, Map[ First, $kbStruct]]
						],
						makeUpdateArea[]}, Spacer[3]
					]
				],
				Pane[ view, ImageSize -> {350, Automatic}]
				(*PaneSelector[ Map[ #[[1]] -> structView[ #[[1]], #[[2]], {}, {}, task][[1]]&, 
                   			$kbStruct], Dynamic[ $tcKBBrowseSelection[ task]], ImageSize -> {350, Automatic}]*),
                Button[ translate[ "OKnext"], $tcActionView++]
            }]
        ]
    ]
displayKBBrowser[args___] := unexpected[ displayKBBrowser, {args}]

(*
TabView[
                  		Map[Tooltip[Style[FileBaseName[#[[1]]], "NotebookName"], #[[1]]] -> 
                     		Pane[structView[#[[1]], #[[2]], {}, {}, task][[1]], ImageSizeAction -> "Scrollable", Scrollbars -> Automatic] &, 
                   			$kbStruct], 
                  		Appearance -> {"Limited", 10}, FrameMargins->None]
                  		*)

refreshKBstruct[] :=
	Module[{nbFiles},
		If[ inEnvironment[], Return[ ]];
		(* refresh those that are older than 1.5 sec *)
		nbFiles = Cases[ $tmaNbUpdateQueue, {f_, _?(SessionTime[] - # > 1.5&)} -> f, {1}, 1];
		Scan[ updateKBBrowser, nbFiles]
	]
refreshKBstruct[ args___] := unexpected[ refreshKBstruct, {args}]

(* The update area consists of a "reload-button" which automatically updates and displays as a checkmark if no updates are pending. 
   Second, it has an invisible field ("") which updates every 10 seconds and triggers regular updates of pending events.
   *)
makeUpdateArea[ ] := Dynamic[ 
	If[ $tmaNbUpdateQueue =!= {}, 
		Button[ Style[ "\:21ba", {Medium}], refreshKBstruct[], Appearance -> None], 
		(* else *)
		"\[Checkmark]"
		]
	]
makeUpdateArea[ args___] := unexpected[ makeUpdateArea, {args}]

(* ::Subsubsection:: *)
(* structViewBuiltin *)


Clear[structViewBuiltin];
Clear[resultBuiltin];

(* structured view for builtin operators
   follows the ideas of the structured view of the KB *)
   
structViewBuiltin[{category_String, rest__List}, tags_, task_String] :=
    Module[ {sub, compTags, opGroup},
        sub = Transpose[Map[structViewBuiltin[#, tags, task] &, {rest}]];
        compTags = Apply[Union, sub[[2]]];
        opGroup = partitionFill[ sub[[1]], 3];
        {OpenerView[{headerViewBuiltin[category, compTags, task], Grid[ opGroup, Alignment -> {Left, Baseline}, Spacings -> {2, Automatic}, ItemSize -> Full]}, 
        	ToExpression["Dynamic[Theorema`Interface`GUI`Private`$builtinStructState$"<>category<>"]"]], 
         compTags}
    ]     
    
structViewBuiltin[ item:List[__List], tags_, task_String] :=
    Module[ {sub, compTags},
        sub = Transpose[Map[structViewBuiltin[#, tags, task] &, item]];
        compTags = Apply[Union, sub[[2]]];
        {Column[sub[[1]]], compTags}
    ]

structViewBuiltin[ {op_String, display_, _, _, _}, tags_, task_String] :=
    Module[ { },
        {Switch[ task,
            "prove",
            Row[{Checkbox[ Dynamic[ buiActProve[op]]], Tooltip[ Style[ DisplayForm[ display], "FormalTextInputFormula"], op]}, 
                Spacer[2]],
            "compute",
          	Row[{Checkbox[ Dynamic[ buiActComputation[op]]], Tooltip[ Style[ DisplayForm[ display], "FormalTextInputFormula"], op]}, 
          		Spacer[2]],
            "solve",
          	Row[{Checkbox[ Dynamic[ buiActSolve[op]]], Tooltip[ Style[ DisplayForm[ display], "FormalTextInputFormula"], op]}, 
          		Spacer[2]]
        ], {op}}
    ]

structViewBuiltin[args___] :=
    unexpected[structViewBuiltin, {args}]


headerViewBuiltin[ category_String, tags_, task_String] :=
    Module[ {},
    	Switch[ task,
    		"prove",
    		Row[{Checkbox[ Dynamic[ allTrue[ tags, buiActProve], 
        		setAll[ tags, buiActProve, #] &]], 
          		Style[ translate[category], "Section"]}, Spacer[4]],
    		"compute",
        	Row[{Checkbox[ Dynamic[ allTrue[ tags, buiActComputation], 
        		setAll[ tags, buiActComputation, #] &]], 
          		Style[ translate[category], "Section"]}, Spacer[4]],
          	"solve",
          	Row[{Checkbox[ Dynamic[ allTrue[ tags, buiActSolve], 
        		setAll[ tags, buiActSolve, #] &]], 
          		Style[ translate[category], "Section"]}, Spacer[4]]
    	]
    ]

headerViewBuiltin[args___] :=
    unexpected[ headerViewBuiltin, {args}]


(* ::Subsection:: *)
(* Summary of used builtins *)

summarizeBuiltins[ task_String] := summarizeBuiltins[ task, $tmaBuiltins]

summarizeBuiltins[ task_String, l_List] := 
	Module[ {cat},
		cat = Map[ resultBuiltin[ #, task]&, l];
		Column[ Apply[ Join, Map[ #[[1]]&, cat]]]		
	]
summarizeBuiltins[args___] := unexpected[ summarizeBuiltins, {args}]
   
resultBuiltin[{category_String, rest__List}, task_String] :=
    Module[ {sub, opAct, opInact, subCat},
        sub = Map[ resultBuiltin[ #, task] &, {rest}];
        opAct = Cases[ sub, {op_String, True} -> op];
        opInact = Cases[ sub, {op_String, False} -> op];
        subCat = Cases[ sub, {_List, _}];
        Which[ 
        	opInact === {} && Apply[ And, Map[ #[[2]]&, subCat]],
        	(* all True *)
        	{{"\[Checkmark] [" <> category <> "]"}, True},
        	opAct === {} && Not[ Apply[ Or, Map[ #[[2]]&, subCat]]],
        	{{Style[ category, "ComponentEmpty"]}, False},
        	True,
        	{{OpenerView[ {category,
        		Column[ Join[
        			{Row[ Prepend[ Riffle[ Map[ Style[ #, "ComponentActive"]&, opAct], ","], "\[Checkmark] "]], 
        			Row[ Riffle[ Map[ Style[ #, "ComponentInactive"]&, opInact], ","]]}, 
        			Map[ #[[1]]&, subCat]]]}, True]}, Undefined}
        ]
    ] 
 
resultBuiltin[ {op_String, display_, _, _, _}, task_String] :=
	{op, Switch[ task,
    		"prove",
    		buiActProve[ op],
    		"compute",
    		buiActComputation[ op],        	
          	"solve",
          	buiActSolve[ op]]}        	

resultBuiltin[args___] :=
    unexpected[ resultBuiltin, {args}]

  

(* ::Subsubsection:: *)
(* structViewRules *)


Clear[structViewRules];
Clear[makeRuleRow];
Clear[displaySelectedRules];

(*
	Go through the nested rule list recursively and bulid up the nested opener view for rule selection.
	Return a list {op, rules}, where
		op is the main OpenerView and
		rules is a list of all inference rule names contained in it.
	As side effects, interactive elements contained in the view set the initial values for
	each rule's activity (ruleActive), textActivity (ruleTextActive), and priority (rulePriority).
	ruleActive and rulePriority are GUI-private symbols, their values are only needed as initial
	values and go into the initial proof object (settings can be changed during the proof).
	ruleTextActive is a global symbol, it does not go into the proof object and can be modified globally.
*)

structViewRules[ {category_String},___] := Sequence[];

(*Responsible for group name of rules *)
structViewRules[ {category_String, r__}, tags_, open_:False] :=
    Module[ {sub, compTags, structControl},
		sub = Map[ structViewRules[ #, tags] &, {r}];
		If[ sub === {}, Return[ {{}, {}}]];
        sub = Transpose[ sub];
        compTags = Apply[ Union, sub[[2]]];
        structControl = "Theorema`Interface`GUI`Private`$ruleStructState$" <> ToString[ Hash[ category]];
        If[ open && MatchQ[ ToExpression[ structControl], _Symbol],
        	ToExpression[ structControl <> "=True"]
        ];
        {OpenerView[ {structViewRules[ category, compTags], Column[ sub[[1]]]}, 
        	ToExpression[ StringReplace[ "Dynamic[NEWSYM]", "NEWSYM" -> structControl]]], 
         compTags}
    ]

(*Responsible for groupe name of rules. 
	If no rules in group, returns empty Sequense *)
structViewRules[ {category_String}, tags_, open_] := Sequence[];

structViewRules[ Hold[ rs_]] := 
	Module[ {list = {}},
		If[ StringLength[ $ruleFilterKW] > 2,		
			list = DeleteCases[ rs, {r_Symbol /; testNoMatch[ MessageName[ r, "usage", $TmaLanguage], "*" <> $ruleFilterKW <> "*"], t_, text_, p_Integer ,___}, Infinity];
			structViewRules[ list, {}, True],
			(* else *)
			structViewRules[ rs, {}, True]
		]
	]

testNoMatch[ s_String, p_String] := Not[ StringMatchQ[ s, p, IgnoreCase -> True]]
testNoMatch[ s_, p_] := True

displaySelectedRules[ Hold[ rs_]] := 
	Module[ {actRules},
		(* Select rule defaults *)  
		actRules = Cases[ rs, {r_Symbol, _, _, _Integer, ___}, Infinity];
		(* Sort list by priority *)
		actRules = Sort[ actRules, rulePriority[ #1[[1]]] < rulePriority[ #2[[1]]]&];
		Pane[		
			Column[ Map[ makeRuleRow, actRules]],
			ImageSize -> {360,200},
			Scrollbars -> {False, True}
		]	
	]

makeRuleRow[ {r_Symbol, False, rta_, prio_, ___}] /; !ruleActive[ r] := Sequence[]

makeRuleRow[ {r_Symbol, ra_, rta_, prio_, ___}] := 
	Module[ {}, 
		Style[ 
			Row[{Style[ "(" <> ToString[ rulePriority[ r]] <> ")", FontWeight -> If[ prio === rulePriority[ r], "Plain", "Bold"]], Spacer[2],
				Tooltip[ Style[ showProofTextPic[ ruleTextActive[ r]], FontWeight -> If[ rta === ruleTextActive[ r], "Plain", "Bold"]], 
					MessageName[ ruleTextActive, "usage", $TmaLanguage]], Spacer[5], 
				Style[ MessageName[ r, "usage", $TmaLanguage], 
					Which[ ruleActive[ r] && !ra, 
						FontWeight -> "Bold", 
						   !ruleActive[ r] && ra, 
						FontVariations -> {"StrikeThrough" -> True}, 
						   True, 
						FontWeight -> "Plain"]]}],
			LineBreakWithin -> False]
	]

(*Draws toggler icon *) 
(* showProofTextPic[ active_] = Graphics[ {If[ active, GrayLevel[0], GrayLevel[0.7]], 
	{Thin, Line[{{0, 0}, {4, 0}, {4, 4}, {0, 4}, {0, 0}}], Table[ Line[{{1, i}, {3, i}}], {i, 1, 3}]}}, ImageSize -> {15, 15}, PlotRange -> {{-1, 5}, {-1, 5}}];*)
showProofTextPic[ active_] = If[ active, "\:270D", "\:2751"];

(*Responsible for rule *) 
structViewRules[ {r_Symbol, active:(True|False), textActive:(True|False), p_Integer, ___}, tags_] :=
    Module[ {align = Baseline},
        {Style[ 
         Row[{
            Row[{Tooltip[ 
            		Checkbox[ Dynamic[ ruleActive[ r]], BaselinePosition -> align],
            		translate[ "ruleActive"]], 
            	Tooltip[
                    Toggler[ Dynamic[ ruleTextActive[ r]],
                    	{False -> showProofTextPic[ False],
                    	True -> showProofTextPic[ True]}, BaselinePosition -> align],
                	MessageName[ ruleTextActive, "usage", $TmaLanguage]],
                Tooltip[ 
                	PopupMenu[ Dynamic[ rulePriority[ r]], Table[ i, {i,1,100}], BaselinePosition -> align, ImageSize -> {45, 16}],
                    translate[ "rulePriority"]]}
            ],
            MessageName[ r, "usage", $TmaLanguage]}, Spacer[7]], LineBreakWithin -> False], {r}}
    ]

structViewRules[ category_String, tags_] :=
    Module[ {align = Baseline},
    	Row[{
    		Row[{
    			Checkbox[ 
    				Dynamic[ allTrue[ tags, ruleActive], setAll[ tags, ruleActive, #] &], BaselinePosition -> align],
        		Toggler[ Dynamic[ allTrue[ tags, ruleTextActive], setAll[ tags, ruleTextActive, #] &],
                    	{False -> showProofTextPic[ False],
                    	True -> showProofTextPic[ True]}, BaselinePosition -> align]
    		}], 
          	Style[ translate[ category], "Section"]}, Spacer[5]]
    ]


structViewRules[args___] :=
    unexpected[structViewRules, {args}];


(* ::Subsubsection:: *)
(* check/set values *)


allTrue[ l_, test_] :=
    Catch[Module[ {},
              Scan[If[ Not[TrueQ[test[#]]],
                       Throw[False]
                   ] &, l];
              True
          ]]

setAll[l_, test_, val_] :=
    Scan[(test[#] = val) &, l]
   


(* ::Subsubsection:: *)
(* displayBuiltinBrowser *)


(* see displayKBBrowser *)

displayBuiltinBrowser[ task_String] :=
  Column[{
  	Button[ translate[ "OKnext"], $tcActionView++],
	Row[ {Button[ translate[ "ResetBui"], initBuiltins[ {task}]]}, Spacer[3]],
	(* Putting an invisible frame around the pane allows to measure its size correctly. Otherwise its width is calculated as the width
	   of the content, regardless of the {355, Automatic} size spezified *)
  	Framed[ Pane[ structViewBuiltin[ $tmaBuiltins, {}, task][[1]], {354, Automatic}, ImageSizeAction -> "Scrollable", Scrollbars -> Automatic], FrameStyle -> None],
  	Button[ translate[ "OKnext"], $tcActionView++]
  }]
displayBuiltinBrowser[args___] := unexcpected[ displayBuiltinBrowser, {args}]

$allProveSettings = Hold[ $selectedProofGoal, $selectedProofKB, $selectedRuleSet, $selectedStrategy, $selectedSearchDepth, $selectedSearchTime,
	$eliminateBranches, $eliminateSteps, $eliminateFormulae,
	$interactiveProofSitSel, $interactiveNewProofSitFilter, $proofCellStatus,
	kbSelectProve, buiActProve, ruleActive, rulePriority, $tcKBBrowseSelection];

selectProver[ ] :=
    Column[{
    	Button[ translate[ "OKnext"], $tcActionView++],

    	Labeled[ Tooltip[ PopupMenu[ Dynamic[ $selectedRuleSet], Map[ MapAt[ translate, #, {2}]&, $registeredRuleSets]],
    			Apply[ Function[ rs, MessageName[ rs, "usage", $TmaLanguage], {HoldFirst}], $selectedRuleSet]], 
    		translate[ "pRules"], {{ Top, Left}}],
    	Module[ {view},
			
			{view, $allRules} = structViewRules[ $selectedRuleSet];								
    		
    		Labeled[ Column[{
				Row[{	
				Button[ translate[ "RestoreDefaults"], setRulesDefaults[ $selectedRuleSet]],
				Button[ translate[ "ShowAll"], $ruleFilterKW = ""]},
				Spacer[2]],
				With[ {label = Row[ {translate[ "FilteredBy"] <> ": ", InputField[ $ruleFilterKW, String]}]},
					Button[ label,
						CreateDialog[{
							Row[ {translate[ "Keyword"] <> ": ", InputField[ Dynamic[ $ruleFilterKW], String, ContinuousAction -> True]}],
							DefaultButton[ DialogReturn[]]},
							WindowTitle-> translate[ "FilterRulesWindow"]
						],
						Appearance -> "Frameless"
					]
				],
				(* Pane[ views[[$tcActivitiesView, $tcActionView]], {400, 600}, ImageSizeAction -> "Scrollable", Scrollbars -> Automatic,
                    ImageMargins -> 0, FrameMargins -> 10]*)
				If[ view === {}, 
					translate[ "noRules"], 
					(* else *)
					Pane[ view, {360, Automatic}, ImageSizeAction -> "Scrollable", Scrollbars -> Automatic]
				]}], translate[ "pRulesSetup"], {{Top, Left}}]],
    	Labeled[ Tooltip[ PopupMenu[ Dynamic[ $selectedStrategy], Map[ MapAt[ translate, #, {2}]&, $registeredStrategies]],
    		With[ {ss = $selectedStrategy}, MessageName[ ss, "usage", $TmaLanguage]]], 
    		translate[ "pStrat"], {{ Top, Left}}],
    	Labeled[ Grid[{
    		{translate[ "sDepth"], Dynamic[ Row[ {Slider[ Dynamic[ $selectedSearchDepth], {2, $maxSearchDepth, 1}, ImageSize -> 150],
    			InputField[ Dynamic[ $selectedSearchDepth], Number, FieldSize -> 3], 
    			Button[ "-", $selectedSearchDepth--],
    			Button[ "+", $selectedSearchDepth++],
    			Button[ "\[LeftSkeleton]", $maxSearchDepth/=2],
    			Button[ "\[RightSkeleton]", $maxSearchDepth*=2]}]]},
    		{translate[ "sTime"], Dynamic[ Row[ {Slider[ Dynamic[ $selectedSearchTime], {2, $maxSearchTime, 1}, ImageSize -> 133],
    			If[ $selectedSearchTime === Infinity,
    				InputField[ "\[Infinity]", String, FieldSize -> 3], 
    				InputField[ Dynamic[ $selectedSearchTime], Number, FieldSize -> 3]], 
    			Button[ "-", $selectedSearchTime--],
    			Button[ "+", $selectedSearchTime++],
    			Button[ "\[LeftSkeleton]", $maxSearchTime/=2],
    			Button[ "\[RightSkeleton]", $maxSearchTime*=2],
    			If[ $selectedSearchTime === Infinity, 
    				Button[ "\[Infinity]", $selectedSearchTime=360, Appearance :> "Pressed"],
    				Button[ "\[Infinity]", $selectedSearchTime=Infinity]
    			]}]]}
    		}, Alignment -> Left], translate[ "sLimits"], {{Top, Left}}],
    	Labeled[ Grid[{
    		{Checkbox[ Dynamic[ $eliminateBranches]], translate[ "elimBranches"]},
    		{Checkbox[ Dynamic[ $eliminateSteps]], translate[ "elimSteps"]},
    		{Checkbox[ Dynamic[ $eliminateFormulae]], translate[ "elimForm"]}
    		}, Alignment -> {Left}], 
    		translate[ "pSimp"], {{Top, Left}}],
    	Labeled[ Grid[{
    		{Checkbox[ Dynamic[ $interactiveProofSitSel]], translate[ "interactiveProofSitSel"]},
    		{Checkbox[ Dynamic[ $interactiveNewProofSitFilter]], translate[ "interactiveNewProofSitFilter"]},
    		{Checkbox[ Dynamic[ allTrue[ {existsGoalInteractive, forallKBInteractive}, ruleActive], setAll[ {existsGoalInteractive, forallKBInteractive}, ruleActive, #] &]], translate[ "interactiveInstantiate"]}
    		}, Alignment -> {Left}], 
    		translate[ "pInteractive"], {{Top, Left}}],
    	Module[ {po},
    		po = {Labeled[ RadioButtonBar[ 
    				Dynamic[ $proofCellStatus], {Automatic -> translate[ "auto"], Open -> translate[ "open"], Closed -> translate[ "closed"]}], 
    				translate[ "proofCellStatus"], Left]};
    		$numExistProofs = findNumExistingProofs[ $proofInitNotebook, $selectedProofGoal];
    		If[ $replExistProof === 0,
    			$replExistProof = $numExistProofs + 1;
    		];
    		If[ $numExistProofs > 0,
    			PrependTo[ po,
    				Labeled[ PopupMenu[ Dynamic[ $replExistProof], Prepend[ Table[ i -> "#"<>ToString[i], {i, $numExistProofs}], $numExistProofs+1 -> "\[LongDash]"],
    					BaselinePosition -> Baseline, ImageSize -> {50, 20}], 
    				translate[ "replaceExistProof"], Left]
    			]
    		];
    		Labeled[ Row[ {Spacer[20], Column[ po]}], translate[ "proofOutput"], {{Top, Left}}]
    	],
    	Button[ translate[ "OKnext"], $tcActionView++]	
    	}]
selectProver[ args___] := unexpected[ selectRuleSet, {args}]

findNumExistingProofs[ nb_NotebookObject, goal_FML$] :=
	Module[{sel},
		(* Find all cells with the proofIdTag *)
		sel = NotebookFind[ $proofInitNotebook, makeProofIDTag[ goal], All, CellTags];
		If[ sel === $Failed,
			(* if none occur -> 0 *)
			0,
			sel = NotebookRead[ $proofInitNotebook];
			(* read selection *)
			If[ ListQ[ sel],
				(* multiple cells selected -> number of cells = number of proofs *)
				Length[ sel],
				(* single cell -> 1*)
				1
			]
		]
	]
findNumExistingProofs[ nb_, g_] := 0
findNumExistingProofs[ args___] := unexpected[ findNumExistingProofs, {args}]

submitProveTask[ ] := 
	Module[ {},
		Column[{
			Button[ translate["prove"],
				$tcActionView++;
				execProveCall[ $selectedProofGoal, $selectedProofKB, 
					{$selectedRuleSet, Map[ # -> ruleActive[#]&, $allRules], Map[ # -> rulePriority[#]&, $allRules]},
					$selectedStrategy, $selectedSearchDepth,
					(* If interactive proving is active in one way, then do not apply time limit *)
					If[ TrueQ[ ruleActive[ forallKBInteractive] || ruleActive[ existsGoalInteractive] || $interactiveProofSitSel || $interactiveNewProofSitFilter],
						Infinity,
						$selectedSearchTime
					],
					{$eliminateBranches, $eliminateSteps, $eliminateFormulae}, $replExistProof], 
				Method -> "Queued", Active -> ($selectedProofGoal =!= {})],
			Column[{
					Labeled[ Pane[ displaySelectedGoal[ $selectedProofGoal], {360, Automatic}, ImageSizeAction -> "Scrollable", Scrollbars -> Automatic],
						translate["selGoal"], {{Top, Left}}],
					Labeled[ Pane[ displaySelectedKB[ $selectedProofKB], {360, {10, 250}}, ImageSizeAction -> "Scrollable", Scrollbars -> Automatic], 
						translate["selKB"], {{Top, Left}}],
					Labeled[ Pane[ summarizeBuiltins[ "prove"], {360, {10, 250}}, ImageSizeAction -> "Scrollable", Scrollbars -> Automatic], 
						translate["selBui"], {{Top, Left}}]},
					Left
				],
			
			Column[{				
				Labeled[ displaySelectedRules[ $selectedRuleSet], translate[ "selectedRules"]<>":", {{Top,Left}}],
				Labeled[ Tooltip[ $selectedStrategy /. $registeredStrategies, MessageName[ Evaluate[ $selectedStrategy], "usage", $TmaLanguage]], translate[ "pStrat"]<>":", Left],
				Labeled[ $selectedSearchDepth, translate[ "sDepth"]<>":", Left],
				Labeled[ $selectedSearchTime, translate[ "sTime"]<>":", Left],
				Labeled[
					Column[{
    					If[ TrueQ[ $eliminateBranches], translate[ "elimBranches"], Sequence[]],
    					If[ TrueQ[ $eliminateSteps], translate[ "elimSteps"], Sequence[]],
    					If[ TrueQ[ $eliminateFormulae], translate[ "elimForm"], Sequence[]]
    				}],
    				translate[ "pSimp"]<>":", {{Left, Top}}],
				Labeled[
					Column[{
    					If[ TrueQ[ $interactiveProofSitSel], translate[ "interactiveProofSitSel"], Sequence[]],
    					If[ TrueQ[ $interactiveNewProofSitFilter], translate[ "interactiveNewProofSitFilter"], Sequence[]],
    					If[ TrueQ[ Map[ ruleActive, And[ existsGoalInteractive, forallKBInteractive]]], translate[ "interactiveInstantiate"], Sequence[]]
    				}],
    				translate[ "pInteractive"]<>":", {{Left, Top}}],
				Labeled[ 
					Column[{
						translate[ "replaceExistProof"] <> ": " <> If[ $replExistProof > $numExistProofs, "\[LongDash]", "#" <> ToString[ $replExistProof]],
						translate[ "proofCellStatus"] <> ": " <>
							Switch[ $proofCellStatus,
								Automatic, translate[ "auto"],
								Open, translate[ "open"],
								Closed, translate[ "closed"]
							]}],
    				translate[ "proofOutput"]<>":", {{Left, Top}}]
			}]			
			,
			(* Method -> "Queued" so that no time limit is set for proof to complete *)
			Button[ translate["prove"],
				$tcActionView++;
				execProveCall[ $selectedProofGoal, $selectedProofKB, 
					{$selectedRuleSet, Map[ # -> ruleActive[#]&, $allRules], Map[ # -> rulePriority[#]&, $allRules]},
					$selectedStrategy, $selectedSearchDepth,
					(* If interactive proving is active in one way, then do not apply time limit *)
					If[ TrueQ[ ruleActive[ forallKBInteractive] || ruleActive[ existsGoalInteractive] || $interactiveProofSitSel || $interactiveNewProofSitFilter],
						Infinity,
						$selectedSearchTime
					],
					{$eliminateBranches, $eliminateSteps, $eliminateFormulae}, $replExistProof], 
				Method -> "Queued", Active -> ($selectedProofGoal =!= {})]
		}]
	]
submitProveTask[ args___] := unexpected[ submitProveTask, {args}]

execProveCall[ goal_FML$, kb_, rules:{ruleSet_, active_List, priority_List}, strategy_, searchDepth_, searchTime_, simplification_List, repl_Integer] :=
	Module[ {po, pv, pt, pTree, subsP, fileID, file, log},
		{subsP, fileID, file, log} = openLog[ goal, repl];
		Block[ {$TMALogFile = log},
			writeLog[ "Proof run initiated from GUI"];
			$addProofKB = {};
			{pv, po, pTree, pt} = callProver[ rules, strategy, goal, kb, searchDepth, searchTime];
		
			(* Update GUI and proof object w.r.t. knowledge that was added during proof *)
			$selectedProofKB = DeleteDuplicates[ Join[ kb, $addProofKB]];
			Scan[ With[ {fkey = key[ #]}, kbSelectProve[ fkey] = True]&, $addProofKB];
			If[ $addProofKB =!= {}, po = ReplacePart[ po, {1, 3, 1} -> Prepend[ $selectedProofKB, goal]]];
		
			(* At this point po is equal to the global $TMAproofObject and $TMAproofTree is the corresponding tree *)
			saveProofObject[ po, pTree, file];
			{po, pTree} = simplifyProof[ po, pTree, simplification, file];
			(* po is the simplified proof object and $TMAproofTree is the corresponding simplified tree, but $TMAproofObject is still the unsimplified object *)
			$TMAproofObject = po;
			$TMAproofTree = pTree;
			printProveInfo[ DeleteDuplicates[ Map[ {key[#], label[#]}&, $selectedProofKB]], pv, pt, simplification, {subsP, fileID, file}];
			writeLog[ StringForm[ "Proof info written to ``.\nProof run finished.", CurrentValue[ $proofInitNotebook, "NotebookFullFileName"]]];
		];
		closeLog[ log];
	]
execProveCall[ args___] := unexpected[ execProveCall, {args}]

saveProofObject[ po_, pt_, file_String] :=
	Module[{},
		(* cleanup all proof object files from previous runs *)
		DeleteFile[ FileNames[ file <> "-po-*.m"]];
		Put[ {po, pt}, file <> "-po.m"];		
	]
saveProofObject[ args___] := unexpected[ saveProofObject, {args}]

openLog[ goal_FML$, repl_Integer] :=
	Module[{cellID, nbDir, subsP = repl, fileID, file, log},
		cellID = getCellIDFromKey[ key@goal];
		nbDir = createPerNotebookDirectory[ CurrentValue[ $proofInitNotebook, "NotebookFullFileName"]];
		If[ subsP === 0,
			(* This may occur if the prover tab has been skipped and $replexistProof still has init val 0 *)
			subsP = findNumExistingProofs[ $proofInitNotebook, goal] + 1;
		];
		fileID = "p" <> cellID <> "-" <> ToString[ subsP];
		file = FileNameJoin[ {nbDir, fileID}];
		log = OpenWrite[ file <> ".log"];
		{subsP, fileID, file, log}		
	]
openLog[ args___] := unexpected[ openLog, {args}]

closeLog[ file_OutputStream] :=
	Module[{},
		Close[ file]
	]	
closeLog[ args___] := unexpected[ closeLog, {args}]


addKnowledgeWhileProving[ new_List] :=
	(
		$addProofKB = DeleteDuplicates[ Join[ $addProofKB, new]];
	)
addKnowledgeWhileProving[ args___] := unexpected[ addKnowledgeWhileProving, {args}]

proofNavigation[ po_] :=
    Module[ {proofTree, geom, addControl},
    	If[ Length[ po] > 50 && $TMAproofSearchRunning,
    		proofTree = showProofNavigation[ po, Fit, $selectedSearchDepth, Automatic];
    		addControl = Graphics[ Table[{EdgeForm[Thick], ColorData["TemperatureMap"][ i/$selectedSearchDepth], 
    			Rectangle[ {i*360/($selectedSearchDepth+1), 0}, {(i + 1)*360/($selectedSearchDepth+1), 20}]}, {i, 0, $currentSearchLevel}],
    			PlotRange -> {{-0.1, 360}, {-0.1, 20.1}}, ImageSize -> {360, 20}],
    	(* else *)
    		proofTree = showProofNavigation[ po, $proofTreeScale, $selectedSearchDepth, All];
    		addControl = ButtonBar[ {Tooltip[ "+", translate[ "zoom in"]] :> ($proofTreeScale *= 2), 
        		Tooltip[ "\[FivePointedStar]", translate[ "optimal size"]] :> ($proofTreeScale = 1), 
        		Tooltip[ "\[DottedSquare]", translate[ "fit into window"]] :> ($proofTreeScale = Fit), 
        		Tooltip[ "-", translate[ "zoom out"]] :> ($proofTreeScale /= 2)},
        		FrameMargins -> {{15, 15}, {2, 0}}];
    	];
    	geom = Replace[ ImageSize, Options[ proofTree, ImageSize]];
    	(* Putting the frame around the inner Pane is a work-around, otherwise the pane is not positioned correctly when the proof tree is higher than 420 *)
        Column[{
        	addControl,
        	Framed[ Pane[ proofTree,
        		{360, 510}, ImageSizeAction -> "Scrollable", Scrollbars -> Automatic, ScrollPosition -> {geom[[1]]/2-175, 0}], FrameStyle -> None],
        	Button[ translate["abort"], $proofAborted = True]
        	}, Center]	
    ]
proofNavigation[ args___] := unexpected[ proofNavigation, {args}]


(* ::Subsubsection:: *)
(* printComputationInfo *)


(* this function is called during a computation (see processComputation[])
   effect: print a cell containg information about the environment settings for that computation *)

printComputationInfo[ cellID_Integer, cache_, fn_String, cTime_] := 
	Module[ {nbDir, file, fileID},
		nbDir = createPerNotebookDirectory[ fn];
		(* Generate cache only in plain .m format, since this allows sharing notebooks with users on different platforms.
			Also, loading a .m-file allows dynamic objects to react to new settings, whereas loading a .mx-file has no effect on dynamics.
			I assume the speed gain from using mx is neglectable *)
		fileID = "c" <> ToString[ cellID];
		file = FileNameJoin[ {nbDir, fileID}];
		If[ cache,
			(* we generate new cache files only if needed *)
			saveComputationCacheDisplay[ cellID, file, cTime]
		];
		(* the comp info has to be written in any case, otherwise the old info is removed (GeneratedCell, CellAutoOverwrite) *)
		With[ {fnco = makeRelFilename[ fileID, "co.m"], fnd = makeRelFilename[ fileID, "display.m"]},
			CellPrint[ Cell[ 
				If[ TrueQ[ $traceUserDef],
					BoxData[ ToBoxes[ Button[ Style[ translate["ShowComputation"], FontVariations -> {"Underline" -> True}], 
						displayComputation[ ToExpression[ fnco]], ImageSize -> Automatic, Appearance -> None, Method -> "Queued"]]], 
					(* else *)
					""],
				"ComputationInfo",
				CellFrameLabels -> {
					{None, Cell[ BoxData[ ButtonBox[ "\[Times]", Evaluator -> Automatic, Appearance -> None, 
						With[ {f = fileID}, ButtonFunction :> removeGroup[ ButtonNotebook[], f]]]]]},
					{None, None}}]];
			(* This needs to be done in that complicated way, because saving formatted Theorema expressions to the file would result in syntax errors
			   when reading in the file later (Theorema MakeExpressions are not applied when reading from a file!).
			   Therefore, we must write something to the file, which is syntactically OK on the plain Mma-level and format it after reading the file *)
			CellPrint[ Cell[ BoxData[ ToBoxes[ Dynamic[ Refresh[ Get[ ToExpression[ fnd]] /. FORM -> displayFormulaFromKey,
				TrackedSymbols :> {$tmaEnv}]]]], "ComputationInfoBody"]]
		];
	]
printComputationInfo[ args___] := unexcpected[ printComputationInfo, {args}]
     
setComputationEnvironment[ file_String] :=
	Module[ {fn = file <> ".m"},
		If[ FileExistsQ[ fn],
			Clear[ kbSelectCompute];
			Get[ fn];
			Apply[ Clear, Map[ # <> "*"&, $allCurrentComputationContexts]];
			fn = file <> ".mx";
			If[ FileExistsQ[ fn],
				Get[ fn]
			];
			(* whether to cache the computation environment: if we use existing caches, we will not re-generate them later *)
			False,
			(* else *)
			(* whether to cache the computation environment, default=True *)
			True
		]
	]
setComputationEnvironment[ args___] := unexpected[ setComputationEnvironment, {args}]

saveComputationCacheDisplay[ cellID_Integer, file_String, cTime_] :=
	With[ {fn = file <> ".m", fc = file <> ".mx", kbKeysLabels = Map[ {key[#], label[#]}&, Select[ $tmaEnv, kbSelectCompute[ key[ #]]&]]},
		Put[ $TmaComputationObject, file <> "-co.m"];
		$allCurrentComputationContexts = Join[ {"Theorema`Computation`Knowledge`"}, 
			Map[ StringReplace[ #, "Theorema`Knowledge`" -> "Theorema`Computation`Knowledge`", 1]&, $TheoremaArchives]];
		Put[ Definition[ buiActComputation], Definition[ kbSelectCompute], Definition[ $traceUserDef], Definition[ $allCurrentComputationContexts],
			 Definition[ $tmaEnv], Definition[ $kbStruct], Definition[ $tcKBBrowseSelection], fn];
		(* we save all computation contexts into an mx-cache file that can be loaded quickly (dynamics need not react to that *)
		DumpSave[ fc, Evaluate[ $allCurrentComputationContexts]];
		Put[ 
			TabView[ {
				translate[ "tcComputeTabKBTabLabel"] -> Pane[ Row[ Map[ FORM, kbKeysLabels], ", "], 500],
        		translate[ "tcComputeTabBuiltinTabLabel"] -> summarizeBuiltins[ "compute"],
        		translate[ "Computation"] -> summarizeComputationSettings[ cTime],
        		translate[ "RestoreSettings"] -> Row[ {translate[ "RestoreSettingsLong"], Button[ translate[ "OK"], setComputationEnvironment[ file]]}, Spacer[5]]
				},
				ImageSize -> Automatic
			],
			file <> "-display.m"];
	]	
saveComputationCacheDisplay[ args___] := unexpected[ saveComputationCacheDisplay, {args}]

summarizeComputationSettings[ cTime_] :=
	TabView[
		{
			translate[ "input"] -> 	DisplayForm[ $TmaComputationObject[[1]]],
			(* Out[] is the result of the computation translated to standard context, not anymore Computation`-context.
			   This ensures that no evaluations will happen even when displaying the result under different built-in settings. *)
			translate[ "result"] -> theoremaDisplay[ Out[]],
			translate[ "statistics"] -> Column[{
    			Labeled[ cTime, translate[ "computationTime"] <> ":", Left]
    			}]
		},
		AutoAction -> True,
		ControlPlacement -> Left
	]
summarizeComputationSettings[ args___] := unexpected[ summarizeComputationSettings, {args}]

displayFormulaFromKey[ {k_List, l_String}] :=
	Module[ {form},
		form = Select[ $tmaEnv, key[ #] === k&];
		If[ form === {},
			Button[ Tooltip[ Style[ "?" <> l <> "?", "TabView"], translate[ "notEval"]], evalFormulaFromKey[ k], Appearance -> None],
			form = form[[1]];
			Tooltip[ l, theoremaDisplay[ formula@form]]
		]
	]
displayFormulaFromKey[ args___] := unexpected[ displayFormulaFromKey, {args}]

evalFormulaFromKey[ k_List] :=
	Module[ { file = Part[ StringSplit[ k[[2]], ":"], 2], nb},
		nb = NotebookOpen[ file];
		NotebookFind[ nb, "GlobalDeclaration", All, CellStyle];
		FrontEndTokenExecute[ "EvaluateCells"];
        NotebookFind[ nb, k[[1]], All, CellTags];
        FrontEndTokenExecute[ "EvaluateCells"];
       ]
evalFormulaFromKey[ args___] := unexpected[ evalFormulaFromKey, {args}]

makeRelFilename[ base_String, id_String] := 
	ToString[ StringForm[ 
		"FileNameJoin[{CurrentValue[\"NotebookDirectory\"], FileBaseName[CurrentValue[\"NotebookFileName\"]], \"``-``\"}]", base, id]
	]
makeRelFilename[ base_String] :=
	ToString[ StringForm[ 
		"FileNameJoin[{CurrentValue[\"NotebookDirectory\"], FileBaseName[CurrentValue[\"NotebookFileName\"]], \"``\"}]", base]
	]
makeRelFilename[ args___] := unexpected[ makeRelFilename, {args}]


(* ::Subsubsection:: *)
(* printProofInfo *)


printProveInfo[ kbKeysLabels_, pVal_, pTime_, simplification_List, {subsP_Integer, fileID_String, file_String}] := 
	Module[ {},
		saveProveCacheDisplay[ kbKeysLabels, pTime, file];
        If[ NotebookFind[ $proofInitNotebook, makeProofIDTag[ $selectedProofGoal] <> "-" <> ToString[ subsP], All, CellTags] === $Failed,
        	(* no replacement of existing proof -> new proof *)
        	If[ NotebookFind[ $proofInitNotebook, makeProofIDTag[ $selectedProofGoal] <> "-" <> ToString[ subsP-1], All, CellTags] === $Failed,
        		(* there are no proofs for this goal -> put after env *)
				NotebookFind[ $proofInitNotebook, id@$selectedProofGoal, All, CellTags];
				NotebookFind[ $proofInitNotebook, "CloseEnvironment", Next, CellStyle];
				SelectionMove[ $proofInitNotebook, After, CellGroup],
				(* there are already proofs for this goal *)
				SelectionMove[ $proofInitNotebook, All, CellGroup];
				SelectionMove[ $proofInitNotebook, After, CellGroup]
        	],
        	(* replace existing -> select group to overwrite *)
			SelectionMove[ $proofInitNotebook, All, CellGroup]
		];
		SetSelectedNotebook[ $proofInitNotebook];
		With[ {fnpo = makeRelFilename[ fileID], fnd = makeRelFilename[ fileID, "display.m"]},
        	NotebookWrite[ $proofInitNotebook, Cell[ TextData[ {Cell[ BoxData[ ToBoxes[ proofStatusIndicator[ pVal]]]], " " <> translate[ "Proof of"] <> " ",
        		formulaReference[ $selectedProofGoal], " #" <> ToString[ subsP] <> ":   ",
				Cell[ BoxData[ ToBoxes[ Dynamic[ Refresh[ displayProofButtons[ ToExpression[ fnpo]], UpdateInterval -> 4]]]]]}],
        		"ProofInfo",
        		CellTags -> With[ {pTag = makeProofIDTag[ $selectedProofGoal]}, {pTag, pTag <> "-" <> ToString[ subsP]}],
        		CellFrameLabels -> {{None, Cell[ BoxData[ ButtonBox[ "\[Times]", Evaluator -> Automatic, Appearance -> None, 
        			With[ {f = fileID}, ButtonFunction :> removeGroup[ ButtonNotebook[], f]]]]]}, {None, None}}]];
			NotebookWrite[ $proofInitNotebook, Cell[ BoxData[ ToBoxes[ Dynamic[ Refresh[ Get[ ToExpression[ fnd]] /. FORM -> displayFormulaFromKey, TrackedSymbols :> {$tmaEnv}]]]], "ProofInfoBody"]]
		]
	]

printProveInfo[args___] := unexcpected[ printProveInfo, {args}]

displayProofButtons[ fn_String] :=
	Module[ {simpFile = FileNames[ fn <> "-po-*.m"]},
		If[ simpFile === {},
			(* there are no stored simplified proofs *)
			Button[ Style[ translate["ShowProof"], FontVariations -> {"Underline" -> True}], 
					displayProof[ fn, {False, False, False}], ImageSize -> Automatic, Appearance -> None, Method -> "Queued"],
			(* else: there are stored simplified proofs, offer a button for opening the most simplified version available *)
			If[ FileExistsQ[ fn <> "-po-fav.m"],
				simpFile = {fn <> "-po-" <> ToString[ Get[ fn <> "-po-fav.m"]] <> ".m"}
			];
			With[ {sl = IntegerDigits[ ToExpression[ First[ StringCases[ Last[ simpFile], __ ~~ "-po-" ~~ x_ ~~ ".m" -> x, 1]]], 2] /. {1 -> True, 0 -> False}},
		    	Row[ {Button[ Style[ translate["ShowSimplifiedProof"], FontVariations -> {"Underline" -> True}], 
					displayProof[ fn, sl], ImageSize -> Automatic, Appearance -> None, Method -> "Queued"],
			      Button[ Style[ translate["ShowFullProof"], FontVariations -> {"Underline" -> True}], 
					displayProof[ fn, {False, False, False}], ImageSize -> Automatic, Appearance -> None, Method -> "Queued"]}, Spacer[3]]
			]
		]  
	]
displayProofButtons[ args___] := unexpected[ displayProofButtons, {args}]

removeGroup[ nb_NotebookObject, base_String] :=
	Module[ {},
		(* remove all .m-files. 
		   Could be specified more precisely using string patterns or regexp, but this crashes under Linux (at least in Mma 8) *)
		DeleteFile[ FileNames[ FileNameJoin[ {CurrentValue[ nb, "NotebookDirectory"], FileBaseName[ CurrentValue[ nb, "NotebookFileName"]], base <> "*.m"}]]];
		DeleteFile[ FileNameJoin[ {CurrentValue[ nb, "NotebookDirectory"], FileBaseName[ CurrentValue[ nb, "NotebookFileName"]], base <> ".log"}]];
		SelectionMove[ nb, All, ButtonCell];
		SelectionMove[ nb, All, CellGroup];
		NotebookDelete[ nb];
	]
removeGroup[][ args___] := unexpected[ removeGroup[], {args}]

setProveEnv[ file_String] :=
	Module[ {},
		Clear[ kbSelectProve, ruleActive];
		Get[ file];
	]
setProveEnv[ args___] := unexpected[ setProveEnv, {args}]

makeProofIDTag[ f_FML$] := "Proof|" <> id@f
makeProofIDTag[ args___] := unexpected[ makeProofIDTag, {args}]

saveProveCacheDisplay[ kbKeysLabels_, pTime_, file_String] :=
	With[ {fn = file <> ".m"},
		(* Generate cache only in plain .m format, since this allows sharing notebooks with users on different platforms.
			Also, loading a .m-file allows dynamic objects to react to new settings, whereas loading a .mx-file has no effect on dynamics.
			I assume the speed gain from using mx is neglectable *)
		Apply[ Put[ ##, fn]&, Map[ Definition, $allProveSettings]];
		PutAppend[ Definition[ $tmaEnv], Definition[ $kbStruct], fn];
		Put[ 
			TabView[ {
				translate[ "tcProveTabKBTabLabel"] -> Pane[ Row[ Map[ FORM, kbKeysLabels], ", "], 500],
        		translate[ "tcProveTabBuiltinTabLabel"] -> summarizeBuiltins[ "prove"],
        		translate[ "tcProveTabProverTabLabel"] -> summarizeProverSettings[ pTime],
        		translate[ "RestoreSettings"] -> Row[ {translate[ "RestoreSettingsLong"], Button[ translate[ "OK"], setProveEnv[ fn]]}, Spacer[5]]
				},
				ImageSize -> Automatic
			],
			file <> "-display.m"];
	]
saveProveCacheDisplay[ args___] := unexpected[ saveProveCacheDisplay, {args}]

summarizeProverSettings[ pTime_] :=
	Module[{},
		TabView[{				
				translate[ "selectedRules"] -> displaySelectedRules[ $selectedRuleSet],
				translate[ "pStrat"] -> $selectedStrategy /. $registeredStrategies,
				translate[ "sLimits"] -> Column[{
    					Labeled[ $selectedSearchDepth, translate[ "sDepth"] <> ":", Left],
    					Labeled[ $selectedSearchTime, translate[ "sTime"] <> ":", Left]
    				}],
				translate[ "pSimp"] -> Column[{
    					If[ TrueQ[ $eliminateBranches], translate[ "elimBranches"], Sequence[]],
    					If[ TrueQ[ $eliminateSteps], translate[ "elimSteps"], Sequence[]],
    					If[ TrueQ[ $eliminateFormulae], translate[ "elimForm"], Sequence[]]
    				}],
    			translate[ "pInteractive"] -> Column[{
    					If[ TrueQ[ $interactiveProofSitSel], translate[ "interactiveProofSitSel"], Sequence[]],
    					If[ TrueQ[ $interactiveNewProofSitFilter], translate[ "interactiveNewProofSitFilter"], Sequence[]],
    					If[ TrueQ[ Map[ ruleActive, And[ existsGoalInteractive, forallKBInteractive]]], translate[ "interactiveInstantiate"], Sequence[]]
    				}],
    			translate[ "proofCellStatus"] -> Switch[ $proofCellStatus,
						Automatic, translate[ "auto"],
						Open, translate[ "open"],
						Closed, translate[ "closed"]
					],
				translate[ "statistics"] -> Column[{
    					Labeled[ pTime, translate[ "proofFindTime"] <> ":", Left],
    					Labeled[ DateString[ {"DayName", ", ", "Year", "-", "Month", "-", "Day", ", ", "Hour24", ":", "Minute", ":", "Second"}], translate[ "TimeStamp"] <> ":", Left]
    				}]
			}, AutoAction -> True, ControlPlacement -> Left]
	]
summarizeProverSettings[ args___] := unexpected[ summarizeProverSettings, {args}]


(* ::Section:: *)
(* Palettes *)


insertNewEnv[ type_String] :=
    Module[ {nb = InputNotebook[]},
        NotebookWrite[
         nb, {newOpenEnvCell[],
          newEnvHeaderCell[ type],
          newFormulaCell[ type],
          newEndEnvCell[],
          newCloseEnvCell[]}];
    ]
insertNewEnv[ args___] :=
    unexpected[ insertNewEnv, {args}]

openNewEnv[ type_String] :=
    Module[ {},
        NotebookWrite[ InputNotebook[], newOpenEnvCell[]];
        NotebookWrite[ InputNotebook[], newEnvHeaderCell[ type]];
    ]
openNewEnv[ args___] :=
    unexpected[openNewEnv, {args}]

insertNewFormulaCell[ style_String] := 
	Module[{}, 
		NotebookWrite[ InputNotebook[], newFormulaCell[ style]];
		(* we use NotebookFind because parameter Placeholder in NotebookWrite does not work (Mma 8.0.1) *)
		NotebookFind[ InputNotebook[], "\[SelectionPlaceholder]", Previous];
	]
insertNewFormulaCell[ args___] :=
    unexpected[ insertNewFormulaCell, {args}]

closeEnv[] :=
    Module[ {},
        NotebookWrite[ InputNotebook[], {newEndEnvCell[], newCloseEnvCell[]}];
    ]
closeEnv[ args___] :=
    unexpected[ closeEnv, {args}]

newFormulaCell[ "COMPUTE"] = Cell[ BoxData[ "\[SelectionPlaceholder]"], "Computation"]	
newFormulaCell[ "DECLARATION"] = Cell[ BoxData[ "\[SelectionPlaceholder]"], "GlobalDeclaration"]	
newFormulaCell[ style_, label_:$initLabel] = Cell[ BoxData[ "\[SelectionPlaceholder]"], "FormalTextInputFormula", CellTags -> {label}]	
newFormulaCell[ args___] := unexpected[ newFormulaCell, {args}]

newOpenEnvCell[] := Cell[ "", "OpenEnvironment"]
newOpenEnvCell[ args___] := unexpected[ newOpenEnvCell, {args}]

newEnvHeaderCell[ type_String] := Cell[ type <> " (\[Ellipsis])", "EnvironmentHeader",
	CellFrameLabels -> {{None, 
    	Cell[ BoxData[ ButtonBox[ "\[Times]", Evaluator -> Automatic, Appearance -> None,
    		ButtonFunction :> removeEnvironment[ ButtonNotebook[]]]]]}, {None, None}}]
newEnvHeaderCell[ args___] := unexpected[ newEnvHeaderCell, {args}]

newEndEnvCell[] := Cell[ "\[GraySquare]", "EndEnvironmentMarker"]
newEndEnvCell[ args___] := unexpected[ newEndEnvCell, {args}]

newCloseEnvCell[] := Cell[ "", "CloseEnvironment"]
newCloseEnvCell[ args___] := unexpected[ newCloseEnvCell, {args}]


(* ::Subsection:: *)
(* Buttons *)


makeNbNewButton[] :=
	Button[ translate[ "New"],
		createNbRememberLocation[ Magnification -> CurrentValue[ getTheoremaCommander[], Magnification]],
		Alignment -> {Left, Top}, Method -> "Queued"]
makeNbNewButton[ args___] := unexpected[ makeNbNewButton, {args}]

makeNbOpenButton[ ] :=
	Button[ translate["Open"],
		openNbRememberLocation[ Magnification -> CurrentValue[ getTheoremaCommander[], Magnification]],
		Method -> "Queued"
	]
makeNbOpenButton[ args___] := unexpected[ makeNbOpenButton, {args}]
		

envButtonData[ "DEF"] := "tcSessTabEnvTabButtonDefLabel";
envButtonData[ "THM"] := "tcSessTabEnvTabButtonThmLabel";
envButtonData[ "LMA"] := "tcSessTabEnvTabButtonLmaLabel";
envButtonData[ "PRP"] := "tcSessTabEnvTabButtonPrpLabel";
envButtonData[ "COR"] := "tcSessTabEnvTabButtonCorLabel";
envButtonData[ "ALG"] := "tcSessTabEnvTabButtonAlgLabel";
envButtonData[ "EXM"] := "tcSessTabEnvTabButtonExmLabel";
envButtonData[ args___] := unexpected[envButtonData, {args}]

makeEnvButton[ bname_String] :=
    With[ { bd = If[ bname === "?", "?", translate[ envButtonData[ bname]]]},
		Button[ bd, insertNewEnv[ bd], Alignment -> Center]
    ]
makeEnvButton[args___] := unexpected[makeEnvButton, {args}]

makeFormButton[] := Button[ translate[ "New"], insertNewFormulaCell[ "Env"], Alignment -> {Left, Top}, ImageSize -> Automatic]
makeFormButton[args___] := unexpected[ makeFormButton, {args}]

makeGroupUngroupButton[ ] := Tooltip[ 
	Button[ translate[ "group/ungroup"],
		(* ShiftKey is not recognized inside Button in Mma 10 on Linux. Worked in Mma 8/9. Needs to be checked on other platforms. WW 5.7.2016 *)
		If[ CurrentValue[ "ShiftKey"],
			FrontEndExecute[ {NotebookWrite[ InputNotebook[], removeAutoParen[ NotebookRead[ InputNotebook[]]], Placeholder]}],
			(* else *)
			FrontEndExecute[ {NotebookApply[ InputNotebook[], RowBox[ {autoParenthesis[ "("], "\[SelectionPlaceholder]", autoParenthesis[ ")"]}], Placeholder]}]
		]
	], translate[ "tooltipButtonGroupUngroup"], TooltipDelay -> 0.5
]
makeGroupUngroupButton[ args___] := unexpected[ makeGroupUngroupButton, {args}]

makeQuoteUnquoteButton[ ] := Tooltip[
	Button[ translate[ "quote/unquote"],
		If[ CurrentValue[ "ShiftKey"],
			FrontEndExecute[ {NotebookWrite[ InputNotebook[], Replace[ NotebookRead[ InputNotebook[]], RowBox[ {"\[OpenCurlyQuote]", expr_, "\[CloseCurlyQuote]"}] :> expr], Placeholder]}],
			(* else *)
			FrontEndExecute[ {NotebookApply[ InputNotebook[], RowBox[ {"\[OpenCurlyQuote]", "\[SelectionPlaceholder]", "\[CloseCurlyQuote]"}], Placeholder]}]
		]
	], translate[ "tooltipButtonQuoteUnquote"], TooltipDelay -> 0.5
]
makeGroupUngroupButton[ args___] := unexpected[ makeGroupUngroupButton, {args}]

removeAutoParen[ RowBox[ {TagBox[ "(", "AutoParentheses"], expr_, TagBox[ ")", "AutoParentheses"]}]] := expr
removeAutoParen[ expr_] := expr
removeAutoParen[ args___] := unexpected[ removeAutoParen, {args}]


makeNewDeclButton[] :=
    Button[ translate[ "New"], insertNewFormulaCell[ "DECLARATION"], Alignment -> {Left, Top}, ImageSize -> Automatic]
makeNewDeclButton[args___] := unexpected[ makeNewDeclButton, {args}]


makeDeclButtons[] := Row[ Map[ makeDeclBut, {"VAR", "VARCOND", "COND", "ABBREV"}], Spacer[5]]
makeDeclButtons[args___] := unexpected[ makeDeclButtons, {args}]

displayDecl[ ] :=
	Column[{
		Row[ {
			Pane[ $TMAactDecl, {350, {10, 100}}, ImageSizeAction -> "Scrollable", Scrollbars -> Automatic],
			Tooltip[ Button[ Style[ "\:21ba", {Medium}], $TMAactDecl = displayGlobalDeclarations[ InputNotebook[]]], translate[ "tcSessTabEnvTabButtonDeclLabel"]]
			}, Spacer[3]],
		Row[ {
			PopupMenu[ Dynamic[ $activeNB], Map[ # -> FileNameTake[ #]&, allTmaNotebooks[]]],
			Tooltip[ Button[ translate[ "resyncGlobal"], resyncGlobals[ $activeNB]], translate[ "resyncGlobalTooltip"]]}, Spacer[3]]
	}]
displayDecl[ args___] := unexpected[ displayDecl, {args}]

declButtonData["VAR"] := 
	{
		DisplayForm[ UnderscriptBox[ "\[ForAll]", SelectionPlaceholder[ "rg"]]], 
		UnderscriptBox[ "\[ForAll]", "\[SelectionPlaceholder]"],
		translate[ "GVARTooltip"]
	}

declButtonData["VARCOND"] := 
	{
		DisplayForm[ UnderscriptBox[ UnderscriptBox[ "\[ForAll]", SelectionPlaceholder[ "rg"]], Placeholder[ "cond"]]],
		UnderscriptBox[ UnderscriptBox[ "\[ForAll]", "\[SelectionPlaceholder]"], "\[Placeholder]"],
		translate[ "GVARCONDTooltip"]
	}

declButtonData["COND"] := 
	{
		DisplayForm[ RowBox[ {SelectionPlaceholder[ "cond"], "\[DoubleRightArrow]"}]],
		RowBox[ {"\[SelectionPlaceholder]", "\[Implies]"}],
		translate[ "GCONDTooltip"]
	}

declButtonData["ABBREV"] := 
	{
		DisplayForm[ UnderscriptBox[ "let", RowBox[ {SelectionPlaceholder[ "v"], "=", Placeholder[ "\[Ellipsis]"]}]]], 
		UnderscriptBox[ "let", RowBox[ {"\[SelectionPlaceholder]", "=", "\[Placeholder]"}]],
		translate[ "GABBREVTooltip"]
	}

makeDeclBut[ bname_String] := makeDeclBut[ bname, "GlobalDeclaration"]
	
makeDeclBut[ bname_String, style_String] :=
    With[ { bd = declButtonData[ bname]},
			Tooltip[ Button[ bd[[1]], 
				(* Should check CurrentValue["SelectionData"] to find out what is currently selected *)
				FrontEndExecute[
					NotebookApply[ InputNotebook[], bd[[2]], Placeholder];
					(*NotebookApply[ InputNotebook[], Cell[ BoxData[ bd[[2]]], style], Placeholder];
					If[ MatchQ[ NotebookRead[ InputNotebook[]], _Cell],
						SelectionMove[ InputNotebook[], All, CellContents]
					]*)
				],
				Appearance -> "DialogBox", Alignment -> {Left, Top}, ImageSize -> All],
				bd[[3]], TooltipDelay -> 0.5]
    ]
makeDeclBut[args___] := unexpected[ makeDeclBut, {args}]

displayEnv[ ] :=
	If[ $tmaEnv === {},
		emptyPane[ "", {350, 30}],
		Pane[ Column[ displayLabeledFormulaList[ $tmaEnv], Left, 0.2], {380, {10, 400}}, ImageSizeAction -> "Scrollable", Scrollbars -> Automatic]
	]
displayEnv[ args___] := unexpected[ displayEnv, {args}]
   
allEnvironments = {"DEF", "THM", "LMA", "PRP", "COR", "ALG", "EXM", "?"};

sessionCompose[] :=
    Column[{
    	Labeled[ Row[ {makeNbNewButton[], makeNbOpenButton[]}, Spacer[5]],
    		translate[ "Notebooks"], {{Top, Left}}],
    	Labeled[ Grid[ Partition[ Map[ makeEnvButton, allEnvironments], 4]],
    		translate[ "Environments"], {{Top, Left}}],
    	Labeled[ Column[ {Row[ {makeFormButton[], makeGroupUngroupButton[], makeQuoteUnquoteButton[]}, Spacer[5]],
    				Dynamic[ Refresh[ langButtons[], TrackedSymbols :> {$buttonNat, $tcLangButtonSelection}]]}, Left, Spacer[2]],
    		translate[ "Formulae"], {{Top, Left}}],
    	Labeled[ Column[ {makeNewDeclButton[], makeDeclButtons[]}, Left, Spacer[2]],
    		translate[ "Declarations"], {{Top, Left}}]
    }]
sessionCompose[args___] :=
    unexpected[sessionCompose, {args}]

sessionInspect[ ] :=
	Column[{
    	Labeled[ Column[ {Dynamic[ displayEnv[]]}, Left, Spacer[2]],
    		translate[ "Formulae"], {{Top, Left}}],
    	Labeled[ Column[ {Dynamic[ displayDecl[]]}, Left, Spacer[2]],
    		translate[ "Declarations"], {{Top, Left}}]
    }]
sessionInspect[ args___] := unexpected[ sessionInspect, {args}]


(* ::Section:: *)
(* Archives Tab *)


sessionArchive[] :=
    Column[{
        Labeled[ Column[{
            Row[ {makeArchCreateButton[], makeArchNewButton[]}, Spacer[2]],
            Row[ {makeArchInfoButton[], makeArchCloseButton[]}, Spacer[2]]}], translate[ "tcLangTabArchTabSectionCreate"], {{Top, Left}}],
        Labeled[ Column[{
            makeArchLoadButton[]}], translate[ "tcLangTabArchTabSectionLoad"], {{Top, Left}}],
        Labeled[ Column[{
            makeArchExportSelection[]}], translate[ "tcLangTabArchTabSectionExport"], {{Top, Left}}]
    }]
sessionArchive[args___] := unexpected[sessionArchive, {args}]

makeArchCreateButton[] :=
	Button[ translate[ "New"], 
		insertNewArchive[ NotebookCreate[ StyleDefinitions -> makeColoredStylesheet[ "Notebook"]]], Alignment -> {Left, Top}, Method -> "Queued"]
makeArchNewButton[args___] := unexpected[makeArchNewButton, {args}]

makeArchNewButton[] :=
	Button[ translate["tcLangTabArchTabButtonMakeLabel"], 
		insertNewArchive[ InputNotebook[]], Alignment -> {Left, Top}, Method -> "Queued"]
makeArchNewButton[args___] := unexpected[makeArchNewButton, {args}]

makeArchInfoButton[] :=
	Button[ translate["tcLangTabArchTabButtonInfoLabel"], 
		insertArchiveInfo[], Alignment -> {Left, Top}]
makeArchInfoButton[args___] := unexpected[makeArchInfoButton, {args}]

makeArchCloseButton[] :=
	Button[ translate["tcLangTabArchTabButtonCloseLabel"], 
		insertCloseArchive[], Alignment -> {Left, Top}]
makeArchCloseButton[args___] := unexpected[makeArchCloseButton, {args}]

insertNewArchive[ nb_NotebookObject] :=
	Module[{},
		SelectionMove[nb, Before, Notebook];
		NotebookWrite[nb, archiveOpenCell[]];
		insertArchiveInfo[];
		If[ NotebookFind[nb, "CloseArchive", All, CellStyle] === $Failed,
			SelectionMove[nb, After, Notebook];
			insertCloseArchive[];
		];
		NotebookFind[nb, "OpenArchive", All, CellStyle]
	]
insertNewArchive[args___] := unexpected[insertNewArchive, {args}]

insertArchiveInfo[] := NotebookWrite[ InputNotebook[], archiveInfoCells[]]
insertArchiveInfo[args___] := unexpected[insertArchiveInfo, {args}]

insertCloseArchive[] := NotebookWrite[ InputNotebook[], archiveCloseCells[]]
insertCloseArchive[args___] := unexpected[insertCloseArchive, {args}]

archiveOpenCell[] := 
	Module[ {name, input=""},
		name = DialogInput[ 
			Column[{ 
				translate["archiveNameDialogField"],
				InputField[ Dynamic[ input], String, FieldHint -> translate["archiveNameDialogHint"]],
				ChoiceButtons[ {DialogReturn[ input], DialogReturn[ ""]}]}]];
		If[ name === "" || StringTake[ name, -1] =!= "`",
			name = name <> "`"
		]; 
		Cell[ BoxData["\"\<" <> name <> "\>\""], "OpenArchive", CellFrameLabels->{{translate["archLabelName"], None}, {None, translate["archLabelBegin"]}}]
	]
archiveOpenCell[args___] := unexpected[archiveOpenCell, {args}]

archiveInfoCells[] := {
	Cell[ BoxData[RowBox[{"{","}"}]], "ArchiveInfo", CellFrameLabels->{{translate["archLabelNeeds"], None}, {None, None}}],
	Cell[ BoxData[RowBox[{"{","}"}]], "ArchiveInfo", CellFrameLabels->{{translate["archLabelPublic"], None}, {None, None}}]}
archiveInfoCells[args___] := unexpected[archiveInfoCells, {args}]

archiveCloseCells[] := Cell["\[FilledUpTriangle]", "CloseArchive", CellFrameLabels->{{None, None}, {translate["archLabelEnd"], None}}]
archiveCloseCells[args___] := unexpected[archiveCloseCells, {args}]

makeArchLoadButton[] :=
    DynamicModule[ {arch = $TheoremaArchiveDirectory},
        Column[{
            Dynamic[showSelectedArchives[arch]], 
            Row[ {FileNameSetter[Dynamic[arch], "OpenList", {translate["fileTypeArchive"]->{"*.ta"}}, Appearance -> translate["tcLangTabArchTabButtonSelectLabel"]],
            	Button[ translate["tcLangTabArchTabButtonLoadLabel"], (If[ loadInPlace, loadArchiveInPlace[ arch], loadArchive[ arch]];arch=$TheoremaArchiveDirectory;), Alignment -> {Left, Top}],
            	Row[ {Checkbox[ Dynamic[ loadInPlace]], translate[ "in place"]}, Spacer[1]]}, Spacer[2]]}]
    ]
makeArchLoadButton[args___] := unexpected[makeArchLoadButton, {args}]

showSelectedArchives[ l_List] :=
    Pane[ Column[ Map[ Style[ archiveName[ #, Short], LineBreakWithin -> False]&, l]], ImageSize -> {200,20*Length[l]}, Scrollbars -> Automatic]
showSelectedArchives[ s_String] :=
    translate["tcLangTabArchTabNoArchSel"]
showSelectedArchives[args___] := unexpected[showSelectedArchives, {args}]

loadArchiveInPlace[ arch_List] := 
	Module[ {archNames = Map[ archiveName[ #, Short]&, arch]},
		NotebookWrite[ InputNotebook[], Cell[ BoxData[ ToBoxes[ archNames]], "IncludeArchive"], All];
		SelectionEvaluate[ InputNotebook[]]
	]
loadArchiveInPlace[ args___] := unexpected[ loadArchiveInPlace, {args}]

makeArchExportSelection[ ] :=
	Row[ {Checkbox[ Dynamic[ $omdocExport]], translate[ "OmDoc"]}, Spacer[2]]
makeArchExportSelection[ args___] := unexpected[ makeArchExportSelection, {args}]

(* ::Section:: *)
(* Preferences Tab *)


setPreferences[ ] :=
	Column[ {
	Column[ {
		Labeled[ PopupMenu[ Dynamic[ $TmaLanguage], availableLanguages[]], translate[ "tcPrefLanguage"], {{Top, Left}}],
		Labeled[ Row[ {Dynamic[ Tooltip[ FileNameJoin[ Take[ FileNameSplit[$TheoremaArchiveDirectory], -2]], $TheoremaArchiveDirectory]],
				FileNameSetter[Dynamic[$TheoremaArchiveDirectory], "Directory"]}, Spacer[10]], translate["tcPrefArchiveDir"], {{Top, Left}}],
		Labeled[ Row[{PopupMenu[ Dynamic[ $TheoremaColorScheme], $availableColorSchemes, BaselinePosition -> Center], 
    				  Dynamic[ TMAcolorScheme[ $TheoremaColorScheme, ImageSize -> {28, 28}, BaselinePosition -> Center]],
    				  Button[ translate[ "apply color scheme"], applyColorScheme[ ], BaselinePosition -> Center]}, Spacer[2]], 
    		translate[ "tcPrefAppearColorSchemes"], {{Top, Left}}],
		Labeled[ Row[{Checkbox[ Dynamic[ $suppressWelcomeScreen]], translate["tcPrefAppearSuppressWelcome"]}, Spacer[2]], 
    		translate[ "tcPrefAppearWelcome"], {{Top, Left}}],
		Labeled[ Grid[{{RadioButton[Dynamic[$buttonNat], False], translate["tcSessTabMathTabBSform"], 
			RadioButton[Dynamic[$buttonNat], True], translate["tcSessTabMathTabBSnat"]}}, Spacings -> {{{4, 0.5}}, Automatic}], 
    		translate["tcSessTabMathTabBS"], {{Top, Left}}]
    	}],
    	Spacer[{1,230}],
		savePreferencesButton[]
	}
	]
setPreferences[ args___] := unexpected[ setPreferences, {args}]

applyColorScheme[ ] :=
	Module[{},
		closeTheoremaCommander[];
		openTheoremaCommander[];
		Map[ SetOptions[ #, StyleDefinitions -> makeColoredStylesheet[ "Notebook"]]&,
			Select[ Notebooks[], isTheoremaNotebook]];
	]

applyColorScheme[ args___] := unexpected[ applyColorScheme, {args}]

makeColoredStylesheet[ type_String, color_:$TheoremaColorScheme] :=
	Module[{tmp, styles, alias},
		tmp = NotebookOpen[ 
			FileNameJoin[ {$TheoremaDirectory, "Theorema", "Interface", "Templates", type <> "-Template.nb"}],
			Visible -> False];
		styles = NotebookGet[ tmp];
		NotebookClose[ tmp];
		alias = Cases[ Flatten[ Transpose[ allFormulae][[2]], 2],
					{n_String, i_Integer} :>
						With[ {bd = langButtonData[ n]},
							If[ i === 1,
								bd[[4]] -> RowBox[ {autoParenthesis[ "("], bd[[2]], autoParenthesis[ ")"]}],
								bd[[4]] -> bd[[2]]
							]
						]
				];
		alias = Join[ alias, {"(" -> autoParenthesis[ "("], ")" -> autoParenthesis[ ")"]}];
		styles /. Table[Apply[CMYKColor, IntegerDigits[i, 2, 4]] -> TMAcolor[i, color], {i, 0, 15}]
				/. {(InputAliases -> {}) -> (InputAliases -> alias), "DOCKED_HEADER" -> "Theorema " <> If[ type === "Notebook", $TheoremaVersion, translate[ type]]}
	]
makeColoredStylesheet[ args___] := unexpected[ makeColoredStylesheet, {args}]

isTheoremaNotebook[ nb_NotebookObject] := Not[ FreeQ[ Options[ nb, CounterAssignments], "TheoremaFormulaCounter" -> _Integer]]
isTheoremaNotebook[ args___] := unexpected[ isTheoremaNotebook, {args}]


savePreferencesButton[ ] :=
    Module[ {prefsFile = FileNameJoin[ {$UserBaseDirectory, "Applications", "Theorema", "Kernel", "TheoremaPreferences.m"}]},
        $prefsSaveStatus = If[ FileExistsQ[ prefsFile],
        	DateString[ FileDate[ prefsFile]],
        	"\[LongDash]"];
        Column[{
        	Dynamic[ Refresh[ Row[{
        	translate[ "preferences last saved"] <> ": ",
            $prefsSaveStatus <> If[ {$TmaLanguage, $TheoremaArchiveDirectory, $TheoremaColorScheme, $suppressWelcomeScreen, $buttonNat} === $savedValues,
                                        " \[Checkmark]",
                                        ""
                                    ]}], TrackedSymbols :> {$TmaLanguage, $TheoremaArchiveDirectory, $TheoremaColorScheme, $suppressWelcomeScreen, $buttonNat, $prefsSaveStatus}]],
         Button[ translate[ "save current settings"], savePreferences[]]
        }, Center, ItemSize -> {28.2,1}, Dividers -> {{False}, 1 -> True}
        ]
    ]
savePreferencesButton[ args___] := unexpected[ savePreferencesButton, {args}]
    
savePreferences[ ] :=
	Module[{prefsDir = FileNameJoin[{$UserBaseDirectory, "Applications", "Theorema", "Kernel"}], prefsFile},
		prefsFile = FileNameJoin[{prefsDir, "TheoremaPreferences.m"}];
		If[ !DirectoryQ[ prefsDir],
			CreateDirectory[ prefsDir, CreateIntermediateDirectories -> True],
			(* else *)
			If[ FileExistsQ[ prefsFile],
				DeleteFile[ prefsFile]
			]
		];
		$savedValues = {$TmaLanguage, $TheoremaArchiveDirectory, $TheoremaColorScheme, $suppressWelcomeScreen, $buttonNat};
		Save[ prefsFile, {$TmaLanguage, $TheoremaArchiveDirectory, $TheoremaColorScheme, $suppressWelcomeScreen, $buttonNat, $savedValues}];
		$prefsSaveStatus = DateString[ FileDate[ FileNameJoin[{$UserBaseDirectory, "Applications", "Theorema", "Kernel", "TheoremaPreferences.m"}]]];
	]
savePreferences[ args___] := unexpected[ savePreferences, {args}]



(* ::Section:: *)
(* Math Tab *)

langButtonData[ "AND2"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "AND2"], 
			DisplayForm[ RowBox[ {TagBox[ FrameBox[ "left"], "SelectionPlaceholder"],
				"\[And]",
				TagBox[ FrameBox[ "right"], "Placeholder"]}]]],
		RowBox[ {"\[SelectionPlaceholder]", "\[And]", "\[Placeholder]"}],
		translate[ "CONN2Tooltip"],
		"and"
	}
	
langButtonData[ "AND3"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "AND3"], 
			DisplayForm[ RowBox[ {"\[And]", "\[Piecewise]", GridBox[{{TagBox[ FrameBox[ SubscriptBox[ "e", "1"]], "SelectionPlaceholder"]},
				{"\[VerticalEllipsis]"},
				{TagBox[ FrameBox[ SubscriptBox[ "e", "n"]], "Placeholder"]}}]}]]],
		RowBox[ {"\[And]", "\[Piecewise]", GridBox[ {{"\[SelectionPlaceholder]"}, {"\[Placeholder]"}}, ColumnAlignments -> Left]}],
		translate[ "CONNTooltip"],
		"andn"
	}
	
langButtonData[ "NOT"] := 
	{
		If[ $buttonNat, 
			translate[ "NOT"], 
			DisplayForm[ RowBox[ {"\[Not]",
				TagBox[ FrameBox[ "form"], "SelectionPlaceholder"]}]]],
		RowBox[ {"\[Not]", "\[SelectionPlaceholder]"}],
		translate[ "NOTTooltip"],
		"not"
	}

langButtonData[ "OR2"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "OR2"], 
			DisplayForm[ RowBox[ {TagBox[ FrameBox[ "left"], "SelectionPlaceholder"],
				"\[Or]",
				TagBox[ FrameBox[ "right"], "Placeholder"]}]]],
		RowBox[ {"\[SelectionPlaceholder]", "\[Or]", "\[Placeholder]"}],
		translate[ "CONN2Tooltip"],
		"or"
	}
	
langButtonData[ "OR3"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "OR3"], 
			DisplayForm[ RowBox[ {"\[Or]", "\[Piecewise]", GridBox[ {{TagBox[ FrameBox[ SubscriptBox[ "e", "1"]], "SelectionPlaceholder"]},
				{"\[VerticalEllipsis]"},
				{TagBox[ FrameBox[ SubscriptBox[ "e", "n"]], "Placeholder"]}}]}]]],
		RowBox[ {"\[Or]", "\[Piecewise]", GridBox[ {{"\[SelectionPlaceholder]"}, {"\[Placeholder]"}}, ColumnAlignments -> Left]}],
		translate[ "CONNTooltip"],
		"orn"
	}

langButtonData[ "IMPL2"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "IMPL2"], 
			DisplayForm[ RowBox[ {TagBox[ FrameBox[ "left"], "SelectionPlaceholder"],
				"\[Implies]",
				TagBox[ FrameBox[ "right"], "Placeholder"]}]]],
		RowBox[ {"\[SelectionPlaceholder]", "\[Implies]", "\[Placeholder]"}],
		translate[ "CONN2Tooltip"],
		"impl"
	}

langButtonData[ "EQUIV2"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "EQUIV2"], 
			DisplayForm[ RowBox[ {TagBox[ FrameBox[ "left"], "SelectionPlaceholder"],
				"\[DoubleLongLeftRightArrow]",
				TagBox[ FrameBox[ "right"], "Placeholder"]}]]],
		RowBox[ {"\[SelectionPlaceholder]", "\[DoubleLongLeftRightArrow]", "\[Placeholder]"}],
		translate["CONN2Tooltip"],
		"equiv"
	}
	
langButtonData[ "EQUIV3"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "EQUIV3"], 
			DisplayForm[ RowBox[ {"\[DoubleLeftRightArrow]", "\[Piecewise]", GridBox[ {{TagBox[ FrameBox[ SubscriptBox[ "e", "1"]], "SelectionPlaceholder"]},
				{"\[VerticalEllipsis]"},
				{TagBox[ FrameBox[ SubscriptBox[ "e", "n"]], "Placeholder"]}}]}]]],
		RowBox[ {"\[DoubleLeftRightArrow]", "\[Piecewise]", GridBox[ {{"\[SelectionPlaceholder]"}, {"\[Placeholder]"}}]}],
		translate[ "CONNTooltip"],
		"equivn"
	}

langButtonData[ "EQ"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "EQ"], 
			DisplayForm[ RowBox[ {TagBox[ FrameBox[ "left"], "SelectionPlaceholder"],
				"\[Equal]",
				TagBox[ FrameBox[ "right"], "Placeholder"]}]]],
		RowBox[ {"\[SelectionPlaceholder]", "\[Equal]", "\[Placeholder]"}],
		translate[ "CONN2Tooltip"],
		"eq"
	}

langButtonData[ "EQUIVDEF"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "EQUIVDEF"], 
			DisplayForm[ RowBox[ {TagBox[ FrameBox[ "left"], "SelectionPlaceholder"],
				RowBox[{":", "\[NegativeThickSpace]\[NegativeThinSpace]", "\[DoubleLongLeftRightArrow]"}],
				TagBox[ FrameBox[ "right"], "Placeholder"]}]]],
		RowBox[ {"\[SelectionPlaceholder]",
			TagBox[ RowBox[{":", "\[NegativeThickSpace]\[NegativeThinSpace]", "\[DoubleLongLeftRightArrow]"}], Identity, SyntaxForm->"a:=b"], "\[Placeholder]"}],
		translate[ "EQUIVDEFTooltip"],
		":equiv"
	}

langButtonData[ "EQDEF"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "EQDEF"], 
			DisplayForm[ RowBox[ {TagBox[ FrameBox[ "left"], "SelectionPlaceholder"],
				":=",
				TagBox[ FrameBox[ "right"], "Placeholder"]}]]],
		RowBox[ {"\[SelectionPlaceholder]", ":=", "\[Placeholder]"}],
		translate[ "EQDEFTooltip"],
		":eq"
	}

langButtonData[ "FORALL1"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "FORALL1"], 
			DisplayForm[ RowBox[ {UnderscriptBox[StyleBox[ "\[ForAll]", FontSize->14], Placeholder["rg"]], SelectionPlaceholder["expr"]}]]],
		RowBox[ {UnderscriptBox[ "\[ForAll]", "\[Placeholder]"], "\[SelectionPlaceholder]"}],
		translate[ "QUANT1Tooltip"],
		"far"
	}

langButtonData[ "FORALL2"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "FORALL2"], 
			DisplayForm[ RowBox[{UnderscriptBox[ UnderscriptBox[ StyleBox["\[ForAll]", FontSize->14], Placeholder["rg"]], Placeholder["cond"]], SelectionPlaceholder["expr"]}]]],
		RowBox[ {UnderscriptBox[ UnderscriptBox["\[ForAll]", "\[Placeholder]"], "\[Placeholder]"], "\[SelectionPlaceholder]"}],
		translate[ "QUANT2Tooltip"],
		"farc"
	}
	
langButtonData[ "EXISTS1"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "EXISTS1"], 
			DisplayForm[ RowBox[ {UnderscriptBox[ StyleBox["\[Exists]", FontSize->14], Placeholder["rg"]], SelectionPlaceholder["expr"]}]]],
		RowBox[ {UnderscriptBox[ "\[Exists]", "\[Placeholder]"], "\[SelectionPlaceholder]"}],
		translate[ "QUANT1Tooltip"],
		"exr"
	}

langButtonData[ "EXISTS2"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "EXISTS2"], 
			DisplayForm[ RowBox[{UnderscriptBox[ UnderscriptBox[ StyleBox["\[Exists]", FontSize->14], Placeholder["rg"]], Placeholder["cond"]], SelectionPlaceholder["expr"]}]]],
		RowBox[ {UnderscriptBox[ UnderscriptBox[ "\[Exists]", "\[Placeholder]"], "\[Placeholder]"], "\[SelectionPlaceholder]"}],
		translate[ "QUANT2Tooltip"],
		"exrc"
	}
	
langButtonData[ "LET"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "LET"], 
			DisplayForm[ RowBox[{UnderscriptBox[ "let", RowBox[ {Placeholder["a"], "=", Placeholder["x"]}]], SelectionPlaceholder["expr"]}]]],
		RowBox[ {UnderscriptBox[ "let", RowBox[ {"\[Placeholder]", "=", "\[Placeholder]"}]], "\[SelectionPlaceholder]"}],
		translate[ "LETTooltip"],
		"let"
	}
	
langButtonData[ "CASEDIST"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "CASEDIST"], 
			DisplayForm[RowBox[{"\[Piecewise]",
				GridBox[{
					{TagBox[ FrameBox[ SubscriptBox[ "e", "1"]], "SelectionPlaceholder"], "\[DoubleLeftArrow]", TagBox[ FrameBox[SubscriptBox[ "c", "1"]], "Placeholder"]},
					{"", "\[VerticalEllipsis]", ""},
					{TagBox[ FrameBox[ SubscriptBox[ "e", "n"]], "Placeholder"], "\[DoubleLeftArrow]", TagBox[ FrameBox[SubscriptBox[ "c", "n"]], "Placeholder"]}
				}]
			}]]],
		RowBox[{"\[Piecewise]",
			GridBox[{
				{"\[SelectionPlaceholder]", "\[DoubleLeftArrow]", "\[Placeholder]"},
				{"\[Placeholder]", "\[DoubleLeftArrow]", "\[Placeholder]"}
			}]
		}],
		translate[ "CASEDISTTooltip"],
		"cdist"
	}
	
langButtonData[ "SINGLEOP"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "SINGLEOP"], 
			DisplayForm[ TagBox[ FrameBox[ "\[CircleDot]"], "SelectionPlaceholder"]]],
		TagBox[ "\[SelectionPlaceholder]", Identity],
		translate[ "0ANNOPTooltip"],
		"op"
	}
	
langButtonData[ "OVEROP"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "OVEROP"], 
			DisplayForm[ OverscriptBox[ TagBox[ FrameBox["\[CircleDot]"], "SelectionPlaceholder"],
										TagBox[ FrameBox["A"], "Placeholder"]]]],
		OverscriptBox[ "\[SelectionPlaceholder]", "\[Placeholder]"],
		translate[ "1ANNOPTooltip"],
		"oop"
	}
	
langButtonData[ "UNDEROVEROP"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "UNDEROVEROP"], 
			DisplayForm[ UnderoverscriptBox[ TagBox[ FrameBox["\[CircleDot]"], "SelectionPlaceholder"],
										TagBox[ FrameBox["A"], "Placeholder"],
										TagBox[ FrameBox["B"], "Placeholder"]]]],
		UnderoverscriptBox[ "\[SelectionPlaceholder]", "\[Placeholder]", "\[Placeholder]"],
		translate[ "2ANNOPTooltip"],
		"uoop"
	}
	
langButtonData[ "SUBOP"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "SUBOP"], 
			DisplayForm[ SubscriptBox[ TagBox[ FrameBox["\[CircleDot]"], "SelectionPlaceholder"],
									   TagBox[ FrameBox["A"], "Placeholder"]]]],
		SubscriptBox[ "\[SelectionPlaceholder]", "\[Placeholder]"],
		translate[ "1ANNOPTooltip"],
		"subop"
	}
	
langButtonData[ "SUPEROP"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "SUPEROP"], 
			DisplayForm[ SuperscriptBox[ TagBox[ FrameBox["\[CircleDot]"], "SelectionPlaceholder"],
										 TagBox[ FrameBox["A"], "Placeholder"]]]],
		SuperscriptBox[ "\[SelectionPlaceholder]", "\[Placeholder]"],
		translate[ "1ANNOPTooltip"],
		"supop"
	}
	
langButtonData[ "SUBSUPEROP"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "SUBSUPEROP"], 
			DisplayForm[ SubsuperscriptBox[ TagBox[ FrameBox["\[CircleDot]"], "SelectionPlaceholder"],
										TagBox[ FrameBox["A"], "Placeholder"],
										TagBox[ FrameBox["B"], "Placeholder"]]]],
		SubsuperscriptBox[ "\[SelectionPlaceholder]", "\[Placeholder]", "\[Placeholder]"],
		translate[ "2ANNOPTooltip"],
		"subsupop"
	}
	
langButtonData[ "OVERSUBOP"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "OVERSUBOP"], 
			DisplayForm[ SubscriptBox[ OverscriptBox[ TagBox[ FrameBox["\[CircleDot]"], "SelectionPlaceholder"],
													  TagBox[ FrameBox["A"], "Placeholder"]],
									   TagBox[ FrameBox["B"], "Placeholder"]]]],
		SubscriptBox[ OverscriptBox[ "\[SelectionPlaceholder]", "\[Placeholder]"], "\[Placeholder]"],
		translate[ "2ANNOPTooltip"],
		"osop"
	}

langButtonData[ "APPEND"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "APPEND"], 
			"\:293a"],
		RowBox[ {"\[SelectionPlaceholder]", TagBox[ "\:293a", Identity, SyntaxForm -> "a*b"], "\[Placeholder]"}],
		MessageName[ appendElem$TM, "usage", $TmaLanguage],
		"app"
	}
	
langButtonData[ "PREPEND"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "PREPEND"], 
			"\:293b"],
		RowBox[ {"\[SelectionPlaceholder]", TagBox[ "\:293b", Identity, SyntaxForm -> "a*b"], "\[Placeholder]"}],
		MessageName[ prependElem$TM, "usage", $TmaLanguage],
		"prep"
	}
	
langButtonData[ "JOIN"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "JOIN"], 
			"\:22c8"],
		RowBox[ {"\[SelectionPlaceholder]", TagBox[ "\:22c8", Identity, SyntaxForm -> "a*b"], "\[Placeholder]"}],
		MessageName[ joinTuples$TM, "usage", $TmaLanguage],
		"join"
	}
	
langButtonData[ "ELEMTUP"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate[ "ELEMTUP"], 
			"\:22ff"],
		RowBox[ {"\[SelectionPlaceholder]", TagBox[ "\:22ff", Identity, SyntaxForm -> "a+b"], "\[Placeholder]"}],
		MessageName[ elemTuple$TM, "usage", $TmaLanguage],
		"elemT"
	}
Scan[
	With[ {id = #[[1]], plain = #[[2]], left = #[[3]], right = #[[4]], name = "Theorema`Language`" <> #[[5]], esc = #[[6]]},
		With[ {sym = If[ StringMatchQ[ name, __ ~~ ("$"|"$TM")], ToExpression[ name], ToExpression[ name <> "$TM"]]},
			langButtonData[ id] :=
				{
					If[ TrueQ[ $buttonNat],
						translate[ id],
						plain
					],
					RowBox[ {TagBox[ left, Identity, SyntaxForm -> "("], "\[SelectionPlaceholder]", TagBox[ right, Identity, SyntaxForm -> ")"]}],
					MessageName[ sym, "usage", $TmaLanguage],
					esc
				}
		]
	]&,
	specialBrackets
]
langButtonData[ args___] := unexpected[ langButtonData, {args}]

(*
	We distinguish several types of buttons:
	Type 1: adds AutoParentheses
	Type 2: no AutoParentheses
*)
makeLangButton[ {bname_String, 1}] :=
    With[ { bd = langButtonData[ bname]},
    	With[ {lab = bd[[1]], paste = bd[[2]], help = bd[[3]], key = bd[[4]]},
			Tooltip[ Button[ lab,
				If[ CurrentValue[ "ShiftKey"],
					FrontEndExecute[ {NotebookApply[ InputNotebook[], paste, Placeholder]}],
					FrontEndExecute[ {NotebookApply[ InputNotebook[], RowBox[ {autoParenthesis[ "("], paste, autoParenthesis[ ")"]}], Placeholder]}]
				], Appearance -> "DialogBox", Alignment -> {Left, Top}, ImageSize -> All],
				help <> translate[ "tooltipButtonParen"]<>": \[EscapeKey]"<> key <>"\[EscapeKey]", TooltipDelay -> 0.5]
    	]
    ]
makeLangButton[ {bname_String, 2}] :=
    With[ { bd = langButtonData[ bname]},
    	With[ {lab = bd[[1]], paste = bd[[2]], help = bd[[3]], key = bd[[4]]},
			Tooltip[ Button[ lab,
				FrontEndExecute[ {NotebookApply[ InputNotebook[], paste, Placeholder]}], 
				Appearance -> "DialogBox", Alignment -> {Left, Top}, ImageSize -> All],
				help <> translate[ "tooltipButtonNoParen"]<>": \[EscapeKey]"<> key <>"\[EscapeKey]", TooltipDelay -> 0.5]
    	]
    ]
makeLangButton[ args___] := unexpected[ makeLangButton, {args}]

(*
	We use TagBox because StyleBox did not work together with InputAliases: when entering formulae with alias, some StyleBoxes vanished
	for unknown reasons. With TagBox it works.
*)
autoParenthesis[ c_String] := TagBox[ c, "AutoParentheses"]
autoParenthesis[ args___] := unexpected[ autoParenthesis, {args}]

allFormulae = {
			   {"Logic", {{{"AND2", 1}, {"OR2", 1}, {"NOT", 1}, {"IMPL2", 1}},
			   	{{"EQUIV2", 1}, {"EQ", 1}, {"EQUIVDEF", 1}, {"EQDEF", 1}},
			   	{{"AND3", 1}, {"OR3", 1}, {"EQUIV3", 1}, {"CASEDIST", 1}},
			   	{{"FORALL1", 1}, {"EXISTS1", 1}, {"FORALL2", 1}, {"EXISTS2", 1}},
			   	{{"LET", 1}}}},
			   {"Arithmetic", {}},
			   {"Sets", {}},
			   {"Tuples", {{{"APPEND", 1}, {"PREPEND", 1}, {"JOIN", 1}, {"ELEMTUP", 1}}}},
			   {"Operators", {{{"SUBOP", 1}, {"SUPEROP", 1}, {"SUBSUPEROP", 1}},
			   	{{"OVEROP", 1}, {"UNDEROVEROP", 1}, {"OVERSUBOP", 1}},
			   	{{"SINGLEOP", 1}}}},
			   {"Bracketted", Map[ {First[ #], 2}&, With[ {l = Length[ specialBrackets]}, Append[ Partition[ specialBrackets, 7], Take[ specialBrackets, -Mod[ l, 7]]]], {2}]}
};

makeButtonCategory[ {category_String, buttons_List}, cols_Integer:2] :=
	category -> Column[ Map[ Row[ Map[ makeLangButton, #], Spacer[2]]&, buttons]
	]
	(*OpenerView[{
		Style[ translate[ category], "LabeledLabel"],
		Grid[ partitionFill[ Map[ makeLangButton, buttons], cols], Alignment -> {Left, Top}]},
		(* I have no idea why I need the explicit context here, in similar situations for other dynamic object it works without ... *)
		ToExpression["Dynamic[ Theorema`Interface`GUI`Private`$tcSessMathOpener$"<>category<>"]"]
		]
		*)

makeButtonCategory[ args___] := unexpected[ makeButtonCategory, {args}]

langButtons[] :=
    Pane[
    	TabView[ Map[ makeButtonCategory, allFormulae]],
    	{350, 275}, ImageSizeAction -> "Scrollable", Scrollbars -> Automatic]
langButtons[] :=
	Module[ {display = Map[ makeButtonCategory, allFormulae]},
		Column[ {
			Row[ Map[ Button[ Style[ #, FontColor -> If[ $tcLangButtonSelection === #, TMAcolor[4], TMAcolor[13]]], $tcLangButtonSelection = #, 
				Background -> If[ $tcLangButtonSelection === #, TMAcolor[6], TMAcolor[0]], FrameMargins -> 2, ImageMargins -> 0]&, Map[ First, display]]],
    		PaneSelector[ display, Dynamic[ $tcLangButtonSelection], ImageSize -> {350, Automatic}]
		}]
	]

langButtons[ args___] := unexpected[ langButtons, {args}]
    
compNew[] := Column[{makeCompButton[]}]
compNew[ args___] := unexpected[ compNew, {args}]

makeCompButton[] :=
    Button[ translate[ "New"], insertNewFormulaCell[ "COMPUTE"], Alignment -> {Left, Top}, ImageSize -> Automatic]
makeCompButton[ args___] := unexpected[ makeCompButton, {args}]

partitionFill[ l_List, n_Integer, default_:""] := Partition[ PadRight[ l, n*Ceiling[ Length[ l]/n], default], n]
partitionFill[ args___] := unexpected[ partitionFill, {args}]

compSetup[] := 
	Column[{
		Labeled[ 
			Grid[{
    			{Checkbox[ Dynamic[ $traceUserDef]], translate[ "traceUserDef"]}
    		}, Alignment -> {Left}], 
    		translate[ "Trace"], {{Top, Left}}],
		Labeled[ 
			Row[ {Checkbox[ Dynamic[ $TMAcomputationDemoMode]], translate[ "restoreSettingsBeforeComp"]}, Spacer[5]], 
    		translate[ "DemoMode"], {{Top, Left}}]
    	}
	]
compSetup[ args___] := unexpected[ compSetup, {args}]

solveSetup[ ] := ""
solveSetup[ args___] := unexpected[ solveSetup, {args}]

(* ::Section:: *)
(* Windowing functions *)

tmaNotebookPut[ nb_Notebook, style_String, opts___?OptionQ] :=
	NotebookPut[ nb, 
		StyleDefinitions -> makeColoredStylesheet[ style],
		WindowTitle -> "Theorema " <> translate[ style],
		Magnification -> CurrentValue[ getTheoremaCommander[], Magnification],
		opts
	]
tmaNotebookPut[ args___] := unexpected[ tmaNotebookPut, {args}]

tmaDialogInput[ Notebook[ expr_, nbOpts___?OptionQ], style_String, opts___?OptionQ] :=
	DialogInput[ 
		Notebook[ expr, 
			StyleDefinitions -> makeColoredStylesheet[ style],
			Magnification -> CurrentValue[ getTheoremaCommander[], Magnification],
			ShowCellBracket -> False, Deployed -> True,
			WindowSize -> All,
			WindowElements -> {"VerticalScrollBar", "HorizontalScrollBar", "StatusArea"},
			opts
		]
	]
tmaDialogInput[ args___] := unexpected[ tmaDialogInput, {args}]

getExistGoalInstanceDialog[ v_, fix_, {g_, kb_}] :=
    Module[ {expr, 
    		fixBut = Map[ 
    			PasteButton[
    				theoremaDisplay[ RNG$[ #]], 
    				With[ {fbox = ToBoxes[ First[ #], TheoremaForm], fc = First[ #]}, DisplayForm[ InterpretationBox[ fbox, fc]]]]&, fix],
    		buttonRow},
        expr[_] = Null;
        buttonRow = {CancelButton[ translate[ "instantiate later"], DialogReturn[ $Failed]], DefaultButton[ translate[ "OK"], DialogReturn[ Array[ expr, Length[v]]]]};
        tmaDialogInput[ Notebook[ 
        	Join[
        		{pSitCells[ PRFSIT$[ g, kb, ""]],
        		Cell[ translate[ "instVar"], "Subsubsection"]},
        		MapIndexed[ Cell[ BoxData[ RowBox[ {ToBoxes[ #1, TheoremaForm], ":=", 
        			ToBoxes[ InputField[ Dynamic[ expr[#2[[1]]]], Hold[ Expression], FieldSize -> 10]]}]], "Text"]&, v], 
        		{Cell[ translate[ "availConst"], "Subsubsection"],
        		Cell[ BoxData[ RowBox[ Map[ ToBoxes, fixBut]]], "Text"],
        		Cell[ BoxData[ RowBox[ Map[ ToBoxes, buttonRow]]], "Text"]}
        		]
        	],
        	"Dialog"
        ]
    ]
getExistGoalInstanceDialog[ args___] := unexpected[ getExistGoalInstanceDialog, {args}]

nextProofSitDialog[ ps_List] :=
    Module[ {proofCells, showProof = False},
        proofCells = pObjCells[];
        $TMAproofNotebook = tmaNotebookPut[ Notebook[ proofCells], "Proof", Visible -> Dynamic[ showProof]];
        tmaDialogInput[ Notebook[
            Join[ 
                {Cell[ BoxData[ ToBoxes[ 
                    Toggler[ Dynamic[ showProof], 
                        {False -> Tooltip[ translate[ "more"], translate[ "showProofProgress"]], 
                         True -> Tooltip[ translate[ "hide proof"], translate[ "hideProofProgress"]]}]]], 
                    "Hint"]},
                MapIndexed[ proofSitChoiceButtons, ps], 
                {Cell[ BoxData[ ToBoxes[ DefaultButton[]]]]}]
            ], "Dialog"]
    ]
nextProofSitDialog[ args___] := unexpected[ nextProofSitDialog, {args}]

proofSitChoiceButtons[ ps_PRFSIT$, {num_Integer}] :=
	Module[ {},
		Cell[ CellGroupData[ 
			{Cell[ TextData[{ Cell[ BoxData[ ToBoxes[ RadioButton[ Dynamic[ $selectedProofStep], id@ps]]]], 
   			"  ", translate[ "open proof situation"], " #" <> ToString[ num]}], "Section", ShowGroupOpener -> False],
			pSitCells[ ps]}, Dynamic[ If[ $selectedProofStep === id@ps, Open, Closed]]]]
	]
proofSitChoiceButtons[ args___] := unexpected[ proofSitChoiceButtons, {args}]


(* ::Section:: *)
(* licenseTab *)

licenseTab[ ] := Text[ Style[ translate[ "GNULicense"], ParagraphIndent -> 0, LineIndent -> 0, TextJustification -> 1]]
licenseTab[ args___] := unexpected[ licenseTab, {args}]


(* ::Section:: *)
(* aboutTab *)
aboutTab[ ] := Text[ Style[ translate[ "aboutTheorema"], ParagraphIndent -> 0, LineIndent -> 0, TextJustification -> 1]]
aboutTab[ args___] := unexpected[ aboutTab, {args}]

(* ::Section:: *)
(* end of package *)

If[ $Notebooks,
	openTheoremaCommander[]
];

End[];
EndPackage[];
