(* Theorema 
    Copyright (C) 2010 The Theorema Group

    This file is part of Theorema 2.0
    
    Theorema 2.0 is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Theorema 2.0 is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

BeginPackage["Theorema`Interface`GUI`", {"Theorema`"}];
(* Exported symbols added here with SymbolName::usage *)  

Needs["Theorema`Common`"]
Needs["Theorema`Language`"]
Needs["Theorema`Provers`"]
Needs["Theorema`Interface`Language`"]

Begin["`Private`"] (* Begin Private Context *) 

If[ $Notebooks,
	closeTheoremaCommander[]
];


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
                {"MaximumElementSet", RowBox[{"max","[", "A", "]"}], False, True, False},
                {"MinimumElementSet", RowBox[{"min","[", "A", "]"}], False, True, False},
                {"MaximumOf", RowBox[{"max",SubscriptBox["A","i"]}], False, True, False},
                {"MinimumOf", RowBox[{"min",SubscriptBox["A","i"]}], False, True, False},
                {"UnionOf", RowBox[{"\[Union]",SubscriptBox["A","i"]}], False, True, False},
        		{"IntersectionOf", RowBox[{"\[Intersection]",SubscriptBox["A","i"]}], False, True, False}
        	},
        	{"Tuples",
        		{"Subscript", SubscriptBox[ "T", "i"], False, True, False},
                {"TupleEqual", RowBox[ {"T","\[Equal]","S"}], False, True, False},
                {"IsElement", RowBox[ {"e","\[Element]","T"}], False, True, False},
        		{"Length", RowBox[{"\[LeftBracketingBar]", "T", "\[RightBracketingBar]"}], False, True, False},
                {"Insert", SubscriptBox[ "T",RowBox[{"e","\[Rule]","i"}]], False, True, False},
                {"Delete", SubscriptBox[ "T", RowBox[{RowBox[{"e", ",", "\[Ellipsis]"}], "\[LeftArrowBar]"}]], False, True, False},
                {"DeleteAt", SubscriptBox[ "T", RowBox[{"i", "\[LeftArrow]"}]], False, True, False},
        	    {"Replace", SubscriptBox[ "T", RowBox[{RowBox[{RowBox[{"e", ",", "\[Ellipsis]"}], "\[LeftArrowBar]", "newe"}], ",", "\[Ellipsis]"}]], False, True, False},
                {"ReplacePart", SubscriptBox[ "T", RowBox[{RowBox[{"i", "\[LeftArrow]", "e"}], ",", "\[Ellipsis]"}] ], False, True, False},
			    {"Append", RowBox[{"T","\[Cup]","e"}], False, True, False},
        		{"Prepend", RowBox[{"e","\[Cap]","T"}], False, True, False},
        		{"Join", RowBox[{"T","\[CupCap]","S"}], False, True, False},
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
        		{"Equal", RowBox[{"A","=","B"}], False, False, False},
        		{"Less", RowBox[{"A","<","B"}], False, True, False},
        		{"LessEqual", RowBox[{"A","\[LessEqual]","B"}], False, True, False},
        		{"Greater", RowBox[{"A",">","B"}], False, True, False},
        		{"GreaterEqual", RowBox[{"A","\[GreaterEqual]","B"}], False, True, False},
        		{"AbsValue", RowBox[{"\[LeftBracketingBar]", "A", "\[RightBracketingBar]"}], False, True, False},
        		{"SumOf", RowBox[{"\[Sum]",SubscriptBox["A","i"]}], False, True, False},
        		{"ProductOf", RowBox[{"\[Product]",SubscriptBox["A","i"]}], False, True, False}
        	},
        	{"Logic", 
        		{"Not", RowBox[{"\[Not]","P"}], False, True, False},
        		{"And", RowBox[{"P", "\[And]","Q"}], True, True, False},
        		{"Or", RowBox[{"P", "\[Or]","Q"}], True, True, False},
        		{"Implies", RowBox[{"P", "\[Implies]","Q"}], True, True, False},
        		{"Iff", RowBox[{"P", "\[Equivalent]","Q"}], True, True, False},
        		{"Forall", RowBox[{"\[ForAll]","P"}], False, True, False},
        		{"Exists", RowBox[{"\[Exists]","P"}], False, True, False},
        		{"Equal", RowBox[{"A","=","B"}], True, False, False},
        		{"Let", UnderscriptBox["let",RowBox[{"A","=","\[Ellipsis]"}]], False, True, False},
        		{"Componentwise", RowBox[{"P", "@", "A"}], False, True, False}
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
        $tcAllFormulaeOpener = True;
        $tcAllDeclOpener = True;
		$kbStruct = {};
		$ruleFilterKW = "";
		$initLabel = "???";
		$labelSeparator = ",";
		$cellTagKeySeparator = ":";
		Clear[ kbSelectProve, kbSelectSolve];
		kbSelectProve[_] := False;
		kbSelectSolve[_] := False;
		$selectedProofGoal = {};
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
		$TMAactDecl = translate[ "None"];
		$proofTreeScale = 1;
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
        CreatePalette[ Dynamic[
        	Refresh[
        	activitiesView[
        		(* activities buttons *)
        		{translate["tcSessionTabLabel"], translate["tcProveTabLabel"], translate["tcComputeTabLabel"], translate["tcSolveTabLabel"], translate["tcPreferencesTabLabel"]},
        		(* for each activity the respective action buttons *)
        		{
        			(* session *){translate["tcSessTabComposeTabLabel"], translate["tcSessTabInspectTabLabel"], translate["tcSessTabArchTabLabel"]},
        			(* prove *)  {translate["tcProveTabGoalTabLabel"], translate["tcProveTabKBTabLabel"], translate["tcProveTabBuiltinTabLabel"],
        				translate["tcProveTabProverTabLabel"], translate["tcProveTabSubmitTabLabel"], translate["tcProveTabInspectTabLabel"]},
        			(* compute *){translate["tcComputeTabSetupTabLabel"], translate["tcComputeTabKBTabLabel"], translate["tcComputeTabBuiltinTabLabel"]},
        			(* solve *)  {translate["tcSolveTabKBTabLabel"], translate["tcSolveTabBuiltinTabLabel"]},
        			(* prefs *)  {(*, , *)}
        		},
        		(* for each activity and each action the respective content *)
        		{
        			(* session *){sessionCompose[], sessionInspect[], sessionArchive[]},
        			(* prove *)  {Dynamic[ Refresh[ displaySelectedGoal[], UpdateInterval -> 2]],
        				Dynamic[ Refresh[ displayKBBrowser["prove"], TrackedSymbols :> {$kbStruct}]],
        				Dynamic[ Refresh[ displayBuiltinBrowser["prove"], TrackedSymbols :> {buiActProve}]],
        				Dynamic[ Refresh[ selectProver[], TrackedSymbols :> {$selectedRuleSet, $selectedStrategy, $ruleFilterKW}]],
        				Dynamic[ Refresh[ submitProveTask[ ], TrackedSymbols :> {$selectedProofGoal, $selectedProofKB, $selectedSearchDepth, $selectedSearchTime}]],
        				Dynamic[ Refresh[ proofNavigation[ $TMAproofTree], TrackedSymbols :> {$TMAproofTree, $TMAproofSearchRunning, $TMAproofNotebook, ruleTextActive, $proofTreeScale, $selectedProofStep}]]},
        			(* compute *){compSetup[],
        				Dynamic[ Refresh[ displayKBBrowser["compute"], TrackedSymbols :> {$kbStruct}]],
        				Dynamic[ Refresh[ displayBuiltinBrowser["compute"], TrackedSymbols :> {buiActComputation}]]},
        			(* solve *)  {Dynamic[Refresh[displayKBBrowser["solve"], TrackedSymbols :> {$kbStruct}]],
        				Dynamic[ Refresh[ displayBuiltinBrowser["solve"], TrackedSymbols :> {buiActSolve}]]},
        			(* prefs *)  {setPreferences[ ]}
        		}
        	], TrackedSymbols :> {$Language}]],
        	StyleDefinitions -> makeColoredStylesheet[ "GUI"],
        	WindowTitle -> translate["Theorema Commander"],
        	WindowElements -> {"StatusArea"}]
    ]
openTheoremaCommander[ args___] := unexpected[ openTheoremaCommander, {args}]

emptyPane[ text_String:""] := Pane[ text, Alignment -> {Center, Center}]
emptyPane[ text_String:"", size_] := Pane[ text, size, Alignment -> {Left, Top}]
emptyPane[ args___] := unexpected[ emptyPane, {args}]

getTheoremaCommander[ ] := 
	Select[ Notebooks[], (WindowTitle /. Options[ #, WindowTitle]) === translate["Theorema Commander"]&]
getTheoremaCommander[ args___] := unexpected[ getTheoremaCommander, {args}]

closeTheoremaCommander[ ] :=
	Scan[ NotebookClose, getTheoremaCommander[ ]]
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
                activitiesLab], Center, 0],
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
	{1, 1} -> { langButtonData["FORALL1"], {}, {}, {}},
	{1, 2} -> { langButtonData["FORALL2"], {}, {}, {}},
	{1, 3} -> { langButtonData["AND1"], {}, {}, {}},
	{1, 4} -> { langButtonData["IMPL1"], {}, {}, {}},
	{1, 5} -> { langButtonData["EQDEF"], {}, {}, {}},
	{2, 1} -> { langButtonData["EXISTS1"], {}, {}, {}},
	{2, 2} -> { langButtonData["EXISTS2"], {}, {}, {}},
	{2, 3} -> { langButtonData["OR1"], {}, {}, {}},
	{2, 4} -> { langButtonData["EQUIV1"], {}, {}, {}},
	{2, 5} -> { langButtonData["EQUIVDEF"], {}, {}, {}},
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
    	goal = findSelectedFormula[ sel];
        If[ goal === {},
            translate["noGoal"],
            With[ {selGoal = goal[[1]]},
            	Column[ {
            		Button[ translate[ "OKnext"], $selectedProofGoal = selGoal; $tcActionView++],
            		Grid[ {displayLabeledFormula[ selGoal]}]
            		}]
            ]
        ]
    ]
displaySelectedGoal[ goal_] :=
    Module[ { },
        If[ goal === {},
            translate["noGoal"],
            Grid[ {displayLabeledFormula[ goal]}]
        ]
    ]
displaySelectedGoal[args___] :=
    unexpected[displaySelectedGoal, {args}]

displayLabeledFormula[ FML$[ key_, form_, lab_, ___]] := 
	Module[ {src, nb, labDisp = makeLabel[ lab]},
		src = StringReplace[ key[[2]], "Source"<>$cellTagKeySeparator -> "", 1];
		nb = sourceToNotebookFile[ src];
		{ If[ nb =!= $Failed,
			Hyperlink[ Style[ labDisp, "FormulaLabel"], {nb, key[[1]]}],
			Tooltip[ Style[ labDisp, "FormulaLabel"], translate[ "noNB"] <> src]],
		Style[ theoremaDisplay[ form], "DisplayFormula", LineBreakWithin -> False]}
	]
displayLabeledFormula[ args___] := unexpected[ displayLabeledFormula, {args}]

displaySelectedKB[ ] :=
	Module[ {},
    	$selectedProofKB = Select[ $tmaEnv, kbSelectProve[#[[1]]]&];
        If[ $selectedProofKB === {},
            translate["noKB"],
            displayLabeledFormulaListGrid[ $selectedProofKB]
        ]
    ]
displaySelectedKB[ args___] := unexpected[ displaySelectedKB, {args}]

displayLabeledFormulaList[ l_List] := Map[ displayLabeledFormula, l]
displayLabeledFormulaList[ args___] := unexpected[ displayLabeledFormulaList, {args}]

displayLabeledFormulaListGrid[ l_List] := Grid[ displayLabeledFormulaList[ l], Alignment -> {{Center, Left}, Automatic}]
displayLabeledFormulaListGrid[ args___] := unexpected[ displayLabeledFormulaListGrid, {args}]

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

extractKBStruct[ nb_NotebookObject] := extractKBStruct[ NotebookGet[nb]]

extractKBStruct[ Notebook[ l_List, __?OptionQ]] := extractKBStruct[ Notebook[ l]] (* process the notebook cells only, without any notebook options *)
	
extractKBStruct[ nb_Notebook] :=
    Module[ {posTit = Cases[ Position[ nb, Cell[_, "Title", ___]], {a___, 1}],
      posSec =  Cases[ Position[ nb, Cell[_, "Section", ___]], {a___, 1}], 
      posSubsec = Cases[ Position[ nb, Cell[_, "Subsection", ___]], {a___, 1}], 
      posSubsubsec = Cases[ Position[ nb, Cell[_, "Subsubsection", ___]], {a___, 1}], 
      posSubsubsubsec = Cases[ Position[ nb, Cell[_, "Subsubsubsection", ___]], {a___, 1}], 
      posEnv = Cases[ Position[ nb, Cell[_, "EnvironmentHeader", ___]], {a___, 1}], 
      posInp = Position[ nb, Cell[_, "FormalTextInputFormula", ___]], inputs, depth, sub, root, heads, isolated},
      (* extract all positions of relevant cells
         join possible containers with decreasing level of nesting *)
        heads = Join[posEnv, posSubsubsubsec, posSubsubsec, posSubsec, posSec, posTit];
        (* build up a nested list structure representing the nested cell structure 
           start with singleton lists containing a header and add input cells to the respective group *)
        {inputs, isolated} = Fold[arrangeInput, {Map[List, heads], {}}, posInp];
        depth = Union[Map[Length[#[[1]]] &, inputs]];
        (* go through all groups starting with the most deeply nested one *)
        While[Length[depth] > 1,
            (* the most deeply nested ones are the possible candidates to be joined to other groups *)
         sub = Select[inputs, Length[#[[1]]] == depth[[-1]] &];
         (* the less deeply nested ones are groups to which subitems may be added *)
         root = Select[inputs, Length[#[[1]]] < depth[[-1]] &];
         (* one after the other add lower priority groups to higher priority ones *)
         inputs = Fold[arrangeSub, root, sub];
         depth = Drop[depth, -1];
         ];
         (* finally, add isolated nodes at the beginning *)
        Join[isolated, inputs]
    ]

extractKBStruct[ args___] :=
    unexpected[ extractKBStruct, {args}]


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
structView[ file_, {head:Cell[ sec_, style:"Title"|"Section"|"Subsection"|"Subsubsection"|"Subsubsubsection"|"EnvironmentHeader", opts___], rest___}, tags_, task_] :=
    Module[ {content, views, compTags, structControl},
    	(* process content componentwise
    	   during recursion, we collect all cell tags from cells contained in that group 
    	   Transpose -> pos 1 contains the list of subviews
    	   pos 2 contains the list of tags in subgroups *)
    	content = DeleteCases[ Map[ structView[ file, #, tags, task] &, {rest}], {}];
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
structView[ file_, item_List, tags_, task_] :=
    Module[ {content, views, compTags},
     	(* process content componentwise
    	   during recursion, we collect all cell tags from cells contained in that group 
    	   Transpose -> pos 1 contains the list of subviews
    	   pos 2 contains the list of tags in subgroups *)
    	content = DeleteCases[ Map[ structView[ file, #, tags, task] &, item], {}];
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
structView[ file_, Cell[ content_, "FormalTextInputFormula", a___, CellTags -> cellTags_, b___], tags_, task_] :=
    Module[ { isEval, formPos, cleanCellTags, keyTags, formulaLabel, idLabel, nbAvail},
        cleanCellTags = getCleanCellTags[ cellTags];
        (* keyTags are those cell tags that are used to uniquely identify the formula in the KB *)
        keyTags = getKeyTags[ cellTags];
        (* check whether cell has been evaluated -> formula is in KB? *)
        formPos = Position[ $tmaEnv, FML$[ keyTags, _, __], 1, 1];
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
                             	theoremaDisplay[ Extract[ $tmaEnv, Append[ formPos[[1]], 2]]],
                             	displayCellContent[ content]]
                    ]},
                Spacer[10]],
            "compute",
            Row[ {Checkbox[ Dynamic[ kbSelectCompute["KEY"]], Enabled -> isEval] /. "KEY" -> keyTags,
                Tooltip[ Hyperlink[ Style[ formulaLabel, If[ isEval,
                                                       "FormalTextInputFormula",
                                                       "FormalTextInputFormulaUneval"
                                                   ]], {file, idLabel}, Enabled -> nbAvail, ActiveStyle -> If[ nbAvail, "HyperlinkActive", None]],
                             If[ isEval,
                             	theoremaDisplay[ Extract[ $tmaEnv, Append[ formPos[[1]], 2]]],
                             	displayCellContent[ content]]
                    ]},
                Spacer[10]],
            "solve",
            Row[ {Checkbox[ Dynamic[ kbSelectSolve[ "KEY"]], Enabled -> isEval] /. "KEY" -> keyTags, 
                Tooltip[ Hyperlink[ Style[ formulaLabel, If[ isEval,
                                                       "FormalTextInputFormula",
                                                       "FormalTextInputFormulaUneval"
                                                   ]], {file, idLabel}, Enabled -> nbAvail, ActiveStyle -> If[ nbAvail, "HyperlinkActive", None]],
                             If[ isEval,
                             	theoremaDisplay[ Extract[ $tmaEnv, Append[ formPos[[1]], 2]]],
                             	displayCellContent[ content]]
                    ]},
                Spacer[10]]    
            ], {keyTags}}
    ]

(* input cell without cell tags -> ignore *)
structView[ file_, Cell[ content_, "FormalTextInputFormula", ___], tags_, task_] := {}

structView[ args___] :=
    unexpected[ structView, {args}]

(* header view *)
headerView[ file_, Cell[ content_String, style_, ___], tags_, task_] :=
(* tags contains all tags contained in the group
   generate a checkbox for the whole group and the header from the cell
   checkbox does not have an associated variable whose value the box represents
   instead, the checkbox is checked if all tags containd in the group are checked,
   checking the box calls function setAll in order to set/unset all tags contained in the group *)
    Switch[ task,
    	"prove",
        Row[ {Checkbox[ Dynamic[ allTrue[ tags, kbSelectProve], setAll[ tags, kbSelectProve, #] &]], Style[ content, style]}, Spacer[10]],
        "compute",
        Row[ {Checkbox[ Dynamic[ allTrue[ tags, kbSelectCompute], setAll[ tags, kbSelectCompute, #] &]], Style[ content, style]}, Spacer[10]],
        "solve",
        Row[ {Checkbox[ Dynamic[ allTrue[ tags, kbSelectSolve], setAll[ tags, kbSelectSolve, #] &]], Style[ content, style]}, Spacer[10]]        
    ]
headerView[ file_, Cell[ content_TextData, style_, ___], tags_, task_] := headerView[ file, Cell[ formattedCellToString[ content], style], tags, task]
headerView[ args___] := unexpected[ headerView, {args}]

displayCellContent[ BoxData[ b_]] := DisplayForm[ b]
displayCellContent[ c_] := DisplayForm[ c]
displayCellContent[ args___] := unexpected[ displayCellContent, {args}]

formattedCellToString[ TextData[ l_List]] := Apply[ StringJoin, Map[ textDataToString, l]]
formattedCellToString[ d_] := textDataToString[ d]
formattedCellToString[ args___] := unexpected[ formattedCellToString, {args}]

textDataToString[ s_String] := StringReplace[ s, "\n" -> " "]
textDataToString[ StyleBox[ s_String, ___]] := textDataToString[ s]
textDataToString[ Cell[ BoxData[ b_], ___]] := "\!\(" <> ToString[ InputForm[ b]] <> "\)"
textDataToString[ _] := "\[DownQuestion]?"
textDataToString[ args___] := unexpected[ textDataToString, {args}]



(* ::Subsubsection:: *)
(* updateKBBrowser *)


(* global variable $kbStruct contains the knowledge structure
   for each notebook ever evaluated in the session it contains an entry
   filename -> struct, where
   filename is the full filename of the notebook and
   struct is the nested cell structure containing the cells at those positions obtained by extractKBStruct *)
updateKBBrowser[] :=
    Module[ {file=CurrentValue["NotebookFullFileName"], pos, new},
        pos = Position[ $kbStruct, file -> _];
        (* We don't extract the entire cells, we throw away all options except CellTags and CellID in order to not blow up $kbStruct too much *)
        new = file -> With[ {nb = NotebookGet[EvaluationNotebook[]]},
                          extractKBStruct[nb] /. l_?VectorQ :> (Extract[nb, l] /. {c:Cell[ _, _, ___] :> DeleteCases[ c, Except[ CellTags|CellID] -> _]})
                      ];
        (* if there is already an entry for that notebook then replace the structure,
           otherwise add new entry *)
        If[ pos === {},
            AppendTo[ $kbStruct, new],
            $kbStruct[[pos[[1,1]]]] = new
        ]
    ]
updateKBBrowser[args___] :=
    unexpected[updateKBBrowser, {args}]


(* ::Subsubsection:: *)
(* displayKBBrowser *)


   
displayKBBrowser[ task_String] :=
    Module[ {},
        If[ $kbStruct === {},
            emptyPane[translate["noKnowl"]],
            (* generate tabs for each notebook,
               tab label contains a short form of the filename, tab contains a Pane containing the structured view *)
            Dynamic[
            Column[{
            	Button[ translate[ "OKnext"], $tcActionView++],
                Row[ Map[ Button[ Tooltip[ FileBaseName[ #], #], $tcKBBrowseSelection[ task] = #, 
					Background -> If[ $tcKBBrowseSelection[ task] === #, TMAcolor[0], TMAcolor[5]], FrameMargins -> 2, ImageMargins -> 0]&, Map[ First, $kbStruct]]],
				PaneSelector[ Map[ #[[1]] -> 
                     		Pane[ structView[ #[[1]], #[[2]], {}, task][[1]], ImageSizeAction -> "Scrollable", Scrollbars -> Automatic] &, 
                   			$kbStruct], Dynamic[ $tcKBBrowseSelection[ task]], ImageSize -> {350, Automatic}],
                Button[ translate[ "OKnext"], $tcActionView++]
            }]
            ]
        ]
    ]
displayKBBrowser[args___] :=
    unexpected[displayKBBrowser, {args}]

(*
TabView[
                  		Map[Tooltip[Style[FileBaseName[#[[1]]], "NotebookName"], #[[1]]] -> 
                     		Pane[structView[#[[1]], #[[2]], {}, task][[1]], ImageSizeAction -> "Scrollable", Scrollbars -> Automatic] &, 
                   			$kbStruct], 
                  		Appearance -> {"Limited", 10}, FrameMargins->None]
                  		*)

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
        opGroup = partitionFill[ sub[[1]], 4];
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

(*Responsible for groupe name of rules *)
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
structViewRules[{category_String}, tags_, open_]:=Sequence[];

structViewRules[ Hold[ rs_]] := 
	Module[{list = {}},
		If[ StringLength[ $ruleFilterKW] > 2,		
			list = DeleteCases[ rs, {r_Symbol /; testNoMatch[ MessageName[ r, "usage"], "*" <> $ruleFilterKW <> "*"], t_, text_, p_Integer ,___}, Infinity];
			structViewRules[ list, {}, True],
			(* else *)
			structViewRules[ rs, {}, True]
		]
	]

testNoMatch[s_String,p_String]:=Not[StringMatchQ[ s,p]]
testNoMatch[s_,p_]:=True

displaySelectedRules[ Hold[ rs_]] := 
	Module[ {actRules},
		(* Select checked list_ from allRules_ *)  
		actRules = Cases[ rs, {r_Symbol?ruleActive, _, _, _Integer, ___} -> r, Infinity];
		(*Sort list_ by priority_*)
		actRules = Sort[ actRules, rulePriority[#1] < rulePriority[#2]&];
		Pane[		
			Column[ Map[ makeRuleRow, actRules]],
			ImageSize -> {360,200},
			Scrollbars -> {False, True}
		]	
	]

makeRuleRow[r_Symbol] := 
	Module[ {}, 
		Style[ 
			Row[{ "(" <> ToString[ rulePriority[ r]] <> ")", Spacer[2],
				Tooltip[ showProofTextPic[ ruleTextActive[ r]], MessageName[ ruleTextActive, "usage"]], Spacer[5], MessageName[ r, "usage"]}],
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
                	MessageName[ ruleTextActive, "usage"]],
                Tooltip[ 
                	PopupMenu[ Dynamic[ rulePriority[ r]], Table[ i, {i,1,100}], BaselinePosition -> align, ImageSize -> {45, 16}],
                    translate[ "rulePriority"]]}
            ],
            MessageName[ r, "usage"]}, Spacer[7]], LineBreakWithin -> False], {r}}
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
	Row[ {Button[ translate[ "ResetBui"], initBuiltins[ {task}]], Button[ translate[ "OKnext"], $tcActionView++]}, Spacer[3]],
  	structViewBuiltin[ $tmaBuiltins, {}, task][[1]],
  	Button[ translate[ "OKnext"], $tcActionView++]
  }]
displayBuiltinBrowser[args___] := unexcpected[ displayBuiltinBrowser, {args}]

$allProveSettings = Hold[ $selectedProofGoal, $selectedProofKB, $selectedRuleSet, $selectedStrategy, $selectedSearchDepth, $selectedSearchTime,
	$eliminateBranches, $eliminateSteps, $eliminateFormulae,
	$interactiveProofSitSel, $interactiveNewProofSitFilter, $proofCellStatus,
	kbSelectProve, buiActProve, ruleActive];

selectProver[ ] :=
    Column[{
    	Button[ translate[ "OKnext"], $tcActionView++],

    	Labeled[ Tooltip[ PopupMenu[ Dynamic[ $selectedRuleSet], Map[ MapAt[ translate, #, {2}]&, $registeredRuleSets]],
    			Apply[ Function[ rs, MessageName[ rs, "usage"], {HoldFirst}], $selectedRuleSet]], 
    		translate[ "pRules"], {{ Top, Left}}],
    	Module[ {view},
			
			{view, $allRules} = structViewRules[ $selectedRuleSet];								
    		
    		Labeled[ Column[{
				Row[{	
				Button[ translate[ "RestoreDefaults"], setRulesDefaults[ $selectedRuleSet]],
				Button[ translate[ "ShowAll"], $ruleFilterKW = ""]},
				Spacer[2]],
				With[ {label = Row[ {translate[ "FilteredBy"], InputField[ $ruleFilterKW, String]}]},
					Button[ label,
						CreateDialog[{
							Row[ {translate[ "Keyword"], InputField[ Dynamic[ $ruleFilterKW], String, ContinuousAction -> True]}],
							DefaultButton[ DialogReturn[]]},
							WindowTitle-> translate[ "FilterRulesWindow"]
						],
						Appearance -> "Frameless"
					]
				],
				If[ view === {}, translate[ "noRules"], view]}], translate[ "pRulesSetup"], {{Top, Left}}]],
    	Labeled[ Tooltip[ PopupMenu[ Dynamic[ $selectedStrategy], Map[ MapAt[ translate, #, {2}]&, $registeredStrategies]],
    		With[ {ss = $selectedStrategy}, MessageName[ ss, "usage"]]], 
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
    	Labeled[ RadioButtonBar[ 
    		Dynamic[ $proofCellStatus], {Automatic -> translate[ "auto"], Open -> translate[ "open"], Closed -> translate[ "closed"]}], 
    		translate[ "proofCellStatus"], {{Top, Left}}],
    	Button[ translate[ "OKnext"], $tcActionView++]	
    	}]
selectProver[ args___] := unexpected[ selectRuleSet, {args}]

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
					{$eliminateBranches, $eliminateSteps, $eliminateFormulae}], 
				Method -> "Queued", Active -> ($selectedProofGoal =!= {})],
			Column[{
				Labeled[ displaySelectedGoal[ $selectedProofGoal], translate["selGoal"], {{Top, Left}}],
				Labeled[ displaySelectedKB[], translate["selKB"], {{Top, Left}}],
				Labeled[ summarizeBuiltins[ "prove"], translate["selBui"], {{Top, Left}}]
			}],
			
			Column[{				
				Labeled[ displaySelectedRules[ $selectedRuleSet], translate[ "selectedRules"]<>":", {{Top,Left}}],
				Labeled[ Tooltip[ $selectedStrategy /. $registeredStrategies, MessageName[ Evaluate[ $selectedStrategy], "usage"]], translate[ "pStrat"]<>":", Left],
				Labeled[ $selectedSearchDepth, translate[ "sDepth"]<>":", Left],
				Labeled[ $selectedSearchTime, translate[ "sTime"]<>":", Left],
				Labeled[
					Column[{
    					If[ TrueQ[ $eliminateBranches], translate[ "elimBranches"], Sequence[]],
    					If[ TrueQ[ $eliminateSteps], translate[ "elimSteps"], Sequence[]],
    					If[ TrueQ[ $eliminateFormulae], translate[ "elimForm"], Sequence[]]
    				}],
    				translate[ "pSimp"]<>":", Left],
				Labeled[
					Column[{
    					If[ TrueQ[ $interactiveProofSitSel], translate[ "interactiveProofSitSel"], Sequence[]],
    					If[ TrueQ[ $interactiveNewProofSitFilter], translate[ "interactiveNewProofSitFilter"], Sequence[]],
    					If[ TrueQ[ Map[ ruleActive, And[ existsGoalInteractive, forallKBInteractive]]], translate[ "interactiveInstantiate"], Sequence[]]
    				}],
    				translate[ "pInteractive"]<>":", Left],
				Labeled[ 
					Switch[ $proofCellStatus,
						Automatic, translate[ "auto"],
						Open, translate[ "open"],
						Closed, translate[ "closed"]
					],
    			translate[ "proofCellStatus"]<>":", Left]
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
					{$eliminateBranches, $eliminateSteps, $eliminateFormulae}], 
				Method -> "Queued", Active -> ($selectedProofGoal =!= {})]
		}]
	]
submitProveTask[ args___] := unexpected[ submitProveTask, {args}]

execProveCall[ goal_FML$, kb_, rules:{ruleSet_, active_List, priority_List}, strategy_, searchDepth_, searchTime_, simplification_List] :=
	Module[{po, pv, pt, st},
		{pv, po, pt} = callProver[ rules, strategy, goal, kb, searchDepth, searchTime];
		{po, st} = simplifyProof[ po, simplification];
		printProveInfo[ pv, pt, st];
	]
execProveCall[ args___] := unexpected[ execProveCall, {args}]

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
(*printComputationInfo[] :=
    Module[ {kbAct, bui, buiAct},
        kbAct = Cases[ $tmaEnv, FML$[ k_, _, l_, ___] /; kbSelectCompute[k] -> l];
        bui = Cases[ DownValues[ buiActComputation],
        	HoldPattern[ Verbatim[HoldPattern][ buiActComputation[ op_String]] :> v_] -> {op, v}];
        buiAct = Cases[ bui, { op_, True} -> op];
        CellPrint[ Cell[ ToBoxes[ OpenerView[ {"", 
            Column[ {OpenerView[ {Style[ translate[ "KBcomp"], "CIContent"], Style[ kbAct, "CIContent"]}],
                OpenerView[ {Style[ translate[ "BuiComp"], "CIContent"], Style[ buiAct, "CIContent"]}],
                With[ {kb = Cases[ DownValues[ kbSelectCompute],
                	HoldPattern[ Verbatim[HoldPattern][ kbSelectCompute[ k_List]] :> v_] -> {k, v}],
                    allBui = bui},
                    Button[ translate["RestoreEnv"], setCompEnv[ kb, allBui], ImageSize -> Automatic]
                ]}
            ]}, False]], "ComputationInfo"]];
    ]
*)    
printComputationInfo[ cellID_Integer] := 
	Module[ {nbDir, file},
		nbDir = createPerNotebookDirectory[ CurrentValue[ "NotebookFullFileName"]];
		(* Generate cache only in plain .m format, since this allows sharing notebooks with users on different platforms.
			Also, loading a .m-file allows dynamic objects to react to new settings, whereas loading a .mx-file has no effect on dynamics.
			I assume the speed gain from using mx is neglectable *)
		file = FileNameJoin[ {nbDir, "c" <> ToString[ cellID]}];
		saveComputationCacheDisplay[ cellID, file];
		With[ {fn = file <> "-display.m"},
			CellPrint[ Cell[ "", "ComputationInfo"]];
			CellPrint[ Cell[ BoxData[ ToBoxes[ Dynamic[ Refresh[ Get[ fn], None]]]], "ComputationInfoBody"]]
		];
	]
printComputationInfo[args___] := unexcpected[ printComputationInfo, {args}]
     
setCompEnv[ file_String] :=
	Module[{},
		Clear[ kbSelectCompute];
		Get[ file];
	]
setCompEnv[ args___] := unexpected[ setCompEnv, {args}]

(*
displayComputationCache[ cellID_Integer, dir_String, tab_Integer] :=
	Block[ {kbSelectCompute, buiActComputation},
		Get[ "c" <> ToString[ cellID] <> "`", Path -> {dir}];
		Switch[ tab,
			1, (* display kb *)
			Map[ displayFormulaFromKey, Cases[ DownValues[ kbSelectCompute],
        		HoldPattern[ Verbatim[HoldPattern][ kbSelectCompute[ k_List]] :> True] -> k]],
			2, (* display builtin *)
			summarizeBuiltins[ "compute"],
			_, (* undefined *)
			"???"
		]
	]
displayComputationCache[ cellID_Integer, dir_String, tab_] := displayComputationCache[ cellID, dir, 1]
displayComputationCache[ args___] := unexpected[ displayComputationCache, {args}]
*)
saveComputationCacheDisplay[ cellID_Integer, file_String] :=
	With[ {fn = file <> ".m"},
		Put[ Definition[ buiActComputation], Definition[ kbSelectCompute], fn];
		Put[ 
			TabView[ {
				translate["tcComputeTabKBTabLabel"] -> Map[ displayFormulaFromKey, Cases[ DownValues[ kbSelectCompute],
        			HoldPattern[ Verbatim[HoldPattern][ kbSelectCompute[ k_List]] :> True] -> k]],
        		translate["tcComputeTabBuiltinTabLabel"] -> summarizeBuiltins[ "compute"],
        		translate["RestoreEnv"] -> Row[ {translate["RestoreEnvLong"], Button[ translate[ "OK"], setCompEnv[ fn]]}, Spacer[5]]
				},
				ImageSize -> Automatic
			],
			file <> "-display.m"];
	]	
	
saveComputationCacheDisplay[ args___] := unexpected[ saveComputationCacheDisplay, {args}]

displayFormulaFromKey[ k_List] :=
	Module[ {form},
		form = Select[ $tmaEnv, key[ #] === k&];
		If[ form === {},
			Button[ "???", evalFormulaFromKey[ k], Appearance -> None],
			form = form[[1]];
			Tooltip[ label@form, theoremaDisplay[ formula@form]]
		]
	]
displayFormulaFromKey[ args___] := unexpected[ displayFormulaFromKey, {args}]

evalFormulaFromKey[ k_List] :=
	With[ { file = Part[ StringSplit[ k[[2]], ":"], 2]},
        NotebookLocate[ {file, k[[1]]}];
        FrontEndTokenExecute[ "EvaluateCells"];
       ]
evalFormulaFromKey[ args___] := unexpected[ evalFormulaFromKey, {args}]

(* ::Subsubsection:: *)
(* printProofInfo *)

(*
printProveInfo[ goal_, kb_, rules_, strategy_, {pVal_, proofObj_}, {pTime_, sTime_}, searchDepth_] :=
    Module[ {kbAct, bui, buiAct},
    	(* pTime (prove time) and sTime (simplification time) currently unused, should be displayed somewhere *)
        kbAct = Map[ makeLabel[ label[#]]&, kb];
        bui = Cases[ DownValues[ buiActProve],
        	HoldPattern[ Verbatim[HoldPattern][ buiActProve[ op_String]] :> v_] -> {op, v}];
        buiAct = Cases[ bui, { op_, True} -> op];
        If[ NotebookFind[ $proofInitNotebook, makeProofIDTag[ goal], All, CellTags] === $Failed,
			NotebookFind[ $proofInitNotebook, goal[[1,1]], All, CellTags];
			NotebookFind[ $proofInitNotebook, "CloseEnvironment", Next, CellStyle];
			SelectionMove[ $proofInitNotebook, After, CellGroup],
			SelectionMove[ $proofInitNotebook, All, CellGroup]
		];
		SetSelectedNotebook[ $proofInitNotebook];
        NotebookWrite[ $proofInitNotebook, Cell[ TextData[ {translate[ "Proof of"]<>" ", formulaReference[ goal], ": ", 
        	Cell[ BoxData[ ToBoxes[ proofStatusIndicator[ pVal]]]]}],
        	"OpenProof", CellTags -> makeProofIDTag[ goal]]];
        (* Use Method -> "Queued" so that no time limit for proof display applies *)
        NotebookWrite[ $proofInitNotebook, Cell[ BoxData[ ToBoxes[
        	Button[ translate["ShowProof"], displayProof[ proofObj], ImageSize -> Automatic, Method -> "Queued"]]], "ProofDisplay"]];
        NotebookWrite[ $proofInitNotebook, Cell[ ToBoxes[
        	OpenerView[ {Spacer[10], 
            Column[ {OpenerView[ {Style[ translate[ "GoalProve"], "PIContent"], Style[ makeLabel[ label@goal], "PIContent"]}],
            	OpenerView[ {Style[ translate[ "KBprove"], "PIContent"], Style[ kbAct, "PIContent"]}],
                OpenerView[ {Style[ translate[ "BuiProve"], "PIContent"], Style[ buiAct, "PIContent"]}],
                OpenerView[ {Style[ translate[ "selProver"], "PIContent"], Style[ {rules, strategy}, "PIContent"]}],
                With[ {allKB = Cases[ DownValues[ kbSelectProve],
                	HoldPattern[ Verbatim[HoldPattern][ kbSelectProve[ k_List]] :> v_] -> {k, v}],
                    allBui = bui, allRules = Cases[ DownValues[ ruleActive],
                	HoldPattern[ Verbatim[HoldPattern][ ruleActive[ r_Symbol]] :> v_] -> {r, v}]},
                    Button[ translate["RestoreEnv"], setProveEnv[ goal, allKB, allBui, rules, strategy, allRules, searchDepth], ImageSize -> Automatic]
                ]}
            ]}, False]], "ProofInfo"]];
        NotebookWrite[ $proofInitNotebook, Cell[ "\[EmptySquare]", "CloseProof"]];
    ]
*)
printProveInfo[ pVal_, pTime_, sTime_] := 
	Module[ {nbDir, cellID = getCellIDFromKey[ key@$selectedProofGoal], file},
		nbDir = createPerNotebookDirectory[ CurrentValue[ $proofInitNotebook, "NotebookFullFileName"]];
		(* Generate cache only in plain .m format, since this allows sharing notebooks with users on different platforms.
			Also, loading a .m-file allows dynamic objects to react to new settings, whereas loading a .mx-file has no effect on dynamics.
			I assume the speed gain from using mx is neglectable *)
		file = FileNameJoin[ {nbDir, "p" <> cellID}];
		saveProveCacheDisplay[ pTime, sTime, file];
        If[ NotebookFind[ $proofInitNotebook, makeProofIDTag[ $selectedProofGoal], All, CellTags] === $Failed,
			NotebookFind[ $proofInitNotebook, id@$selectedProofGoal, All, CellTags];
			NotebookFind[ $proofInitNotebook, "CloseEnvironment", Next, CellStyle];
			SelectionMove[ $proofInitNotebook, After, CellGroup],
			SelectionMove[ $proofInitNotebook, All, CellGroup]
		];
		SetSelectedNotebook[ $proofInitNotebook];
		With[ {fnpo = file <> "-po.m", fnd = file <> "-display.m"},
        	NotebookWrite[ $proofInitNotebook, Cell[ TextData[ {Cell[ BoxData[ ToBoxes[ proofStatusIndicator[ pVal]]]], " " <> translate[ "Proof of"] <> " ",
        		formulaReference[ $selectedProofGoal], ":   ",
				Cell[ BoxData[ ToBoxes[ Button[ translate["ShowProof"], displayProof[ Get[ fnpo]], ImageSize -> Automatic, Appearance -> None, Method -> "Queued"]]]]}],
        		"ProofInfo",
        		CellTags -> makeProofIDTag[ $selectedProofGoal],
        		CellFrameLabels -> {{None, Cell[ BoxData[ ButtonBox[ "\[Times]", Evaluator -> Automatic, Appearance -> None, ButtonFunction :> removeGroup[ ButtonNotebook[]]]]]}, {None, None}}]];
			NotebookWrite[ $proofInitNotebook, Cell[ BoxData[ ToBoxes[ Dynamic[ Refresh[ Get[ fnd], None]]]], "ProofInfoBody"]]
		]
	]

printProveInfo[args___] := unexcpected[ printProveInfo, {args}]

removeGroup[ nb_NotebookObject] :=
	Module[{},
		SelectionMove[ nb, All, ButtonCell];
		SelectionMove[ nb, All, CellGroup];
		NotebookDelete[ nb];
	]
removeGroup[][ args___] := unexpected[ removeGroup[], {args}]

(*
setProveEnv[ goal_, kb_List, bui_List, ruleSet_, strategy_, allRules_List, searchDepth_] :=
	Module[{},
		$selectedProofGoal = goal;
		NotebookLocate[ goal[[1,1]]];
		Clear[kbSelectProve];
		kbSelectProve[_] := False;
		Scan[(kbSelectProve[#[[1]]] = #[[2]])&, kb];
		Clear[ruleActive];
		ruleActive[_] := True;
		Scan[(ruleActive[#[[1]]] = #[[2]])&, allRules];
		Scan[(buiActProve[#[[1]]] = #[[2]])&, bui];
		$selectedRuleSet = ruleSet;
		$selectedStrategy = strategy;
		$selectedSearchDepth = searchDepth;
	]
	*)
setProveEnv[ file_String] :=
	Module[ {},
		Clear[ kbSelectProve, ruleActive];
		Get[ file];
	]
setProveEnv[ args___] := unexpected[ setProveEnv, {args}]

makeProofIDTag[ FML$[ id_, _, __]] := Apply[ StringJoin, Riffle[ Prepend[ id, "Proof"], "|"]]
makeProofIDTag[ args___] := unexpected[ makeProofIDTag, {args}]

saveProveCacheDisplay[ pTime_, sTime_, file_String] :=
	With[ {fn = file <> ".m"},
		Put[ Definition[ $TMAproofTree], Definition[ $TMAproofObject], file <> "-po.m"];
		Apply[ Put[ ##, fn]&, Map[ Definition, $allProveSettings]];
		Put[ 
			TabView[ {
				translate["tcProveTabKBTabLabel"] -> Map[ displayFormulaFromKey, Cases[ DownValues[ kbSelectProve],
        			HoldPattern[ Verbatim[HoldPattern][ kbSelectProve[ k_List]] :> True] -> k]],
        		translate["tcProveTabBuiltinTabLabel"] -> summarizeBuiltins[ "prove"],
        		translate["tcProveTabProverTabLabel"] -> summarizeProverSettings[ pTime, sTime],
        		translate["RestoreEnv"] -> Row[ {translate["RestoreEnvLong"], Button[ translate[ "OK"], setProveEnv[ fn]]}, Spacer[5]]
				},
				ImageSize -> Automatic
			],
			file <> "-display.m"];
	]
saveProveCacheDisplay[ args___] := unexpected[ saveProveCacheDisplay, {args}]

summarizeProverSettings[ pTime_, sTime_] :=
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
    					Labeled[ sTime, translate[ "proofSimpTime"] <> ":", Left]
    				}]
			}, AutoAction -> True, ControlPlacement -> Left]
	]
summarizeProverSettings[ args___] := unexpected[ summarizeProverSettings, {args}]


(* ::Section:: *)
(* Palettes *)


insertNewEnv[type_String] :=
    Module[ {nb = InputNotebook[]},
        NotebookWrite[
         nb, {newOpenEnvCell[],
          newEnvHeaderCell[ type],
          newFormulaCell[ type],
          newEndEnvCell[],
          newCloseEnvCell[]}];
    ]
insertNewEnv[args___] :=
    unexpected[insertNewEnv, {args}]

openNewEnv[type_String] :=
    Module[ {},
        NotebookWrite[ InputNotebook[], newOpenEnvCell[]];
        NotebookWrite[ InputNotebook[], newEnvHeaderCell[ type]];
    ]
openNewEnv[args___] :=
    unexpected[openNewEnv, {args}]

insertNewFormulaCell[ style_String] := 
	Module[{}, 
		NotebookWrite[ InputNotebook[], newFormulaCell[ style]];
		(* we use NotebookFind because parameter Placeholder in NotebookWrite does not work (Mma 8.0.1) *)
		NotebookFind[ InputNotebook[], "\[SelectionPlaceholder]", Previous];
	]
insertNewFormulaCell[args___] :=
    unexpected[insertNewFormulaCell, {args}]

closeEnv[] :=
    Module[ {},
        NotebookWrite[ InputNotebook[], {newEndEnvCell[], newCloseEnvCell[]}];
    ]
closeEnv[args___] :=
    unexpected[closeEnv, {args}]

newFormulaCell[ "COMPUTE"] = Cell[BoxData["\[SelectionPlaceholder]"], "Computation"]	
newFormulaCell[ "DECLARATION"] = Cell[BoxData["\[SelectionPlaceholder]"], "GlobalDeclaration"]	
newFormulaCell[ style_, label_:$initLabel] = Cell[BoxData["\[SelectionPlaceholder]"], "FormalTextInputFormula", CellTags->{label}]	
newFormulaCell[args___] :=
    unexpected[newFormulaCell, {args}]

newOpenEnvCell[] := Cell[ "", "OpenEnvironment"]
newOpenEnvCell[args___] :=
    unexpected[newOpenEnvCell, {args}]

newEnvHeaderCell[ type_String] := Cell[ type, "EnvironmentHeader",
	CellFrameLabels -> {{None, 
    	Cell[ BoxData[ ButtonBox[ "\[Times]", Evaluator -> Automatic, Appearance -> None,
    		ButtonFunction :> removeEnvironment[ ButtonNotebook[]]]]]}, {None, None}}]
newEnvHeaderCell[args___] :=
    unexpected[newEnvHeaderCell, {args}]

newEndEnvCell[] := Cell[ "\[GraySquare]", "EndEnvironmentMarker"]
newEndEnvCell[args___] :=
    unexpected[newEndEnvCell, {args}]

newCloseEnvCell[] := Cell[ "", "CloseEnvironment"]
newCloseEnvCell[args___] :=
    unexpected[newCloseEnvCell, {args}]


(* ::Subsection:: *)
(* Buttons *)


makeNbNewButton[] :=
	Button[ translate[ "New"],
		createNbRememberLocation[ ],
		Alignment -> {Left, Top}, Method -> "Queued"]
makeNbNewButton[ args___] := unexpected[ makeNbNewButton, {args}]

makeNbOpenButton[ ] :=
	Button[ translate["Open"],
		openNbRememberLocation[ ],
		Method -> "Queued"
	]
makeNbOpenButton[ args___] := unexpected[ makeNbOpenButton, {args}]
		

envButtonData["DEF"] := "tcSessTabEnvTabButtonDefLabel";
envButtonData["THM"] := "tcSessTabEnvTabButtonThmLabel";
envButtonData["LMA"] := "tcSessTabEnvTabButtonLmaLabel";
envButtonData["PRP"] := "tcSessTabEnvTabButtonPrpLabel";
envButtonData["COR"] := "tcSessTabEnvTabButtonCorLabel";
envButtonData["CNJ"] := "tcSessTabEnvTabButtonCnjLabel";
envButtonData["ALG"] := "tcSessTabEnvTabButtonAlgLabel";
envButtonData["EXM"] := "tcSessTabEnvTabButtonExmLabel";
envButtonData[args___] :=
    unexpected[envButtonData, {args}]

makeEnvButton[ bname_String] :=
    With[ { bd = envButtonData[bname]},
			Button[ translate[bd], insertNewEnv[ translate[bd]], Alignment -> {Left, Top}]
    ]
makeEnvButton[args___] := unexpected[makeEnvButton, {args}]

makeFormButton[] := Button[ translate[ "New"], insertNewFormulaCell[ "Env"], Alignment -> {Left, Top}, ImageSize -> Automatic]
makeFormButton[args___] := unexpected[ makeFormButton, {args}]

makeNewDeclButton[] :=
    Button[ translate[ "New"], insertNewFormulaCell[ "DECLARATION"], Alignment -> {Left, Top}, ImageSize -> Automatic]
makeNewDeclButton[args___] := unexpected[ makeNewDeclButton, {args}]


makeDeclButtons[] := Row[ Map[ makeDeclBut, {"VAR", "VARCOND", "COND", "ABBREV"}], Spacer[5]]
makeDeclButtons[args___] := unexpected[ makeDeclButtons, {args}]

showDecl[ ] := OpenerView[ {Style[ translate["tcSessTabEnvTabButtonAllDeclLabel"], "SmallHeader"], displayDecl[]}, Dynamic[$tcAllDeclOpener]]
showDecl[ args___] := unexpected[ showDecl, {args}]

displayDecl[ ] :=
	Row[ {
		Pane[ $TMAactDecl, {300, 50}, ImageSizeAction -> "Scrollable", Scrollbars -> Automatic],
		Tooltip[ Button[ Style[ "\[LightBulb]", {Medium, Bold}], $TMAactDecl = displayGlobalDeclarations[ InputNotebook[]]], translate[ "tcSessTabEnvTabButtonDeclLabel"]]
		}, Spacer[5]]
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

showEnv[ ] := OpenerView[ {Style[ translate["tcSessTabEnvTabButtonAllFormLabel"], "SmallHeader"], displayEnv[]}, Dynamic[$tcAllFormulaeOpener]]
showEnv[ args___] := unexpected[ showEnv, {args}]

displayEnv[ ] :=
	If[ $tmaEnv === {},
		emptyPane[ "", {350, 30}],
		Pane[ displayLabeledFormulaListGrid[ $tmaEnv], {340, 250}, ImageSizeAction -> "Scrollable", Scrollbars -> Automatic]
	]
displayEnv[ args___] := unexpected[ displayEnv, {args}]
   
allEnvironments = {"DEF", "THM", "LMA", "PRP", "COR", "CNJ", "ALG", "EXM"};

sessionCompose[] :=
    Column[{
    	Labeled[ Row[ {makeNbNewButton[], makeNbOpenButton[]}, Spacer[5]],
    		translate[ "Notebooks"], {{Top, Left}}],
    	Labeled[ Grid[ Partition[ Map[ makeEnvButton, allEnvironments], 4]],
    		translate[ "Environments"], {{Top, Left}}],
    	Labeled[ Column[ {makeFormButton[], Dynamic[ Refresh[ langButtons[], TrackedSymbols :> {$buttonNat, $tcLangButtonSelection}]]}, Left, Spacer[2]],
    		translate[ "Formulae"], {{Top, Left}}],
    	Labeled[ Column[ {makeNewDeclButton[], makeDeclButtons[]}, Left, Spacer[2]],
    		translate[ "Declarations"], {{Top, Left}}]
    }]
sessionCompose[args___] :=
    unexpected[sessionCompose, {args}]

sessionInspect[ ] :=
	Column[{
    	Labeled[ Column[ {Dynamic[ showEnv[]]}, Left, Spacer[2]],
    		translate[ "Formulae"], {{Top, Left}}],
    	Labeled[ Column[ {Dynamic[ showDecl[]]}, Left, Spacer[2]],
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
            makeArchLoadButton[]}], translate[ "tcLangTabArchTabSectionLoad"], {{Top, Left}}]
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


(* ::Section:: *)
(* Preferences Tab *)


setPreferences[ ] :=
	Column[ {
	Column[ {
		Labeled[ PopupMenu[Dynamic[$Language], availableLanguages[]], translate["tcPrefLanguage"], {{Top, Left}}],
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
		alias = Map[ langButtonData[ #][[4]] -> RowBox[ {autoParenthesis[ "("], langButtonData[ #][[2]], autoParenthesis[ ")"]}]&, 
			Cases[ Flatten[ Transpose[ allFormulae][[2]]], _String]];
		alias = Join[ alias, {"(" -> autoParenthesis[ "("], ")" -> autoParenthesis[ ")"]}];
		styles /. Table[Apply[CMYKColor, IntegerDigits[i, 2, 4]] -> TMAcolor[i, color], {i, 0, 15}] /. (InputAliases -> {}) -> (InputAliases -> alias)
	]
makeColoredStylesheet[ args___] := unexpected[ makeColoredStylesheet, {args}]

isTheoremaNotebook[ nb_NotebookObject] := Not[ FreeQ[ Options[ nb, CounterAssignments], "TheoremaFormulaCounter" -> _Integer]]
isTheoremaNotebook[ args___] := unexpected[ isTheoremaNotebook, {args}]


savePreferencesButton[ ] :=
    Module[ {prefsFile = FileNameJoin[{$UserBaseDirectory, "Applications", "Theorema", "Kernel", "TheoremaPreferences.m"}]},
        $prefsSaveStatus = If[FileExistsQ[ prefsFile],
        	DateString[ FileDate[ prefsFile]],
        	"\[LongDash]"];
        Column[{
        	Dynamic[ Refresh[ Row[{
        	translate["preferences last saved: "],
            $prefsSaveStatus <> If[ {$Language, $TheoremaArchiveDirectory, $TheoremaColorScheme, $suppressWelcomeScreen, $buttonNat} === $savedValues,
                                        " \[Checkmark]",
                                        ""
                                    ]}], TrackedSymbols :> {$Language, $TheoremaArchiveDirectory, $TheoremaColorScheme, $suppressWelcomeScreen, $buttonNat, $prefsSaveStatus}]],
         Button[ translate["save current settings"], savePreferences[]]
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
		$savedValues = {$Language, $TheoremaArchiveDirectory, $TheoremaColorScheme, $suppressWelcomeScreen, $buttonNat};
		Save[ prefsFile, {$Language, $TheoremaArchiveDirectory, $TheoremaColorScheme, $suppressWelcomeScreen, $buttonNat, $savedValues}];
		$prefsSaveStatus = DateString[ FileDate[ FileNameJoin[{$UserBaseDirectory, "Applications", "Theorema", "Kernel", "TheoremaPreferences.m"}]]];
	]
savePreferences[ args___] := unexpected[ savePreferences, {args}]



(* ::Section:: *)
(* Math Tab *)

langButtonData["AND1"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["AND1"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[Wedge]",
				TagBox[ FrameBox["right"], "Placeholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]", "\[Wedge]", "\[Placeholder]"}],
		translate["CONN2STRONGTooltip"],
		""
	}

langButtonData["AND2"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["AND2"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[And]",
				TagBox[ FrameBox["right"], "Placeholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]", "\[And]", "\[Placeholder]"}],
		translate["CONN2WEAKTooltip"],
		"and"
	}
	
langButtonData["AND3"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["AND3"], 
			DisplayForm[RowBox[{"\[And]", "\[Piecewise]", GridBox[{{TagBox[ FrameBox[SubscriptBox["e","1"]], "SelectionPlaceholder"]},
				{"\[VerticalEllipsis]"},
				{TagBox[ FrameBox[SubscriptBox["e","n"]], "Placeholder"]}}]}]]],
		RowBox[{"\[And]", "\[Piecewise]", GridBox[{{"\[SelectionPlaceholder]"}, {"\[Placeholder]"}}]}],
		translate["CONNTooltip"],
		"andn"
	}
	
langButtonData["NOT"] := 
	{
		If[ $buttonNat, 
			translate["NOT"], 
			DisplayForm[RowBox[{"\[Not]",
				TagBox[ FrameBox["form"], "SelectionPlaceholder"]}]]],
		RowBox[{"\[Not]", "\[SelectionPlaceholder]"}],
		translate["NOTTooltip"],
		"not"
	}

langButtonData["OR1"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["OR1"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[Vee]",
				TagBox[ FrameBox["right"], "Placeholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]", "\[Vee]", "\[Placeholder]"}],
		translate["CONN2STRONGTooltip"],
		""
	}

langButtonData["OR2"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["OR2"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[Or]",
				TagBox[ FrameBox["right"], "Placeholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]", "\[Or]", "\[Placeholder]"}],
		translate["CONN2WEAKTooltip"],
		"or"
	}
	
langButtonData["OR3"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["OR3"], 
			DisplayForm[RowBox[{"\[Or]", "\[Piecewise]", GridBox[{{TagBox[ FrameBox[SubscriptBox["e","1"]], "SelectionPlaceholder"]},
				{"\[VerticalEllipsis]"},
				{TagBox[ FrameBox[SubscriptBox["e","n"]], "Placeholder"]}}]}]]],
		RowBox[{"\[Or]", "\[Piecewise]", GridBox[{{"\[SelectionPlaceholder]"}, {"\[Placeholder]"}}]}],
		translate["CONNTooltip"],
		"orn"
	}

langButtonData["IMPL1"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["IMPL1"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[DoubleLongRightArrow]",
				TagBox[ FrameBox["right"], "Placeholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]",
			TagBox[ "\[DoubleLongRightArrow]", Identity, SyntaxForm->"a\[DoubleRightArrow]b"], "\[Placeholder]"}],
		translate["CONN2STRONGTooltip"],
		""
	}

langButtonData["IMPL2"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["IMPL2"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[Implies]",
				TagBox[ FrameBox["right"], "Placeholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]", "\[Implies]", "\[Placeholder]"}],
		translate["CONN2WEAKTooltip"],
		"impl"
	}

langButtonData["EQUIV1"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["EQUIV1"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[DoubleLongLeftRightArrow]",
				TagBox[ FrameBox["right"], "Placeholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]",
			TagBox[ "\[DoubleLongLeftRightArrow]", Identity, SyntaxForm->"a\[DoubleRightArrow]b"], "\[Placeholder]"}],
		translate["CONN2STRONGTooltip"],
		""
	}

langButtonData["EQUIV2"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["EQUIV2"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[DoubleLeftRightArrow]",
				TagBox[ FrameBox["right"], "Placeholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]",
			TagBox[ "\[DoubleLeftRightArrow]", Identity, SyntaxForm->"a\[Implies]b"], "\[Placeholder]"}],
		translate["CONN2WEAKTooltip"],
		"equiv"
	}
	
langButtonData["EQUIV3"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["EQUIV3"], 
			DisplayForm[RowBox[{"\[DoubleLeftRightArrow]", "\[Piecewise]", GridBox[{{TagBox[ FrameBox[SubscriptBox["e","1"]], "SelectionPlaceholder"]},
				{"\[VerticalEllipsis]"},
				{TagBox[ FrameBox[SubscriptBox["e","n"]], "Placeholder"]}}]}]]],
		RowBox[{"\[DoubleLeftRightArrow]", "\[Piecewise]", GridBox[{{"\[SelectionPlaceholder]"}, {"\[Placeholder]"}}]}],
		translate["CONNTooltip"],
		"equivn"
	}

langButtonData["EQ"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["EQ1"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[Equal]",
				TagBox[ FrameBox["right"], "Placeholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]", "\[Equal]", "\[Placeholder]"}],
		translate["CONN2Tooltip"],
		"eq"
	}

langButtonData["EQ2"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["EQ2"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"=",
				TagBox[ FrameBox["right"], "Placeholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]",
			TagBox[ "=", Identity, SyntaxForm->"a\[Equal]b"], "\[Placeholder]"}],
		translate["CONN2Tooltip"],
		""
	}

langButtonData["EQUIVDEF"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["EQUIVDEF"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				RowBox[{":", "\[NegativeThickSpace]\[NegativeThinSpace]", "\[DoubleLongLeftRightArrow]"}],
				TagBox[ FrameBox["right"], "Placeholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]",
			TagBox[ RowBox[{":", "\[NegativeThickSpace]\[NegativeThinSpace]", "\[DoubleLongLeftRightArrow]"}], Identity, SyntaxForm->"a\[Implies]b"], "\[Placeholder]"}],
		translate["EQUIVDEFTooltip"],
		":equiv"
	}

langButtonData["EQDEF"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["EQDEF"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				":=",
				TagBox[ FrameBox["right"], "Placeholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]", ":=", "\[Placeholder]"}],
		translate["EQDEFTooltip"],
		":eq"
	}

langButtonData["FORALL1"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["FORALL1"], 
			DisplayForm[RowBox[{UnderscriptBox[StyleBox["\[ForAll]", FontSize->14], Placeholder["rg"]], SelectionPlaceholder["expr"]}]]],
		RowBox[{UnderscriptBox["\[ForAll]", "\[Placeholder]"], "\[SelectionPlaceholder]"}],
		translate["QUANT1Tooltip"],
		"far"
	}

langButtonData["FORALL2"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["FORALL2"], 
			DisplayForm[RowBox[{UnderscriptBox[ UnderscriptBox[StyleBox["\[ForAll]", FontSize->14], Placeholder["rg"]], Placeholder["cond"]], SelectionPlaceholder["expr"]}]]],
		RowBox[{UnderscriptBox[ UnderscriptBox["\[ForAll]", "\[Placeholder]"], "\[Placeholder]"], "\[SelectionPlaceholder]"}],
		translate["QUANT2Tooltip"],
		"farc"
	}
	
langButtonData["EXISTS1"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["EXISTS1"], 
			DisplayForm[RowBox[{UnderscriptBox[StyleBox["\[Exists]", FontSize->14], Placeholder["rg"]], SelectionPlaceholder["expr"]}]]],
		RowBox[{UnderscriptBox["\[Exists]", "\[Placeholder]"], "\[SelectionPlaceholder]"}],
		translate["QUANT1Tooltip"],
		"exr"
	}

langButtonData["EXISTS2"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["EXISTS2"], 
			DisplayForm[RowBox[{UnderscriptBox[ UnderscriptBox[StyleBox["\[Exists]", FontSize->14], Placeholder["rg"]], Placeholder["cond"]], SelectionPlaceholder["expr"]}]]],
		RowBox[{UnderscriptBox[ UnderscriptBox["\[Exists]", "\[Placeholder]"], "\[Placeholder]"], "\[SelectionPlaceholder]"}],
		translate["QUANT2Tooltip"],
		"exrc"
	}
	
langButtonData["LET"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["LET"], 
			DisplayForm[RowBox[{UnderscriptBox[ "let", RowBox[ {Placeholder["a"], "=", Placeholder["x"]}]], SelectionPlaceholder["expr"]}]]],
		RowBox[{UnderscriptBox[ "let", RowBox[ {"\[Placeholder]", "=", "\[Placeholder]"}]], "\[SelectionPlaceholder]"}],
		translate["LETTooltip"],
		"let"
	}
	
langButtonData["CASEDIST"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["CASEDIST"], 
			DisplayForm[RowBox[{"\[Piecewise]",
				GridBox[{
					{TagBox[ FrameBox[SubscriptBox["e","1"]], "SelectionPlaceholder"], "\[DoubleLeftArrow]", TagBox[ FrameBox[SubscriptBox["c","1"]], "Placeholder"]},
					{"", "\[VerticalEllipsis]", ""},
					{TagBox[ FrameBox[SubscriptBox["e","n"]], "Placeholder"], "\[DoubleLeftArrow]", TagBox[ FrameBox[SubscriptBox["c","n"]], "Placeholder"]}
				}]
			}]]],
		RowBox[{"\[Piecewise]",
			GridBox[{
				{"\[SelectionPlaceholder]", "\[DoubleLeftArrow]", "\[Placeholder]"},
				{"\[Placeholder]", "\[DoubleLeftArrow]", "\[Placeholder]"}
			}]
		}],
		translate["CASEDISTTooltip"],
		"cdist"
	}
	
langButtonData["SINGLEOP"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["SINGLEOP"], 
			DisplayForm[ TagBox[ FrameBox["\[CircleDot]"], "SelectionPlaceholder"]]],
		TagBox[ "\[SelectionPlaceholder]", Identity],
		translate["0ANNOPTooltip"],
		"op"
	}
	
langButtonData["OVEROP"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["OVEROP"], 
			DisplayForm[ OverscriptBox[ TagBox[ FrameBox["\[CircleDot]"], "SelectionPlaceholder"],
										TagBox[ FrameBox["A"], "Placeholder"]]]],
		OverscriptBox[ "\[SelectionPlaceholder]", "\[Placeholder]"],
		translate["1ANNOPTooltip"],
		"oop"
	}
	
langButtonData["UNDEROVEROP"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["UNDEROVEROP"], 
			DisplayForm[ UnderoverscriptBox[ TagBox[ FrameBox["\[CircleDot]"], "SelectionPlaceholder"],
										TagBox[ FrameBox["A"], "Placeholder"],
										TagBox[ FrameBox["B"], "Placeholder"]]]],
		UnderoverscriptBox[ "\[SelectionPlaceholder]", "\[Placeholder]", "\[Placeholder]"],
		translate["2ANNOPTooltip"],
		"uoop"
	}
	
langButtonData["SUBOP"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["SUBOP"], 
			DisplayForm[ SubscriptBox[ TagBox[ FrameBox["\[CircleDot]"], "SelectionPlaceholder"],
										TagBox[ FrameBox["A"], "Placeholder"]]]],
		SubscriptBox[ "\[SelectionPlaceholder]", "\[Placeholder]"],
		translate["1ANNOPTooltip"],
		"subop"
	}
	
langButtonData["SUPEROP"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["SUPEROP"], 
			DisplayForm[ SuperscriptBox[ TagBox[ FrameBox["\[CircleDot]"], "SelectionPlaceholder"],
										TagBox[ FrameBox["A"], "Placeholder"]]]],
		SuperscriptBox[ "\[SelectionPlaceholder]", "\[Placeholder]"],
		translate["1ANNOPTooltip"],
		"supop"
	}
	
langButtonData["SUBSUPEROP"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["SUBSUPEROP"], 
			DisplayForm[ SubsuperscriptBox[ TagBox[ FrameBox["\[CircleDot]"], "SelectionPlaceholder"],
										TagBox[ FrameBox["A"], "Placeholder"],
										TagBox[ FrameBox["B"], "Placeholder"]]]],
		SubsuperscriptBox[ "\[SelectionPlaceholder]", "\[Placeholder]", "\[Placeholder]"],
		translate["2ANNOPTooltip"],
		"subsupop"
	}
	
langButtonData["OVERSUBOP"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["OVERSUBOP"], 
			DisplayForm[ SubscriptBox[ OverscriptBox[ TagBox[ FrameBox["\[CircleDot]"], "SelectionPlaceholder"],
													TagBox[ FrameBox["A"], "Placeholder"]],
										TagBox[ FrameBox["B"], "Placeholder"]]]],
		SubscriptBox[ OverscriptBox[ "\[SelectionPlaceholder]", "\[Placeholder]"], "\[Placeholder]"],
		translate["2ANNOPTooltip"],
		"osop"
	}

langButtonData["APPEND"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["APPEND"], 
			"\:293a"],
		RowBox[ {"\[SelectionPlaceholder]", TagBox[ "\:293a", Identity, SyntaxForm -> "a*b"], "\[Placeholder]"}],
		MessageName[ appendElem$TM, "usage"],
		"app"
	}
	
langButtonData["PREPEND"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["PREPEND"], 
			"\:293b"],
		RowBox[ {"\[SelectionPlaceholder]", TagBox[ "\:293b", Identity, SyntaxForm -> "a*b"], "\[Placeholder]"}],
		MessageName[ prependElem$TM, "usage"],
		"prep"
	}
	
langButtonData["JOIN"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["JOIN"], 
			"\:2a1d"],
		RowBox[ {"\[SelectionPlaceholder]", TagBox[ "\:2a1d", Identity, SyntaxForm -> "a*b"], "\[Placeholder]"}],
		MessageName[ joinTuples$TM, "usage"],
		"join"
	}
	
langButtonData["ELEMTUP"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["ELEMTUP"], 
			"\:22ff"],
		RowBox[ {"\[SelectionPlaceholder]", TagBox[ "\:22ff", Identity, SyntaxForm -> "a+b"], "\[Placeholder]"}],
		MessageName[ elemTuple$TM, "usage"],
		"elemT"
	}

langButtonData["[]"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["[]"], 
			"[ ]"],
		RowBox[ {TagBox[ "\:e114", Identity, SyntaxForm -> "("], "\[SelectionPlaceholder]", TagBox[ "\:e115", Identity, SyntaxForm -> ")"]}],
		MessageName[ squareBracketted$TM, "usage"],
		"[]"
	}

langButtonData["[[]]"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["[[]]"], 
			"[[ ]]"],
		RowBox[ {TagBox[ "\:27e6", Identity, SyntaxForm -> "("], "\[SelectionPlaceholder]", TagBox[ "\:27e7", Identity, SyntaxForm -> ")"]}],
		MessageName[ doubleSquareBracketted$TM, "usage"],
		"[[]]"
	}

langButtonData["<>"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["<>"], 
			"\[LeftAngleBracket] \[RightAngleBracket]"],
		RowBox[ {TagBox[ "\:27e8", Identity, SyntaxForm -> "("], "\[SelectionPlaceholder]", TagBox[ "\:27e9", Identity, SyntaxForm -> ")"]}],
		MessageName[ angleBracketted$TM, "usage"],
		"<>"
	}
	
langButtonData["<<>>"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["<<>>"], 
			"\[LeftAngleBracket]\[LeftAngleBracket] \[RightAngleBracket]\[RightAngleBracket]"],
		RowBox[ {TagBox[ "\:27ea", Identity, SyntaxForm -> "("], "\[SelectionPlaceholder]", TagBox[ "\:27eb", Identity, SyntaxForm -> ")"]}],
		MessageName[ doubleAngleBracketted$TM, "usage"],
		"<<>>"
	}
	
langButtonData["{}"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["{}"], 
			"{ }"],
		RowBox[ {TagBox[ "\:e117", Identity, SyntaxForm -> "("], "\[SelectionPlaceholder]", TagBox[ "\:e118", Identity, SyntaxForm -> ")"]}],
		MessageName[ braced$TM, "usage"],
		"{}"
	}
	
langButtonData["{{}}"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["{{}}"], 
			"{{ }}"],
		RowBox[ {TagBox[ "\:2983", Identity, SyntaxForm -> "("], "\[SelectionPlaceholder]", TagBox[ "\:2984", Identity, SyntaxForm -> ")"]}],
		MessageName[ doubleBraced$TM, "usage"],
		"{{}}"
	}
	
langButtonData["()"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["()"], 
			"( )"],
		RowBox[ {TagBox[ "\:fd3e", Identity, SyntaxForm -> "("], "\[SelectionPlaceholder]", TagBox[ "\:fd3f", Identity, SyntaxForm -> ")"]}],
		MessageName[ parenthesized$TM, "usage"],
		"()"
	}
	
langButtonData["(())"] := 
	{
		If[ TrueQ[ $buttonNat], 
			translate["(())"], 
			"(( ))"],
		RowBox[ {TagBox[ "\:2e28", Identity, SyntaxForm -> "("], "\[SelectionPlaceholder]", TagBox[ "\:2e29", Identity, SyntaxForm -> ")"]}],
		MessageName[ doubleParenthesized$TM, "usage"],
		"(())"
	}
	
langButtonData[args___] :=
    unexpected[langButtonData, {args}]

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
					FrontEndExecute[{NotebookApply[ InputNotebook[], paste, Placeholder]}],
					FrontEndExecute[{NotebookApply[ InputNotebook[], RowBox[ {autoParenthesis[ "("], paste, autoParenthesis[ ")"]}], Placeholder]}]
				], Appearance -> "DialogBox", Alignment -> {Left, Top}, ImageSize -> All],
				help <> translate[ "tooltipButtonParen"]<>" \[EscapeKey]"<> key <>"\[EscapeKey]", TooltipDelay -> 0.5]
    	]
    ]
makeLangButton[ {bname_String, 2}] :=
    With[ { bd = langButtonData[ bname]},
    	With[ {lab = bd[[1]], paste = bd[[2]], help = bd[[3]], key = bd[[4]]},
			Tooltip[ Button[ lab,
				FrontEndExecute[{NotebookApply[ InputNotebook[], paste, Placeholder]}], 
				Appearance -> "DialogBox", Alignment -> {Left, Top}, ImageSize -> All],
				help <> translate[ "tooltipButtonNoParen"]<>" \[EscapeKey]"<> key <>"\[EscapeKey]", TooltipDelay -> 0.5]
    	]
    ]
makeLangButton[args___] :=
    unexpected[makeLangButton, {args}]

(*
	We use TagBox because StyleBox did not work together with InputAliases: when entering formulae with alias, some StyleBoxes vanished
	for unknown reasons. With TagBox it works.
*)
autoParenthesis[ c_String] := TagBox[ c, "AutoParentheses"]
autoParenthesis[ args___] := unexpected[ autoParenthesis, {args}]

allFormulae = {
			   {"Arithmetic", {}},
			   {"Logic", {{{"AND2", 1}, {"OR2", 1}, {"NOT", 1}, {"IMPL2", 1}}, 
			   	{{"EQUIV2", 1}, {"EQ", 1}, {"EQUIVDEF", 1}, {"EQDEF", 1}}, 
			   	{{"AND3", 1}, {"OR3", 1}, {"EQUIV3", 1}, {"CASEDIST", 1}}, 
			   	{{"FORALL1", 1}, {"EXISTS1", 1}, {"FORALL2", 1}, {"EXISTS2", 1}}, 
			   	{{"LET", 1}}}},
			   {"Sets", {}},
			   {"Tuples", {{{"APPEND", 1}, {"PREPEND", 1}, {"JOIN", 1}, {"ELEMTUP", 1}}}},
			   {"Operators", {{{"SUBOP", 1}, {"SUPEROP", 1}, {"SUBSUPEROP", 1}}, 
			   	{{"OVEROP", 1}, {"UNDEROVEROP", 1}, {"OVERSUBOP", 1}}, 
			   	{{"SINGLEOP", 1}}}},
			   {"Bracketted", {{{"[]", 2}, {"()", 2}, {"<>", 2}, {"{}", 2}}, 
			   	{{"[[]]", 2}, {"(())", 2}, {"<<>>", 2}, {"{{}}", 2}}}}
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
			Row[ Map[ Button[ #, $tcLangButtonSelection = #, 
				Background -> If[ $tcLangButtonSelection === #, TMAcolor[0], TMAcolor[5]], FrameMargins -> 2, ImageMargins -> 0]&, Map[ First, display]]],
    		PaneSelector[ display, Dynamic[ $tcLangButtonSelection], ImageSize -> {350, Automatic}]
		}]
	]

langButtons[args___] :=
    unexpected[langButtons, {args}]
    
compSetup[] := 
	Column[{
		makeCompButton[]
	}, Dividers -> Center, Spacings -> 4]
compSetup[args___] :=
    unexpected[compSetup, {args}]

makeCompButton[] :=
    Button[ translate[ "New"], insertNewFormulaCell[ "COMPUTE"], Alignment -> {Left, Top}]
makeCompButton[args___] := unexpected[makeCompButton, {args}]


partitionFill[ l_List, n_Integer, default_:""] := Partition[ PadRight[ l, n*Ceiling[ Length[ l]/n], default], n]
partitionFill[ args___] := unexpected[ partitionFill, {args}]

(* ::Section:: *)
(* Windowing functions *)

tmaNotebookPut[ nb_Notebook, style_String, opts___?OptionQ] :=
	NotebookPut[ nb, 
		StyleDefinitions -> makeColoredStylesheet[ style],
		Magnification -> CurrentValue[ First[ getTheoremaCommander[]], Magnification],
		opts
	]
tmaNotebookPut[ args___] := unexpected[ tmaNotebookPut, {args}]

tmaDialogInput[ Notebook[ expr_, nbOpts___?OptionQ], style_String, opts___?OptionQ] :=
	DialogInput[ 
		Notebook[ expr, 
			StyleDefinitions -> makeColoredStylesheet[ style],
			Magnification -> CurrentValue[ First[ getTheoremaCommander[]], Magnification],
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
(* end of package *)

If[ $Notebooks,
	openTheoremaCommander[]
];

End[]; (* End Private Context *)

EndPackage[];
