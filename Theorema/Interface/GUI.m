(* Theorema 
    Copyright (C) 2010 The Theorema Group

    This file is part of Theorema.2
    
    Theorema.2 is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Theorema.2 is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

BeginPackage["Theorema`Interface`GUI`"];
(* Exported symbols added here with SymbolName::usage *)  

Needs["Theorema`Common`"]
Needs["Theorema`Interface`Language`"]

Begin["`Private`"] (* Begin Private Context *) 


(* ::Section:: *)
(* initGUI *)

initGUI[] := 
	Module[{ tc}, 
        $tmaBuiltins = {
        	{"Sets", 
        		{"union", RowBox[{"A","\[Union]","B"}]},
        		{"intersection", RowBox[{"A","\[Intersection]","B"}]},
        		{"equal", RowBox[{"A","=","B"}]}},
        	{"Arithmetic", 
        		{"plus", RowBox[{"A","+","B"}]},
        		{"times", RowBox[{"A","*","B"}]},
        		{"equal", RowBox[{"A","=","B"}]}}
        };
		$kbStruct = {};
		$initLabel = "???";
		$labelSeparator = ",";
		If[ ValueQ[$theoremaGUI], tc = "Theorema Commander" /. $theoremaGUI];
		If[ $Notebooks && MemberQ[Notebooks[], tc], NotebookClose[tc]];
		$theoremaGUI = {"Theorema Commander" -> theoremaCommander[]};
	]

(* ::Section:: *)
(* theoremaCommander *)

theoremaCommander[] /; $Notebooks :=
    Module[ {style = Replace[ScreenStyleEnvironment,Options[InputNotebook[], ScreenStyleEnvironment]]},
        CreatePalette[ Dynamic[Refresh[
        	TabView[{
        		translate["tcLangTabLabel"]->TabView[{
        			translate["tcLangTabMathTabLabel"]->Dynamic[Refresh[ langButtons[], TrackedSymbols :> {$buttonNat}]],
        			translate["tcLangTabEnvTabLabel"]->envButtons[]}, Dynamic[$tcLangTab],
        			ControlPlacement->Top],
        		translate["tcProveTabLabel"]->TabView[{
        			translate["tcProveTabKBTabLabel"]->Dynamic[Refresh[displayKBBrowser["prove"], TrackedSymbols :> {$kbStruct}]],
        			translate["tcProveTabBuiltinTabLabel"]->displayBuiltinBrowser[]}, Dynamic[$tcProveTab],
        			ControlPlacement->Top],
        		translate["tcComputeTabLabel"]->TabView[{
        			translate["tcComputeTabSetupTabLabel"]->Dynamic[Refresh[ compSetup[], TrackedSymbols :> {$buttonNat}]],
        			translate["tcComputeTabKBTabLabel"]->Dynamic[Refresh[displayKBBrowser["compute"], TrackedSymbols :> {$kbStruct}]],
        			translate["tcComputeTabBuiltinTabLabel"]->displayBuiltinBrowser[]}, Dynamic[$tcCompTab],
        			ControlPlacement->Top],
        		translate["tcPreferencesTabLabel"]->Row[{translate["tcPrefLanguage"], PopupMenu[Dynamic[$Language], availableLanguages[]]}, Spacer[10]]},
        		Dynamic[$tcTopLevelTab],
        		LabelStyle->{Bold}, ControlPlacement->Left
        	], TrackedSymbols :> {$Language}]],
        	StyleDefinitions -> ToFileName[{"Theorema"}, "GUI.nb"],
        	WindowTitle -> "Theorema Commander",
        	ScreenStyleEnvironment -> style,
        	WindowElements -> {"StatusArea"}]
    ]

emptyPane[text_String:""]:=Pane[text, Alignment->{Center,Center}]
 
(* ::Subsubsection:: *)
(* extractKBStruct *)

(*
Documentation see /ProgrammersDoc/GUIDoc.nb#496401653
*)

extractKBStruct[nb_NotebookObject] := extractKBStruct[ NotebookGet[nb]];

extractKBStruct[nb_Notebook] :=
    Module[ {posTit = Cases[Position[nb, Cell[_, "Title", ___]], {a___, 1}],
      posSec = Cases[Position[nb, Cell[_, "Section", ___]], {a___, 1}], 
      posSubsec = Cases[Position[nb, Cell[_, "Subsection", ___]], {a___, 1}], 
      posSubsubsec = Cases[Position[nb, Cell[_, "Subsubsection", ___]], {a___, 1}], 
      posEnv = Cases[Position[nb, Cell[_, "OpenEnvironment", ___]], {a___, 1}], 
      posInp = Position[nb, Cell[_, "FormalTextInputFormula", ___]], inputs, depth, sub, root, heads, isolated},
        heads = Join[posEnv, posSubsubsec, posSubsec, posSec, posTit];
        {inputs, isolated} = Fold[arrangeInput, {Map[List, heads], {}}, posInp];
        depth = Union[Map[Length[#[[1]]] &, inputs]];
        While[Length[depth] > 1,
         sub = Select[inputs, Length[#[[1]]] == depth[[-1]] &];
         root = Select[inputs, Length[#[[1]]] < depth[[-1]] &];
         inputs = Fold[arrangeSub, root, sub];
         depth = Drop[depth, -1];
         ];
        Join[isolated, inputs]
    ]

extractKBStruct[args___] :=
    unexpected[extractKBStruct, {args}]


(* ::Subsubsection:: *)
(* arrangeInput *)

arrangeInput[{struct_, isolated_}, item_] :=
    Module[ {l, root, pos},
        pos = Do[
          root = Drop[struct[[i, 1]], -1];
          l = Length[root];
          If[ Length[item] > l && Take[item, l] == root,
              Return[i]
          ],
          {i, Length[struct]}];
        If[ NumberQ[pos],
            {Insert[struct, item, {pos, -1}], isolated},
            {struct, Insert[isolated, {item}, -1]}
        ]
    ]

arrangeSub[struct_, item : {head_, ___}] :=
    Module[ {l, root, pos},
        pos = Do[
          root = Drop[struct[[i, 1]], -1];
          l = Length[root];
          If[ Length[head] > l && Take[head, l] == root,
              Return[i]
          ],
          {i, Length[struct]}];
        If[ NumberQ[pos],
            Insert[struct, item, {pos, -1}],
            Insert[struct, {item}, 2]
        ]
    ]

(* ::Subsubsection:: *)
(* structView *)
Clear[structView];

structView[file_, {head:Cell[sec_, style:"Title"|"Section"|"Subsection"|"Subsubsection"|"OpenEnvironment", ___], rest__}, tags_, task_] :=
    Module[ {sub, compTags},
        sub = Transpose[Map[structView[file, #, tags, task] &, {rest}]];
        compTags = Apply[Union, sub[[2]]];
        {OpenerView[{structView[file, head, compTags, task], Column[sub[[1]]]}, 
        	ToExpression[StringReplace["Dynamic[NEWSYM]", 
        		"NEWSYM" -> "$kbStructState$"<>ToString[Hash[FileBaseName[file]]]<>"$"<>style<>"$"<>ToString[Hash[sec]]]]], 
         compTags}
    ]

structView[file_, {Cell[sec_, style:"Section"|"Subsection"|"Subsubsection", ___]}, tags_, task_] :=
	Sequence[]
 
structView[file_, item_List, tags_, task_] :=
    Module[ {sub, compTags},
        sub = Transpose[Map[structView[file, #, tags, task] &, item]];
        compTags = Apply[Union, sub[[2]]];
        {Column[sub[[1]]], compTags}
    ]

structView[file_, Cell[content_, "FormalTextInputFormula", ___], tags_, task_] :=
    Sequence[]
    
structView[file_, Cell[content_, "FormalTextInputFormula", ___, CellTags -> cellTags_, ___,CellID -> cellID_,___], 
  tags_, task_] :=
  Module[ { isEval = MemberQ[ $tmaEnv, {cellTags,_}], cleanCellTags, formulaLabel},
	Assert[VectorQ[cellTags, StringQ]];
	cleanCellTags = Select[cellTags, # != ToString[cellID] && # != $initLabel  & ];
	(* Join list of CellTags, use $labelSeparator. *)
	formulaLabel = StringJoin @@ Riffle[cleanCellTags,$labelSeparator];
    {Switch[ task,
    	"prove",
    	Row[{Checkbox[Dynamic[kbSelectProve[cellTags]], Enabled->isEval], 
    		Hyperlink[ Style[formulaLabel, If[ isEval, "FormalTextInputFormula", "FormalTextInputFormulaUneval"]], {file, ToString[cellID]}]},
    		Spacer[10]],
    	"compute",
    	Row[{Checkbox[Dynamic[Theorema`Computation`activeComputationKB[cellTags]], Enabled->isEval], 
    		Hyperlink[ Style[formulaLabel, If[ isEval, "FormalTextInputFormula", "FormalTextInputFormulaUneval"]], {file, ToString[cellID]}]},
    		Spacer[10]]
    	], {formulaLabel}}
  ]

(*structView[file_, Cell[content_, "FormalTextInputFormula", ___, CellTags -> ct_, ___], 
  tags_] :=
  Module[ { isEval = MemberQ[ $tmaEnv, {_,ct}, Infinity]},
    {Row[{Checkbox[Dynamic[isSelected[ct]], Enabled->isEval], Hyperlink[ Style[ct, If[ isEval, "FormalTextInputFormula", "FormalTextInputFormulaUneval"]], {file, ct}]}, 
      Spacer[10]], {ct}}
  ]
*)

structView[file_, Cell[ BoxData[content_String]|content_String, style_, ___], tags_, task_] :=
    Switch[ task,
    	"prove",
        Row[{Checkbox[Dynamic[allTrue[tags, kbSelectProve], setAll[tags, kbSelectProve, #] &]], Style[content, style]}, Spacer[10]],
        "compute",
        Row[{Checkbox[Dynamic[allTrue[tags, Theorema`Computation`activeComputationKB], setAll[tags, Theorema`Computation`activeComputationKB, #] &]], Style[content, style]}, Spacer[10]]
    ]

structView[args___] :=
    unexpected[structView, {args}]

kbSelectProve[_] := False

(* ::Subsubsection:: *)
(* updateKBBrowser *)

updateKBBrowser[] :=
    Module[ {file = CurrentValue["NotebookFullFileName"], pos, new},
        pos = Position[ $kbStruct, file -> _];
        new = file -> With[ {nb = NotebookGet[EvaluationNotebook[]]},
                          extractKBStruct[nb] /. l_?VectorQ :> Extract[nb, l]
                      ];
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
            emptyPane[translate["No knowledge available"]],
            TabView[
                  Map[Tooltip[Style[FileBaseName[#[[1]]], "NotebookName"], #[[1]]] -> 
                     Pane[structView[#[[1]], #[[2]], {}, task][[1]],
                      ImageSizeAction -> "Scrollable", Scrollbars -> Automatic] &, 
                   $kbStruct], 
                  Appearance -> {"Limited", 10}, FrameMargins->None]
        ]
    ]
displayKBBrowser[args___] :=
    unexpected[displayKBBrowser, {args}]

(* ::Subsubsection:: *)
(* structViewBuiltin *)
Clear[structViewBuiltin];

structViewBuiltin[{category_String, rest__List}, tags_] :=
    Module[ {sub, compTags},
        sub = Transpose[Map[structViewBuiltin[#, tags] &, {rest}]];
        compTags = Apply[Union, sub[[2]]];
        {OpenerView[{structViewBuiltin[category, compTags], Column[sub[[1]]]}, 
        	ToExpression["Dynamic[$builtinStructState$"<>category<>"]"]], 
         compTags}
    ]

structViewBuiltin[ item:List[__List], tags_] :=
    Module[ {sub, compTags},
        sub = Transpose[Map[structViewBuiltin[#, tags] &, item]];
        compTags = Apply[Union, sub[[2]]];
        {Column[sub[[1]]], compTags}
    ]
    
structViewBuiltin[ {op_String, display_}, tags_] :=
  Module[ { },
    {Row[{Checkbox[Dynamic[Theorema`Computation`activeComputation[op]]], Style[ DisplayForm[display], "FormalTextInputFormula"]}, 
      Spacer[10]], {op}}
  ]

structViewBuiltin[ category_String, tags_] :=
    Module[ {},
        Row[{Checkbox[Dynamic[allTrue[tags, Theorema`Computation`activeComputation], setAll[tags, Theorema`Computation`activeComputation, #] &]], 
          Style[ translate[category], "Section"]}, Spacer[10]]
    ]

structViewBuiltin[args___] :=
    unexpected[structViewBuiltin, {args}]

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

displayBuiltinBrowser[] :=
  Pane[structViewBuiltin[ $tmaBuiltins, {}][[1]],
  	ImageSizeAction -> "Scrollable", Scrollbars -> Automatic]
displayBuiltinBrowser[args___] := unexcpected[ displayBuiltinBrowser, {args}]

printComputationInfo[] :=
  Module[ {act},
      act = Union[ Cases[ DownValues[Theorema`Computation`activeComputation], HoldPattern[s_:>True]:>s[[1,1]]]];
      Print[OpenerView[{"", OpenerView[{Style[translate["Builtins used in computation"], "CILabel"], act}]}, False]];
  ]
printComputationInfo[args___] := unexcpected[ printComputationInfo, {args}]


(* ::Section:: *)
(* Palettes *)

insertNewEnv[type_String] :=
    Module[ {nb = InputNotebook[]},
        NotebookWrite[
         nb, {newOpenEnvCell[ type], 
          newFormulaCell[ type],
          newCloseEnvCell[ type]}];
    ]
insertNewEnv[args___] :=
    unexpected[insertNewEnv, {args}]

openNewEnv[type_String] :=
    Module[ {},
        NotebookWrite[ InputNotebook[], newOpenEnvCell[ type]];
    ]
openNewEnv[args___] :=
    unexpected[openNewEnv, {args}]

insertNewFormulaCell[ style_String] := 
	Module[{}, 
		NotebookWrite[ InputNotebook[], newFormulaCell[ style]]
	]
insertNewFormulaCell[args___] :=
    unexpected[insertNewFormulaCell, {args}]

closeEnv[ type_String] :=
    Module[ {},
        NotebookWrite[ InputNotebook[], newCloseEnvCell[type]];
    ]
closeEnv[args___] :=
    unexpected[closeEnv, {args}]

newFormulaCell[ "COMPUTE"] = Cell[BoxData[""], "Computation"]	
newFormulaCell[ style_, label_:$initLabel] = Cell[BoxData[""], "FormalTextInputFormula", CellTags->label]	
newFormulaCell[args___] :=
    unexpected[newFormulaCell, {args}]

newOpenEnvCell[ "COMPUTE"] := Cell[BoxData["COMPUTE"], "OpenComputation"]
newOpenEnvCell[ type_String] := Cell[BoxData[type], "OpenEnvironment"]
newOpenEnvCell[args___] :=
    unexpected[newOpenEnvCell, {args}]

newCloseEnvCell[ "COMPUTE"] := Cell[BoxData["\[GraySquare]"], "CloseComputation"]
newCloseEnvCell[ _String] := Cell[BoxData["\[GraySquare]"], "CloseEnvironment"]
newCloseEnvCell[args___] :=
    unexpected[newCloseEnvCell, {args}]


(* ::Subsection:: *)
(* Buttons *)

envButtonData["DEFINITION"] := {"tcLangTabEnvTabButtonDefLabel"};
envButtonData["THEOREM"] := {"tcLangTabEnvTabButtonThmLabel"};
envButtonData[args___] :=
    unexpected[envButtonData, {args}]

makeEnvButton[ bname_String] :=
    With[ { bd = envButtonData[bname]},
			Button[Style[ translate[bd[[1]]], "EnvButton"], insertNewEnv[bname], Appearance -> "FramedPalette", Alignment -> {Left, Top}]
    ]
makeEnvButton[args___] :=
    unexpected[makeEnvButton, {args}]

makeFormButton[] :=
    Button[Style[ translate["tcLangTabEnvTabButtonFormLabel"], "EnvButton"], insertNewFormulaCell[ "Env"], 
    	Appearance -> "FramedPalette", Alignment -> {Left, Top}]
makeFormButton[args___] :=
    unexpected[makeFormButton, {args}]
    
allEnvironments = {"DEFINITION", "THEOREM", "LEMMA", "PROPOSITION", "COROLLARY", "CONJECTURE", "ALGORITHM"};
allEnvironments = {"DEFINITION", "THEOREM"};

envButtons[] :=
    Pane[ 
    Column[{
    Grid[ Partition[ Map[ makeEnvButton, allEnvironments], 2]],
    Grid[ {{makeFormButton[]}}]
    }, Center, Dividers->Center]]
envButtons[args___] :=
    unexpected[envButtons, {args}]

$buttonNat = False;

langButtonData["AND1"] := 
	{
		If[ $buttonNat, 
			translate["AND1"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[Wedge]",
				TagBox[ FrameBox["right"], "SelectionPlaceholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]", "\[Wedge]", "\[Placeholder]"}],
		translate["CONN2STRONGTooltip"]
	}

langButtonData["AND2"] := 
	{
		If[ $buttonNat, 
			translate["AND2"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[And]",
				TagBox[ FrameBox["right"], "SelectionPlaceholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]", "\[And]", "\[Placeholder]"}],
		translate["CONN2WEAKTooltip"]
	}

langButtonData["OR1"] := 
	{
		If[ $buttonNat, 
			translate["OR1"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[Vee]",
				TagBox[ FrameBox["right"], "SelectionPlaceholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]", "\[Vee]", "\[Placeholder]"}],
		translate["CONN2STRONGTooltip"]
	}

langButtonData["OR2"] := 
	{
		If[ $buttonNat, 
			translate["OR2"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[Or]",
				TagBox[ FrameBox["right"], "SelectionPlaceholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]", "\[Or]", "\[Placeholder]"}],
		translate["CONN2WEAKTooltip"]
	}

langButtonData["IMPL1"] := 
	{
		If[ $buttonNat, 
			translate["IMPL1"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[DoubleLongRightArrow]",
				TagBox[ FrameBox["right"], "SelectionPlaceholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]",
			TagBox[ "\[DoubleLongRightArrow]", Identity, SyntaxForm->"a\[DoubleRightArrow]b"], "\[Placeholder]"}],
		translate["CONN2STRONGTooltip"]
	}

langButtonData["IMPL2"] := 
	{
		If[ $buttonNat, 
			translate["IMPL2"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[Implies]",
				TagBox[ FrameBox["right"], "SelectionPlaceholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]", "\[Implies]", "\[Placeholder]"}],
		translate["CONN2WEAKTooltip"]
	}

langButtonData["EQUIV1"] := 
	{
		If[ $buttonNat, 
			translate["EQUIV1"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[DoubleLongLeftRightArrow]",
				TagBox[ FrameBox["right"], "SelectionPlaceholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]",
			TagBox[ "\[DoubleLongLeftRightArrow]", Identity, SyntaxForm->"a\[DoubleRightArrow]b"], "\[Placeholder]"}],
		translate["CONN2STRONGTooltip"]
	}

langButtonData["EQUIV2"] := 
	{
		If[ $buttonNat, 
			translate["EQUIV2"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[DoubleLeftRightArrow]",
				TagBox[ FrameBox["right"], "SelectionPlaceholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]",
			TagBox[ "\[DoubleLeftRightArrow]", Identity, SyntaxForm->"a\[Implies]b"], "\[Placeholder]"}],
		translate["CONN2WEAKTooltip"]
	}

langButtonData["EQUIVDEF"] := 
	{
		If[ $buttonNat, 
			translate["EQUIVDEF"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				RowBox[{":", "\[NegativeThickSpace]\[NegativeThinSpace]", "\[DoubleLongLeftRightArrow]"}],
				TagBox[ FrameBox["right"], "SelectionPlaceholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]",
			TagBox[ RowBox[{":", "\[NegativeThickSpace]\[NegativeThinSpace]", "\[DoubleLongLeftRightArrow]"}], Identity, SyntaxForm->"a\[Implies]b"], "\[Placeholder]"}],
		translate["EQUIVDEFTooltip"]
	}

langButtonData["EQDEF"] := 
	{
		If[ $buttonNat, 
			translate["EQDEF"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				":=",
				TagBox[ FrameBox["right"], "SelectionPlaceholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]", ":=", "\[Placeholder]"}],
		translate["EQDEFTooltip"]
	}

langButtonData["FORALL1"] := 
	{
		If[ $buttonNat, 
			translate["FORALL1"], 
			DisplayForm[RowBox[{UnderscriptBox["\[ForAll]", Placeholder["rg"]], TagBox[ FrameBox["expr"], "SelectionPlaceholder"]}]]],
		RowBox[{UnderscriptBox["\[ForAll]", "\[Placeholder]"], "\[SelectionPlaceholder]"}],
		translate["QUANT1Tooltip"]
	}

langButtonData["FORALL2"] := 
	{
		If[ $buttonNat, 
			translate["FORALL2"], 
			DisplayForm[RowBox[{UnderscriptBox[ UnderscriptBox["\[ForAll]", Placeholder["rg"]], Placeholder["cond"]], TagBox[ FrameBox["expr"], "SelectionPlaceholder"]}]]],
		RowBox[{UnderscriptBox[ UnderscriptBox["\[ForAll]", "\[Placeholder]"], "\[Placeholder]"], "\[SelectionPlaceholder]"}],
		translate["QUANT2Tooltip"]
	}

langButtonData["EXISTS1"] := 
	{
		If[ $buttonNat, 
			translate["EXISTS1"], 
			DisplayForm[RowBox[{UnderscriptBox["\[Exists]", Placeholder["rg"]], TagBox[ FrameBox["expr"], "SelectionPlaceholder"]}]]],
		RowBox[{UnderscriptBox["\[Exists]", "\[Placeholder]"], "\[SelectionPlaceholder]"}],
		translate["QUANT1Tooltip"]
	}

langButtonData["EXISTS2"] := 
	{
		If[ $buttonNat, 
			translate["EXISTS2"], 
			DisplayForm[RowBox[{UnderscriptBox[ UnderscriptBox["\[Exists]", Placeholder["rg"]], Placeholder["cond"]], TagBox[ FrameBox["expr"], "SelectionPlaceholder"]}]]],
		RowBox[{UnderscriptBox[ UnderscriptBox["\[Exists]", "\[Placeholder]"], "\[Placeholder]"], "\[SelectionPlaceholder]"}],
		translate["QUANT2Tooltip"]
	}
langButtonData[args___] :=
    unexpected[langButtonData, {args}]

makeLangButton[ bname_String] :=
    With[ { bd = langButtonData[bname]},
			Tooltip[ Button[ Style[ bd[[1]], "LangButton"], 
				FrontEndExecute[{NotebookApply[ InputNotebook[], bd[[2]], Placeholder]}], Appearance -> "FramedPalette", Alignment -> {Left, Top}, ImageSize -> All],
				bd[[3]], TooltipDelay -> 0.5]
    ]
makeLangButton[args___] :=
    unexpected[makeLangButton, {args}]

allFormulae = {"AND1", "AND2", "OR1", "OR2", "IMPL1", "IMPL2", "EQUIV1", "EQUIV2", "EQUIVDEF", "EQDEF", "FORALL1", "FORALL2", "EXISTS1", "EXISTS2"};

langButtons[] := Pane[ 
	Column[{
		Grid[ Partition[ Map[ makeLangButton, allFormulae], 2], Alignment -> {Left, Top}],
		Row[{translate["tcLangTabMathTabBS"], 
			Row[{RadioButton[Dynamic[$buttonNat], False], translate["tcLangTabMathTabBSform"]}, Spacer[2]], 
			Row[{RadioButton[Dynamic[$buttonNat], True], translate["tcLangTabMathTabBSnat"]}, Spacer[2]]}, Spacer[10]]
	}, Dividers -> Center, Spacings -> 4]]
langButtons[args___] :=
    unexpected[langButtons, {args}]
    
envButtonData["COMPUTE"] := {"tcComputeTabSetupTabButtonCompLabel"};
compSetup[] := Pane[ 
	Column[{
		makeEnvButton[ "COMPUTE"]
	}, Dividers -> Center, Spacings -> 4]]
compSetup[args___] :=
    unexpected[compSetup, {args}]


(* ::Section:: *)
(* checkSession *)

checkSession[ test_String] :=
    Module[ {},
        If[ !TrueQ[ToExpression[test]],
            MessageDialog[translate["outsideSession"]];
        ]
    ]
checkSession[args___] :=
    unexpected[checkSession, {args}]



(* ::Section:: *)
(* end of package *)

initGUI[];

End[] (* End Private Context *)

EndPackage[];
