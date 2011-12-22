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
		$cellTagKeySeparator = "_";
		If[ ValueQ[$theoremaGUI], tc = "Theorema Commander" /. $theoremaGUI];
		If[ $Notebooks && MemberQ[Notebooks[], tc], NotebookClose[tc]];
		$theoremaGUI = {"Theorema Commander" -> theoremaCommander[]};
		kbSelectProve[_] := False
	]

(* ::Section:: *)
(* theoremaCommander *)

theoremaCommander[] /; $Notebooks :=
    Module[ {style = Replace[ScreenStyleEnvironment,Options[InputNotebook[], ScreenStyleEnvironment]]},
        CreatePalette[ Dynamic[Refresh[
        	TabView[{
        		translate["tcLangTabLabel"]->TabView[{
        			translate["tcLangTabMathTabLabel"]->Dynamic[Refresh[ langButtons[], TrackedSymbols :> {$buttonNat}]],
        			translate["tcLangTabEnvTabLabel"]->envButtons[],
        			translate["tcLangTabArchTabLabel"]->archButtons[]}, Dynamic[$tcLangTab],
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
        		translate["tcPreferencesTabLabel"]->TabView[{
        			translate["tcPrefLanguage"]->PopupMenu[Dynamic[$Language], availableLanguages[]],
        			translate["tcPrefArchiveDir"]->Row[{Dynamic[Tooltip[ToFileName[Take[FileNameSplit[$TheoremaArchiveDirectory], -2]], $TheoremaArchiveDirectory]],
        				FileNameSetter[Dynamic[$TheoremaArchiveDirectory], "Directory"]}, Spacer[10]]}
        			]},
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
extract hierarchically structured knowledge from a notebook
*)

extractKBStruct[nb_NotebookObject] := extractKBStruct[ NotebookGet[nb]];

extractKBStruct[nb_Notebook] :=
    Module[ {posTit = Cases[Position[nb, Cell[_, "Title", ___]], {a___, 1}],
      posSec =  Cases[Position[nb, Cell[_, "Section", ___]], {a___, 1}], 
      posSubsec = Cases[Position[nb, Cell[_, "Subsection", ___]], {a___, 1}], 
      posSubsubsec = Cases[Position[nb, Cell[_, "Subsubsection", ___]], {a___, 1}], 
      posSubsubsubsec = Cases[Position[nb, Cell[_, "Subsubsubsection", ___]], {a___, 1}], 
      posEnv = Cases[Position[nb, Cell[_, "OpenEnvironment", ___]], {a___, 1}], 
      posInp = Position[nb, Cell[_, "FormalTextInputFormula", ___]], inputs, depth, sub, root, heads, isolated},
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

extractKBStruct[args___] :=
    unexpected[extractKBStruct, {args}]


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
Clear[structView];

(* produce a list containing the structured view corresponding to notebook file and a list of all cell tags contained
   recursively process the nested list structure generated by extractKBStruct 
   parameter 'task' decides whether the view is generated for the prove tab or the compute tab *)
   
(* group with header and content *)   
structView[file_, {head:Cell[sec_, "Title"|"Section"|"Subsection"|"Subsubsection"|"Subsubsubsection"|"OpenEnvironment", opts___], rest__}, tags_, task_] :=
    Module[ {sub, compTags},
    	(* process content componentwise
    	   during recursion, we collect all cell tags from cells contained in that group 
    	   Transpose -> pos 1 contains the list of subviews
    	   pos 2 contains the list of tags in subgroups *)
        sub = Transpose[Map[structView[file, #, tags, task] &, {rest}]];
        compTags = Apply[Union, sub[[2]]];
        (* generate an opener view with the view of the header and the content as a column
           a global symbol with unique name is generated, whose value stores the state of the opener *)
        (* TODO: Use TaggingRules to store the state -> Tutorial "Storing and Tracking Palette States" *)
        {OpenerView[{headerView[file, head, compTags, task], Column[sub[[1]]]}, 
        	ToExpression[StringReplace["Dynamic[NEWSYM]", 
        		"NEWSYM" -> "$kbStructState$"<>ToString[Hash[FileBaseName[file]]]<>"$"<>ToString[CellID/.{opts}]]]], 
         compTags}
    ]
    
(* group with header and no content -> ignore *)   
structView[file_, {Cell[sec_, "Title"|"Section"|"Subsection"|"Subsubsection"|"Subsubsubsection"|"OpenEnvironment", ___]}, tags_, task_] :=
	Sequence[]

(* list processed componentwise *) 
structView[file_, item_List, tags_, task_] :=
    Module[ {sub, compTags},
     	(* process content componentwise
    	   during recursion, we collect all cell tags from cells contained in that group 
    	   Transpose -> pos 1 contains the list of subviews
    	   pos 2 contains the list of tags in subgroups *)
        sub = Transpose[Map[structView[file, #, tags, task] &, item]];
        compTags = Apply[Union, sub[[2]]];
        (* generate a column and return the collected tags also *)
        {Column[sub[[1]]], compTags}
    ]

(* input cell with cell tags *)
structView[file_, Cell[content_, "FormalTextInputFormula", a___, CellTags -> cellTags_, b___], 
  tags_, task_] :=
    Module[ { isEval, cleanCellTags, keyTags, formulaLabel, idLabel, nbAvail},
        cleanCellTags = getCleanCellTags[ cellTags];
        (* keyTags are those cell tags that are used to uniquely identify the formula in the KB *)
        keyTags = getKeyTags[ cellTags];
        (* check whether cell has been evaluated -> formula is in KB? *)
        isEval = MemberQ[ $tmaEnv, {keyTags, _}];
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
        nbAvail = FileExistsQ[file] && FileExtension[file]==="nb";
        (* generate a checkbox and display the label
           checkbox sets the value of the global function kbSelectProve[labels] (activeComputationKB[labels] resp. for the compute tab),
           enabled only if the formula has been evaluated 
           label is a hyperlink to the notebook or a button that opens a new window displaying the formula *)
        {Switch[ task,
            "prove",
            Row[{Checkbox[Dynamic[kbSelectProve["KEY"]], Enabled->isEval] /. "KEY" -> keyTags, 
                If[ nbAvail,
                    Hyperlink[ Style[formulaLabel, If[ isEval,
                                                       "FormalTextInputFormula",
                                                       "FormalTextInputFormulaUneval"
                                                   ]], {file, idLabel}],
                    Button[ Style[formulaLabel, "FormalTextInputFormula"], 
                        CreateDialog[{Cell[ content, "Output"], CancelButton["OK", NotebookClose[ButtonNotebook[]]]}],
                        Appearance->None]
                ]},
                Spacer[10]],
            "compute",
            Row[{Checkbox[Dynamic[Theorema`Computation`activeComputationKB["KEY"]], Enabled->isEval] /. "KEY" -> keyTags,
                If[ nbAvail,
                    Hyperlink[ Style[formulaLabel, If[ isEval,
                                                       "FormalTextInputFormula",
                                                       "FormalTextInputFormulaUneval"
                                                   ]], {file, idLabel}],
                    Button[ Style[formulaLabel, "FormalTextInputFormula"],
                        CreateDialog[{Cell[ content, "Output"], CancelButton["OK", NotebookClose[ButtonNotebook[]]]}],
                        Appearance->None]
                ]},
                Spacer[10]]
            ], {keyTags}}
    ]

(* input cell without cell tags -> ignore *)
structView[file_, Cell[content_, "FormalTextInputFormula", ___], tags_, task_] :=
    Sequence[]

structView[args___] :=
    unexpected[structView, {args}]

(* header view *)
headerView[file_, Cell[ content_String, style_, ___], tags_, task_] :=
(* tags contains all tags contained in the group
   generate a checkbox for the whole group and the header from the cell
   checkbox does not have an associated variable whose value the box represents
   instead, the checkbox is checked if all tags containd in the group are checked,
   checking the box calls function setAll in order to set/unset all tags contained in the group *)
    Switch[ task,
    	"prove",
        Row[{Checkbox[Dynamic[allTrue[tags, kbSelectProve], setAll[tags, kbSelectProve, #] &]], Style[ content, style]}, Spacer[10]],
        "compute",
        Row[{Checkbox[Dynamic[allTrue[tags, Theorema`Computation`activeComputationKB], setAll[tags, Theorema`Computation`activeComputationKB, #] &]], Style[ content, style]}, Spacer[10]]
    ]
headerView[args___] :=
    unexpected[headerView, {args}]


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
        new = file -> With[ {nb = NotebookGet[EvaluationNotebook[]]},
                          extractKBStruct[nb] /. l_?VectorQ :> Extract[nb, l]
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
            emptyPane[translate["No knowledge available"]],
            (* generate tabs for each notebook,
               tab label contains a short form of the filename, tab contains a Pane containing the structured view *)
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

(* structured view for builtin operators
   follows the ideas of the structured view of the KB *)
   
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

displayBuiltinBrowser[] :=
  Pane[structViewBuiltin[ $tmaBuiltins, {}][[1]],
  	ImageSizeAction -> "Scrollable", Scrollbars -> Automatic]
displayBuiltinBrowser[args___] := unexcpected[ displayBuiltinBrowser, {args}]

(* ::Subsubsection:: *)
(* printComputationInfo *)

(* this function is called during a computation (see processComputation[])
   effect: print a cell containg information about the environment settings for that computation *)
printComputationInfo[] :=
    Module[ {act},
        act = Union[ Cases[ DownValues[Theorema`Computation`activeComputation], HoldPattern[s_:>True]:>s[[1,1]]]];
        CellPrint[Cell[ToBoxes[OpenerView[{"", OpenerView[{Style[translate["Builtins used in computation"], "CILabel"], act}]}, False]], "ComputationInfo"]];
    ]
printComputationInfo[args___] := unexcpected[ printComputationInfo, {args}]


(* ::Section:: *)
(* Palettes *)

insertNewEnv[type_String] :=
    Module[ {nb = InputNotebook[]},
        NotebookWrite[
         nb, {newOpenEnvCell[ type], 
          newFormulaCell[ type],
          newEndEnvCell[],
          newCloseEnvCell[]}];
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
newFormulaCell[ style_, label_:$initLabel] = Cell[BoxData["\[SelectionPlaceholder]"], "FormalTextInputFormula", CellTags->{label}]	
newFormulaCell[args___] :=
    unexpected[newFormulaCell, {args}]

newOpenEnvCell[ type_String] := Cell[ type, "OpenEnvironment"]
newOpenEnvCell[args___] :=
    unexpected[newOpenEnvCell, {args}]

newEndEnvCell[] := Cell[ "\[GraySquare]", "EndEnvironmentMarker"]
newEndEnvCell[args___] :=
    unexpected[newEndEnvCell, {args}]

newCloseEnvCell[] := Cell[ "", "CloseEnvironment"]
newCloseEnvCell[args___] :=
    unexpected[newCloseEnvCell, {args}]


(* ::Subsection:: *)
(* Buttons *)

envButtonData["DEF"] := "tcLangTabEnvTabButtonDefLabel";
envButtonData["THM"] := "tcLangTabEnvTabButtonThmLabel";
envButtonData["LMA"] := "tcLangTabEnvTabButtonLmaLabel";
envButtonData["PRP"] := "tcLangTabEnvTabButtonPrpLabel";
envButtonData["COR"] := "tcLangTabEnvTabButtonCorLabel";
envButtonData["CNJ"] := "tcLangTabEnvTabButtonCnjLabel";
envButtonData["ALG"] := "tcLangTabEnvTabButtonAlgLabel";
envButtonData["EXM"] := "tcLangTabEnvTabButtonExmLabel";
envButtonData[args___] :=
    unexpected[envButtonData, {args}]

makeEnvButton[ bname_String] :=
    With[ { bd = envButtonData[bname]},
			Button[Style[ translate[bd], "EnvButton"], insertNewEnv[ translate[bd]], Alignment -> {Left, Top}]
    ]
makeEnvButton[args___] :=
    unexpected[makeEnvButton, {args}]

makeFormButton[] :=
    Button[Style[ translate["tcLangTabEnvTabButtonFormLabel"], "EnvButton"], insertNewFormulaCell[ "Env"], Alignment -> {Left, Top}]
makeFormButton[args___] :=
    unexpected[makeFormButton, {args}]
    
allEnvironments = {"DEF", "THM", "LMA", "PRP", "COR", "CNJ", "ALG", "EXM"};

envButtons[] :=
    Pane[ 
    Column[{
    Grid[ Partition[ Map[ makeEnvButton, allEnvironments], 2]],
    Grid[ {{makeFormButton[]}}]
    }, Center, Dividers->Center]]
envButtons[args___] :=
    unexpected[envButtons, {args}]

(* ::Section:: *)
(* Archives Tab *)

archButtons[] :=
    Module[ {},
        Pane[
        	Column[{
        		OpenerView[{Style[translate["tcLangTabArchTabSectionCreate"],"Section"], Column[{
        		makeArchNewButton[],
        		makeArchInfoButton[],
        		makeArchCloseButton[]}]}],
        		OpenerView[{Style[translate["tcLangTabArchTabSectionLoad"],"Section"], Column[{
        		makeArchLoadButton[]}]}]}
        	]
        ]
    ]
archButtons[args___] := unexpected[archButtons, {args}]

makeArchNewButton[] :=
	Button[Style[ translate["tcLangTabArchTabButtonArchLabel"], "EnvButton"], insertNewArchive[], Alignment -> {Left, Top}]
makeArchNewButton[args___] := unexpected[makeArchNewButton, {args}]

makeArchInfoButton[] :=
	Button[Style[ translate["tcLangTabArchTabButtonInfoLabel"], "EnvButton"], insertArchiveInfo[], Alignment -> {Left, Top}]
makeArchInfoButton[args___] := unexpected[makeArchInfoButton, {args}]

makeArchCloseButton[] :=
	Button[Style[ translate["tcLangTabArchTabButtonCloseLabel"], "EnvButton"], insertCloseArchive[], Alignment -> {Left, Top}]
makeArchCloseButton[args___] := unexpected[makeArchCloseButton, {args}]

insertNewArchive[] :=
	Module[{nb = InputNotebook[]},
		NotebookWrite[nb, archiveOpenCell[]];
		insertArchiveInfo[];
		If[ NotebookFind[nb, "CloseArchive", All, CellStyle] === $Failed,
			SelectionMove[nb, After, Notebook];
			insertCloseArchive[];
			NotebookFind[nb, "OpenArchive", All, CellStyle]
		]
	]
insertNewArchive[args___] := unexpected[insertNewArchive, {args}]

insertArchiveInfo[] := NotebookWrite[ InputNotebook[], archiveInfoCells[]]
insertArchiveInfo[args___] := unexpected[insertArchiveInfo, {args}]

insertCloseArchive[] := NotebookWrite[ InputNotebook[], archiveCloseCells[]]
insertCloseArchive[args___] := unexpected[insertCloseArchive, {args}]

archiveOpenCell[] := Cell["ArchiveName`", "OpenArchive"]
archiveOpenCell[args___] := unexpected[archiveOpenCell, {args}]

archiveInfoCells[] := {
	Cell[ BoxData[RowBox[{"{","}"}]], "ArchiveInfo", CellFrameLabels->{{translate["archLabelNeeds"], None}, {None, None}}],
	Cell[ BoxData[RowBox[{"{","}"}]], "ArchiveInfo", CellFrameLabels->{{translate["archLabelPublic"], None}, {None, None}}]}
archiveInfoCells[args___] := unexpected[archiveInfoCells, {args}]

archiveCloseCells[] := Cell["\[FilledUpTriangle]", "CloseArchive"]
archiveCloseCells[args___] := unexpected[archiveCloseCells, {args}]

makeArchLoadButton[] :=
    DynamicModule[ {arch = $TheoremaArchiveDirectory},
        Column[{
            Dynamic[showSelectedArchives[arch]], 
            Row[{FileNameSetter[Dynamic[arch], "OpenList", {translate["fileTypeArchive"]->{"*.ta"}}, Appearance -> translate["tcLangTabArchTabButtonSelectLabel"]],
            Button[Style[ translate["tcLangTabArchTabButtonLoadLabel"], "EnvButton"], (loadArchive[arch];arch=$TheoremaArchiveDirectory;), Alignment -> {Left, Top}]}]}]
    ]
makeArchLoadButton[args___] := unexpected[makeArchLoadButton, {args}]

showSelectedArchives[ l_List] :=
    Pane[ Column[ Map[ archiveName, l]], ImageSize->{200,20*Length[l]}, ImageSizeAction->"Scrollable"]
showSelectedArchives[ s_String] :=
    translate["tcLangTabArchTabNoArchSel"]
showSelectedArchives[args___] := unexpected[showSelectedArchives, {args}]

(* ::Section:: *)
(* Math Tab *)

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

langButtonData["EQ1"] := 
	{
		If[ $buttonNat, 
			translate["EQ1"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"\[Equal]",
				TagBox[ FrameBox["right"], "SelectionPlaceholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]", "\[Equal]", "\[Placeholder]"}],
		translate["CONN2Tooltip"]
	}

langButtonData["EQ2"] := 
	{
		If[ $buttonNat, 
			translate["EQ2"], 
			DisplayForm[RowBox[{TagBox[ FrameBox["left"], "SelectionPlaceholder"],
				"=",
				TagBox[ FrameBox["right"], "SelectionPlaceholder"]}]]],
		RowBox[{"\[SelectionPlaceholder]",
			TagBox[ "=", Identity, SyntaxForm->"a\[Equal]b"], "\[Placeholder]"}],
		translate["CONN2Tooltip"]
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
				FrontEndExecute[{NotebookApply[ InputNotebook[], bd[[2]], Placeholder]}], Appearance -> "DialogBox", Alignment -> {Left, Top}, ImageSize -> All],
				bd[[3]], TooltipDelay -> 0.5]
    ]
makeLangButton[args___] :=
    unexpected[makeLangButton, {args}]

allFormulae = {"AND1", "AND2", "OR1", "OR2", "IMPL1", "IMPL2", "EQUIV1", "EQUIV2", "EQ1", "EQ2", "EQUIVDEF", "EQDEF", "FORALL1", "FORALL2", "EXISTS1", "EXISTS2"};

langButtons[] := Pane[ 
	Column[{
		Grid[ Partition[ Map[ makeLangButton, allFormulae], 2], Alignment -> {Left, Top}],
		Row[{translate["tcLangTabMathTabBS"], 
			Row[{RadioButton[Dynamic[$buttonNat], False], translate["tcLangTabMathTabBSform"]}, Spacer[2]], 
			Row[{RadioButton[Dynamic[$buttonNat], True], translate["tcLangTabMathTabBSnat"]}, Spacer[2]]}, Spacer[10]]
	}, Dividers -> Center, Spacings -> 4]]
langButtons[args___] :=
    unexpected[langButtons, {args}]
    
compSetup[] := Pane[ 
	Column[{
		makeCompButton[]
	}, Dividers -> Center, Spacings -> 4]]
compSetup[args___] :=
    unexpected[compSetup, {args}]

makeCompButton[] :=
    Button[Style[ translate["tcComputeTabSetupTabButtonCompLabel"], "EnvButton"], insertNewFormulaCell[ "COMPUTE"], Alignment -> {Left, Top}]
makeCompButton[args___] :=
    unexpected[makeCompButton, {args}]


(* ::Section:: *)
(* end of package *)

initGUI[];

End[]; (* End Private Context *)

EndPackage[];
