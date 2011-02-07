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

theoremaCommander::usage = "The Theorema commander"
updateKBBrowser::usage = "";
displayKBBrowser::usage = "";

Needs["Theorema`System`Messages`"];

Begin["`Private`"] (* Begin Private Context *) 


(* ::Section:: *)
(* Region Title *)

theoremaCommander[] :=
    Module[ {style = Replace[ScreenStyleEnvironment,Options[InputNotebook[], ScreenStyleEnvironment]]},
        CreatePalette[Dynamic[displayKBBrowser[],TrackedSymbols->{kbStruct}],
        	StyleDefinitions -> ToFileName[{"Theorema"}, "GUI.nb"],
        	WindowTitle -> "Theorema Commander",
        	ScreenStyleEnvironment -> style,
        	WindowElements -> {"StatusArea"}]
    ]

 
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
      posInp = Position[nb, Cell[_, "FormalTextInputFormula", ___]], inputs, depth, sub, root, heads, isolated},
        heads = Join[posSubsubsec, posSubsec, posSec, posTit];
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
            {Insert[struct, item, {pos, -1}], 
            isolated},
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

structView[file_, {head_Cell, rest__}, tags_] :=
    Module[ {sub, compTags},
        sub = Transpose[Map[structView[file, #, tags] &, {rest}]];
        compTags = Apply[Union, sub[[2]]];
        {OpenerView[{structView[file, head, compTags], Column[sub[[1]]]}], 
         compTags}
    ]

structView[file_, item_List, tags_] :=
    Module[ {sub, compTags},
        sub = Transpose[Map[structView[file, #, tags] &, item]];
        compTags = Apply[Union, sub[[2]]];
        {Column[sub[[1]]], compTags}
    ]

structView[file_, Cell[content_, "FormalTextInputFormula", ___], tags_] :=
    {Row[{Spacer[14], Style["unlabeled formula", "FormalTextInputFormula"]}, Spacer[10]], {}}

structView[file_, Cell[content_, "FormalTextInputFormula", ___, CellTags -> ct_, ___], 
  tags_] :=
    {Row[{Checkbox[Dynamic[isSelected[ct]]], Hyperlink[ Style[ct, "FormalTextInputFormula"], {file, ct}]}, 
      Spacer[10]], {ct}}

structView[file_, Cell[content_, style_, ___], tags_] :=
    Module[ {},
        Row[{Checkbox[Dynamic[allTrue[tags], setAll[tags, #] &]], 
          Style[content, style]}, Spacer[10]]
    ]

structView[args___] :=
    unexpected[structView, {args}]

isSelected[_] := False

allTrue[l_] :=
    Catch[Module[ {},
              Scan[If[ Not[TrueQ[isSelected[#]]],
                       Throw[False]
                   ] &, l];
              True
          ]]

setAll[l_, val_] :=
    Scan[(isSelected[#] = val) &, l]

(* ::Subsubsection:: *)
(* updateKBBrowser *)

updateKBBrowser[] :=
    (kbStruct[CurrentValue["NotebookFullFileName"]] = 
    Module[ {nb = NotebookGet[EvaluationNotebook[]]},
        extractKBStruct[nb] /. l_?VectorQ :> Extract[nb, l]
    ];)
 
(* ::Subsubsection:: *)
(* displayKBBrowser *)
   
displayKBBrowser[] :=
    TabView[
      Map[Tooltip[Style[FileBaseName[#], "NotebookName"], #] -> 
         Pane[structView[#, kbStruct[#], {}][[1]], {600, 200}, 
          ImageSizeAction -> "Scrollable", Scrollbars -> Automatic] &, 
       Map[#[[1, 1, 1]] &, DownValues[kbStruct]]], 
      Appearance -> {"Limited", 10}]


(* ::Section:: *)
(* end of package *)
  
End[] (* End Private Context *)

EndPackage[];