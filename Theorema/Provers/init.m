(* Theorema 
    Copyright (C) 2010 The Theorema Group

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

BeginPackage["Theorema`Provers`", {"Theorema`"}]

Needs["Theorema`Common`"]
Get["Theorema`Provers`Common`"]

Begin["`Private`"]

proofStepText[ "ID" -> id_, step_, lang_, rest___] := 
	Block[ {$proofStepID = id},
		proofStepText[ step, lang, rest]
	]
	
(* Load the language dependent proof texts *)
Map[ Get, FileNames[ "*.m", ToFileName[{$TheoremaDirectory, "Theorema", "Provers", "LanguageData"}], 2]];

proofStepText[ args___] := unexpected[ proofStepText, {args}]


(* ::Section:: *)
(* Proof Cells *)

goalCell[ {k_, g_, t_}, punct_String:""] := 
	Cell[ BoxData[ RowBox[ {ToBoxes[ g, TheoremaForm], punct}]], "Goal", 
		CellFrameLabels->{{None, Cell[ t, "GoalLabel"]}, {None, None}}, 
		CellTags -> {getCellIDLabel[ k], $proofStepID}
	]
goalCell[ args___] := unexpected[ goalCell, {args}]

assumptionCell[ {k_, a_, t_}, punct_String:""] := 
	Cell[ BoxData[ RowBox[ {ToBoxes[ a, TheoremaForm], punct}]], "Assumption", 
		CellFrameLabels->{{None, Cell[ t, "AssumptionLabel"]}, {None, None}}, 
		CellTags -> {getCellIDLabel[ k], $proofStepID}
	]
assumptionCell[ args___] := unexpected[ assumptionCell, {args}]

assumptionListCells[ {f___, l_}, sep_String, punct_String] :=
	Module[{initial, term},
		initial = Map[ assumptionCell[ #, sep]&, {f}];
		term = assumptionCell[ l, punct];
		Cell[ CellGroupData[ Append[ initial, term]]]
	]
assumptionListCells[ args___] := unexpected[ assumptionListCells, {args}]

textCell[ t__] := Cell[ TextData[ Riffle[ {t}, " "]], "Text", CellTags -> {$proofStepID}]
textCell[ args___] := unexpected[ textCell, {args}]

referenceCell[ {k_, form_, label_}] :=
	With[{ tag = getCellIDLabel[k]},
        Cell[ BoxData[ ToBoxes[
            Button[ Tooltip[ Mouseover[ Style[ label, "Reference"], Style[ label, "ReferenceHover"]], theoremaDisplay[ form]],
            	Module[ {cell},
        			NotebookFind[ SelectedNotebook[], tag, Previous, CellTags, AutoScroll -> False];
        			cell = NotebookRead[ SelectedNotebook[]];
                	CreateDialog[{cell, CancelButton["OK", NotebookClose[ButtonNotebook[]]]}]], Appearance->None]
        ]]]
	]
referenceCell[ args___] := unexpected[ referenceCell, {args}]


End[]
EndPackage[]