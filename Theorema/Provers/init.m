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

BeginPackage[ "Theorema`Provers`", {"Theorema`"}]

(*$NewSymbol = If[ #1 === "pVal", Print[$Input, ":", $Line, #2]]&*)

Needs[ "Theorema`Common`"]
Needs[ "Theorema`Language`"]

(* Load the language dependent proof texts and prover descriptions*)
Map[ Get, FileNames[ "*.m", ToFileName[{$TheoremaDirectory, "Theorema", "Provers", "LanguageData"}], 2]];

Get[ "Theorema`Provers`Common`"]

Begin["`Private`"]

proofStepText[ id -> i_, step_, lang_String, rest___] := 
	Block[ {$proofStepID = i},
		proofStepText[ step, lang, rest]
	]
proofStepText[ args___] := unexpected[ proofStepText, {args}]

subProofHeader[ id -> i_, step_, lang_String, rest___, pVal_, pos_List] :=
	Block[ {$proofStepID = i},
		MapAt[ Append[ #, CellDingbat -> ToBoxes[ proofStatusIndicator[ pVal]]]&, 
			subProofHeader[ step, lang, rest, pVal, pos], 1]
	]
subProofHeader[ args___] := unexpected[ subProofHeader, {args}]


(* ::Section:: *)
(* Proof Cells *)

goalCell[ g_FML$, punct_String:""] := 
	Cell[ BoxData[ RowBox[ {ToBoxes[ g.formula, TheoremaForm], punct}]], "Goal", 
		CellFrameLabels->{{None, Cell[ makeLabel[ g.label], "GoalLabel"]}, {None, None}}, 
		CellTags -> {g.id, $proofStepID}
	]
goalCell[ args___] := unexpected[ goalCell, {args}]
 
assumptionCell[ FML$[ k_, a_, t_], punct_String:""] := 
	Cell[ BoxData[ RowBox[ {ToBoxes[ a, TheoremaForm], punct}]], "Assumption", 
		CellFrameLabels->{{None, Cell[ makeLabel[ t], "AssumptionLabel"]}, {None, None}}, 
		CellTags -> {getCellIDLabel[ k], $proofStepID}
	]
assumptionCell[ args___] := unexpected[ assumptionCell, {args}]

assumptionListCells[ {}, sep_String, punct_String] := 
	Cell[ BoxData[ RowBox[ {ToBoxes[{}], punct}]], "Assumption",
		CellTags -> {$proofStepID}
	]
assumptionListCells[ {f___, l_}, sep_String, punct_String] :=
	Module[{initial, term},
		initial = Map[ assumptionCell[ #, sep]&, {f}];
		term = assumptionCell[ l, punct];
		Cell[ CellGroupData[ Append[ initial, term]]]
	]
assumptionListCells[ args___] := unexpected[ assumptionListCells, {args}]

textCell[ t__] := Cell[ TextData[ Riffle[ {t}, " "]], "Text", CellTags -> {$proofStepID}]
textCell[ args___] := unexpected[ textCell, {args}]

End[]

Get[ "Theorema`Provers`Strategies`"]
Get[ "Theorema`Provers`BasicProver`"]

EndPackage[]