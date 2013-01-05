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

(* Load the language dependent proof texts and prover descriptions *)
Map[ Get, FileNames[ "*.m", FileNameJoin[{$TheoremaDirectory, "Theorema", "Provers", "LanguageData"}], 2]];

Get[ "Theorema`Provers`Common`"]

Begin["`Private`"]

(*
	The default cases to be added after all proof texts have been loaded above.
	
	The standard call is:
	proofStepText[ step, language, used_List, generated_List, addInfo___?OptionQ, pVal_Symbol], where
		addInfo is a sequence of options of the form _String->val_
		pVal is the proof node's value, i.e. the last argument is always the proof value.
*)
proofStepText[ args___] := unexpected[ proofStepText, {args}]
subProofHeader[ args___] := unexpected[ subProofHeader, {args}]

proofStepTextId[ id_, step_, rest___] := 
	Block[ {$proofStepID = id},
		proofStepText[ step, $Language, rest]
	]
proofStepTextId[ args___] := unexpected[ proofStepTextId, {args}]

subProofHeaderId[ id_, step_, rest___, pVal_, pos_List] :=
	Block[ {$proofStepID = id},
		MapAt[ Append[ #, CellDingbat -> ToBoxes[ proofStatusIndicator[ pVal]]]&, 
			subProofHeader[ step, $Language, rest, pVal, pos], 1]
	]
subProofHeaderId[ args___] := unexpected[ subProofHeaderId, {args}]


(* ::Section:: *)
(* Proof Cells *)

formulaBox[ f_FML$] :=
    Module[ {orig = f."origForm"},
        If[ orig === {},
            ToBoxes[ f.formula, TheoremaForm],
            (* else *)
            TooltipBox[ ToBoxes[ f.formula, TheoremaForm], ToBoxes[ orig, TheoremaForm]]
    	]
    ]
formulaBox[ args___] := unexpected[ formulaBox, {args}]

goalCell[ g_FML$, punct_String:""] :=
    With[ {pid = $proofStepID, formBox = formulaBox[ g]},
        Cell[ BoxData[ RowBox[ {formBox, punct}]], "Goal", 
            CellFrameLabels->{{None, Cell[ makeLabel[ g.label], "GoalLabel"]}, {None, None}}, 
            CellTags -> {g.id, pid},
            CellEventActions -> {"MouseClicked" :> ($selectedProofStep = pid), PassEventsDown -> True}
        ]
    ]

goalCell[ args___] := unexpected[ goalCell, {args}]
 
assumptionCell[ a_FML$, punct_String:""] := 
	With[ {pid = $proofStepID, formBox = formulaBox[ a]}, 
		Cell[ BoxData[ RowBox[ {formBox, punct}]], "Assumption", 
			CellFrameLabels->{{None, Cell[ makeLabel[ a.label], "AssumptionLabel"]}, {None, None}}, 
			CellTags -> {a.id, pid},
			CellEventActions -> {"MouseClicked" :> ($selectedProofStep = pid), PassEventsDown -> True}
		]
	]
assumptionCell[ args___] := unexpected[ assumptionCell, {args}]

assumptionListCells[ {f___, l_}, sep_String, punct_String] :=
	Module[{initial, term},
		initial = Map[ assumptionCell[ #, sep]&, {f}];
		term = assumptionCell[ l, punct];
		Cell[ CellGroupData[ Append[ initial, term]]]
	]
assumptionListCells[ args___] := unexpected[ assumptionListCells, {args}]

textCell[ t__] := 
		With[ {pid = $proofStepID}, 
			Cell[ TextData[ {t}], "Text", CellTags -> {pid},
				CellEventActions -> {"MouseClicked" :> ($selectedProofStep = pid), PassEventsDown -> True}
			]
		]
textCell[ args___] := unexpected[ textCell, {args}]

(*
	Inline Theorema formulae inside a textCell
*)
inlineTheoremaExpression[ expr_] := Cell[ ToBoxes[ expr, TheoremaForm]]
inlineTheoremaExpression[ args___] := unexpected[ inlineTheoremaExpression, {args}]

End[]

Get[ "Theorema`Provers`Strategies`"]
Get[ "Theorema`Provers`BasicTheoremaLanguage`"]

EndPackage[]