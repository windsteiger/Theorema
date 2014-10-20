(* Theorema 
    Copyright (C) 1995-2010 The Theorema Group

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

(*
   *********************************************************************************************
   -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- 
   *********************************************************************************************
 
     If you modify this file, then insert the new translation in correct alphabetical 
     order (case-insensitive).

     ALSO, YOU MUST add a corresponding entry in the respective file for each other language, 
     either
      1) in the respective section named "UNTRANSLATED", note there are several such sections
         in the file (in case you cannot or do not want to provide a translation) or
      2) in correct alphabetical order (case-insensitive) in case you immediately provide 
         a translation.
      
   *********************************************************************************************
   -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- 
   *********************************************************************************************
 *)
 
(* ::Section:: *)
(* Public Declaration Part: executes in Theorema`Provers` *)

With[ {lang = "English"},
	
	MessageName[ initialProofSituation, "usage", lang] = "The initial proof situation at the beginning of a proof";
	MessageName[ invalidProofNode, "usage", lang] = "A proof strategy returns an invalid proof node";

	MessageName[ levelSat, "usage", lang] = "Level saturation";

	MessageName[ noApplicableRule, "usage", lang] = "Proof fails since there is no applicable rule";

	MessageName[ openProofSituation, "usage", lang] = "An open proof situation in a proof";

	MessageName[ proofAlternatives, "usage", lang] = "Alternatives to continue a proof when multiple inference rules apply";

	MessageName[ searchDepthLimit, "usage", lang] = "Proof terminates due to search depth limitation";

] (* With *)

(* ::Section:: *)
(* Private Implementation Part: executes in Theorema`Provers`Private` *)

Begin["`Private`"]

With[ {lang = "English"},

inlineTheoremaExpressionSeq[ {f_}, lang] := inlineTheoremaExpression[f];
inlineTheoremaExpressionSeq[ {f_, g_}, lang] := {inlineTheoremaExpression[f], " and ", inlineTheoremaExpression[g]};
inlineTheoremaExpressionSeq[ {f_, m__, g_}, lang] := Join[ {inlineTheoremaExpression[f]}, 
	Riffle[ Map[ inlineTheoremaExpression, {m}], ", ", {1, -1, 2}],
	{"and ", inlineTheoremaExpression[g]}];
inlineTheoremaExpressionSeq[ args___] := unexpected[ inlineTheoremaExpressionSeq, {args}];

formulaReferenceSequence[ {f_}, lang] := formulaReference[f];
formulaReferenceSequence[ {f_, g_}, lang] := {formulaReference[f], " and ", formulaReference[g]};
formulaReferenceSequence[ {f_, m__, g_}, lang] := Join[ {formulaReference[f]}, 
	Riffle[ Map[ formulaReference, {m}], ", ", {1, -1, 2}],
	{"and ", formulaReference[g]}];
formulaReferenceSequence[ args___] := unexpected[ formulaReferenceSequence, {args}];



proofStepText[ initialProofSituation, lang, {}, {{goal_FML$}}, pVal_] := {If[ pVal === proved, textCell[ "We prove:"], textCell[ "We have to prove:"]], 
         goalCell[ goal],
         textCell[ "with no assumptions."]
         };
proofStepText[ initialProofSituation, lang, {}, {{goal_FML$, kb__FML$}}, pVal_] := {If[ pVal === proved, textCell[ "We prove:"], textCell[ "We have to prove:"]], 
         goalCell[ goal],
         textCell[ "under the assumptions:"], 
         assumptionListCells[ {kb}, ",", "."]
         };

proofStepText[ invalidProofNode, lang, expr_, ___] := {textCell[ "The expression returned by the selected proof strategy is not a valid proof tree node."],
	Cell[ BoxData[ ToBoxes[ expr]], "Print"]};


proofStepText[ levelSat, lang, u_List, g_List, pVal_] := Module[{i, cells = {textCell[ "From what we already know, we can derive new knowledge."]}},
	Do[
		cells = Join[ cells, {textCell[ "From ", formulaReferenceSequence[ u[[i]], lang], " we infer"], assumptionListCells[ g[[i]], ",", "."]}],
		{i, Length[ u]}
	];
	cells
];

proofStepText[ noApplicableRule, lang, ps_, {}, pVal_] := 
	{Cell[ CellGroupData[
		Join[{textCell[ "There is no proof rule to apply. The open proof situation is:"]},
			proofStepText[ openProofSituation, lang, ps, {}]
		]
	]]};


(* The data for openProofSituation comes from a PRFSIT$, which has no proofValue yet. Hence, we cannot pass a pVal as last parameter,
   like we do it in all other proofStepText cases. This is no problem, since we don't need a pVal here anyway.
   
   The proof situation data comes in a list, because putting a PRFSIT$[...] into the proof object would confuse the proof search,
   it would be found as a possible position to continue the proof. *)         
proofStepText[ openProofSituation, lang, {ps:{goal_FML$, {}, ___}}, {}] := {textCell[ "Open proof situation"], 
		textCell[ "We have to prove:"],
		goalCell[ goal],
    	textCell[ "with no assumptions."],
    	Cell[ CellGroupData[ {Cell[ "The proof situation data (for debugging)", "Text"],
			 Cell[ BoxData[ ToBoxes[ ps]], "Input"]}, Closed]]
		};

proofStepText[ openProofSituation, lang, {ps:{goal_FML$, kb_, ___}}, {}] := {textCell[ "Open proof situation"], 
		textCell[ "We have to prove:"],
		goalCell[ goal],
    	textCell[ "under the assumptions:"], 
        assumptionListCells[ kb, ",", "."],
        Cell[ CellGroupData[ {Cell[ "The proof situation data (for debugging)", "Text"],
			 Cell[ BoxData[ ToBoxes[ ps]], "Input"]}, Closed]]
		};

proofStepText[ proofAlternatives, lang, ___] := {textCell[ "We have several alternatives to continue the proof."]};

subProofHeader[ proofAlternatives, lang, ___, pVal_, {p_}] := {textCell[ ToString[ StringForm[ "Alternative ``:", p]]]};

proofStepText[ searchDepthLimit, lang, ps_, {}, ___] :=
	Join[{textCell[ "Search depth exceeded! The open proof situation is:"]}, 
		proofStepText[ openProofSituation, lang, ps, {}]
	];

proofStepText[ step_Symbol, lang, r___] := {
	textCell[ ToString[ StringForm[ "We have no explanatory text for step '``'. Please implement the respective case for the function 'proofStepText'. Parameters: ``", step, {r}]]]
	};

subProofHeader[ step_Symbol, lang, r___] := {
	textCell[ ToString[ StringForm[ "We have no explanatory header text for subproofs of step '``'. Please implement the respective case for the function 'subProofHeader'. Parameters: ``", step, {r}]]]
	};

] (* With *)

End[]
