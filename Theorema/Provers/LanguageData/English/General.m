(* ::Section:: *)
(* Public Declaration Part: executes in Theorema`Provers` *)

With[ {lang = "English"},
	
MessageName[ initialProofSituation, "usage", lang] = "The initial proof situation at the beginning of a proof";
MessageName[ openProofSituation, "usage", lang] = "An open proof situation in a proof";
MessageName[ proofAlternatives, "usage", lang] = "Alternatives to continue a proof when multiple inference rules apply";
MessageName[ searchDepthLimit, "usage", lang] = "Proof terminates due to search depth limitation";
MessageName[ invalidProofNode, "usage", lang] = "A proof strategy returns an invalid proof node";
MessageName[ noApplicableRule, "usage", lang] = "Proof fails since there is no applicable rule";
MessageName[ levelSat, "usage", lang] = "Level saturation";

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

(* The data for openProofSituation comes from a PRFSIT$, which has no proofValue yet. Hence, we cannot pass a pVal as last parameter,
   like we do it in all other proofStepText cases. This is no problem, since we don't need a pVal here anyway. *)         
proofStepText[ openProofSituation, lang, {{goal_FML$}}, {}] := {textCell[ "Open proof situation"], 
		textCell[ "We have to prove:"],
		goalCell[ goal],
    	textCell[ "with no assumptions."]
		};

proofStepText[ openProofSituation, lang, {{goal_FML$, kb__FML$}}, {}] := {textCell[ "Open proof situation"], 
		textCell[ "We have to prove:"],
		goalCell[ goal],
    	textCell[ "under the assumptions:"], 
        assumptionListCells[ {kb}, ",", "."]
		};

proofStepText[ proofAlternatives, lang, ___] := {textCell[ "We have several alternatives to continue the proof."]};

subProofHeader[ proofAlternatives, lang, ___, pVal_, {p_}] := {textCell[ ToString[ StringForm[ "Alternative ``:", p]]]};

proofStepText[ levelSat, lang, u_List, g_List, pVal_] := Module[{i, cells = {textCell[ "From what we already know, we can derive new knowledge."]}},
	Do[
		cells = Join[ cells, {textCell[ "From ", formulaReferenceSequence[ u[[i]], lang], " we infer"], assumptionListCells[ g[[i]], ",", "."]}],
		{i, Length[ u]}
	];
	cells
];

proofStepText[ searchDepthLimit, lang, {{goal_FML$, kb___FML$}}, {}, ___] :=
	Join[{textCell[ "Search depth exceeded! The open proof situation is:"]}, 
		proofStepText[ openProofSituation, lang, {{goal, kb}}, {}]
	];

proofStepText[ invalidProofNode, lang, expr_, ___] := {textCell[ "The expression returned by the selected proof strategy is not a valid proof tree node."],
	Cell[ BoxData[ ToBoxes[ expr]], "Print"]};

proofStepText[ noApplicableRule, lang, {{goal_FML$, kb___FML$}}, {}, ___, "openPS" -> ps_, ___] := 
	{Cell[ CellGroupData[
		Join[{textCell[ "There is no proof rule to apply. The open proof situation is:"]},
			proofStepText[ openProofSituation, lang, {{goal, kb}}, {}],
			{Cell[ CellGroupData[ {Cell[ "The proof situation data (for debugging)", "Text"],
			 Cell[ BoxData[ ToBoxes[ ps]], "Input"]}, Closed]]}
		]
	]]};

proofStepText[ step_Symbol, lang, ___] := {
	textCell[ ToString[ StringForm[ "We have no explanatory text for step '``'. Please implement the respective case for the function 'proofStepText'.", step]]]
	};

subProofHeader[ step_Symbol, lang, ___] := {
	textCell[ ToString[ StringForm[ "We have no explanatory header text for subproofs of step '``'. Please implement the respective case for the function 'subProofHeader'.", step]]]
	};

] (* With *)

End[]
