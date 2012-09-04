(* ::Section:: *)
(* Public Declaration Part: executes in Theorema`Provers` *)

With[ {lang = "English"},
	
MessageName[ initialProofSituation, "usage", lang] = "The initial proof situation at the beginning of a proof.";
MessageName[ openProofSituation, "usage", lang] = "An open proof situation in a proof.";
MessageName[ proofAlternatives, "usage", lang] = "Alternatives to continue a proof when multiple inference rules apply.";
MessageName[ searchDepthLimit, "usage", lang] = "Proof terminates due to search depth limitation.";
MessageName[ invalidProofNode, "usage", lang] = "A proof strategy returns an invalid proof node.";
MessageName[ noApplicableRule, "usage", lang] = "Proof fails since there is no applicable rule.";
MessageName[ contradictionKB, "usage", lang] = "Knowledge base contains contradicting formulae.";
MessageName[ falseInKB, "usage", lang] = "Knowledge base contains a formula False.";
MessageName[ goalInKB, "usage", lang] = "Knowledge base contains the proof goal.";

] (* With *)

(* ::Section:: *)
(* Private Implementation Part: executes in Theorema`Provers`Private` *)

Begin["`Private`"]

With[ {lang = "English"},

proofStepText[ initialProofSituation, lang, {goal_FML$, {}}, {}, pVal_] := {textCell[ "We have to prove:"], 
         goalCell[ goal],
         textCell[ "with no assumptions."]
         };
proofStepText[ initialProofSituation, lang, {goal_FML$, kb_List}, {}, pVal_] := {textCell[ "We have to prove:"], 
         goalCell[ goal],
         textCell[ "under the assumptions:"], 
         assumptionListCells[ kb, ",", "."]
         };
         
proofStepText[ openProofSituation, lang, {goal_FML$, {}}, {}] := {textCell[ "Open proof situation"], 
		textCell[ "We have to prove:"],
		goalCell[ goal],
    	textCell[ "with no assumptions."]
		};

proofStepText[ openProofSituation, lang, {goal_FML$, kb_List}, {}] := {textCell[ "Open proof situation"], 
		textCell[ "We have to prove:"],
		goalCell[ goal],
    	textCell[ "under the assumptions:"], 
        assumptionListCells[ kb, ",", "."]
		};

proofStepText[ proofAlternatives, lang, ___] := {textCell[ "We have several alternatives to continue the proof."]};

subProofHeader[ proofAlternatives, lang, ___, pVal_, {p_}] := {textCell[ ToString[ StringForm[ "Alternative ``:", p]]]};
 

proofStepText[ searchDepthLimit, lang, {goal_FML$, kb_List}, {}, ___] :=
	Join[{textCell[ "Search depth exceeded! The open proof situation is:"]}, 
		proofStepText[ openProofSituation, lang, {goal, kb}, {}]
	];

proofStepText[ invalidProofNode, lang, expr_, ___] := {textCell[ "The expression returned by the selected proof strategy is not a valid proof tree node."],
	Cell[ BoxData[ ToBoxes[ expr]], "Print"]};

proofStepText[ noApplicableRule, lang, ___] := {textCell[ "There is no proof rule to apply."]};

proofStepText[ contradictionKB, lang, {k_, c_}, {}, pVal_] := {textCell[ "The proof is finished, because ", formulaReference[ k], 
	" contradicts ", formulaReference[ c], "."]
    };

proofStepText[ falseInKB, lang, {k_}, {}, pVal_] := {textCell[ "The proof is finished, because ", formulaReference[ k], 
	" is a contradiction in the knowledge base."]
    };

proofStepText[ goalInKB, lang, {goal_, k_}, {}, pVal_] := {textCell[ "Now we are done, since the goal ", formulaReference[ goal], 
	" is identical to formula ", formulaReference[ k], "in the knowledge base."]
    };

proofStepText[ step_String, lang, ___] := {
	textCell[ ToString[ StringForm[ "We have no explanatory text for step '``'. Please implement the respective case for the function 'proofStepText'.", step]]]
	};

subProofHeader[ step_String, lang, ___] := {
	textCell[ ToString[ StringForm[ "We have no explanatory header text for subproofs of step '``'. Please implement the respective case for the function 'subProofHeader'.", step]]]
	};

] (* With *)

End[]
