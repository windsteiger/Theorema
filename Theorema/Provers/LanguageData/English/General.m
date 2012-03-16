
With[ {lang = "English"},

proofStepText[ "Initial", lang, goal_, {}, pVal_] := {textCell[ "We have to prove:"], 
         goalCell[ goal],
         textCell[ "with no assumptions."]
         };
proofStepText[ "Initial", lang, goal_, kb_, pVal_] := {textCell[ "We have to prove:"], 
         goalCell[ goal],
         textCell[ "under the assumptions:"], 
         assumptionListCells[ kb, ",", "."]
         };
         
proofStepText[ "ProofSituation", lang, goal_, kb_, ___] := {textCell[ "Open proof situation"], 
		textCell[ "We have to prove:"],
		goalCell[ goal],
    	textCell[ "under the assumptions:"], 
        assumptionListCells[ kb, ",", "."]
		};

proofStepText[ "ProofAlternatives", lang, ___] := {textCell[ "We have several alternatives to continue the proof."]};

subProofHeader[ "ProofAlternatives", lang, ___, {p_}] := {textCell[ ToString[ StringForm[ "Alternative ``:", p]]]};
 

proofStepText[ "SearchDepth", lang, goal_, kb_, ___] := {textCell[ "Search depth exceeded! The open proof situation is:"], 
		textCell[ "We have to prove:"],
		goalCell[ goal],
    	textCell[ "under the assumptions:"], 
        assumptionListCells[ kb, ",", "."]
		};

proofStepText[ "NoPNode", lang, expr_, ___] := {textCell[ "The expression returned by the selected proof strategy is not a valid proof tree node."],
	Cell[ BoxData[ ToBoxes[ expr]], "Print"]};

proofStepText[ "noApplicableRule", lang, ___] := {textCell[ "It seems there is no proof rule to apply."]};

proofStepText[ step_String, lang, ___] := {
	textCell[ ToString[ StringForm[ "We have no explanatory text for step '``'. Please implement the respective case for the function 'proofStepText'.", step]]]
	};

subProofHeader[ step_String, lang, ___] := {
	textCell[ ToString[ StringForm[ "We have no explanatory header text for subproofs of step '``'. Please implement the respective case for the function 'subProofHeader'.", step]]]
	};

] (* With *)

