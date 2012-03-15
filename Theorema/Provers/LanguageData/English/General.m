
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

proofStepText[ "ProofAlternatives", lang, goal_, kb_, ___] := {textCell[ "We have several alternatives to continue the proof."]};

subProofHeader[ "ProofAlternatives", lang, {p_}] := {textCell[ ToString[ StringForm[ "Alternative ``:", p]]]};
 

proofStepText[ "SearchDepth", lang, goal_, kb_, ___] := {textCell[ "Search depth exceeded! The open proof situation is:"], 
		textCell[ "We have to prove:"],
		goalCell[ goal],
    	textCell[ "under the assumptions:"], 
        assumptionListCells[ kb, ",", "."]
		};

proofStepText[ step_String, lang, ___] := {
	textCell[ ToString[ StringForm[ "We have no explanatory text for step '``'. Please implement the respective case for the function 'proofStepText'.", step]]]
	};

subProofHeader[ step_String, lang, ___] := {
	textCell[ ToString[ StringForm[ "We have no explanatory header text for subproofs of step '``'. Please implement the respective case for the function 'subProofHeader'.", step]]]
	};

] (* With *)

