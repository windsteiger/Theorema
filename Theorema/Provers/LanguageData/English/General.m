
With[ {lang = "English"},

proofStepText[ "Initial", lang, goal_, kb_] := {textCell[ "We have to prove:"], 
         goalCell[ goal], 
         textCell[ "under the assumptions:"], 
         assumptionListCells[ kb, ",", "."]
         };
         
proofStepText[ "Proof Situation", lang, goal_, ___] := {textCell[ "In order to prove", referenceCell[ goal], "we have to ..."]};

proofStepText[ step_, lang, goal_, ___] := {textCell[ StringForm[ "We have no explanatory text for step '``'. Please implement the respective case for the function '``'.", step, "proofStepText"]]};

] (* With *)

