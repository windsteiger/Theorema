(* Theorema 
    Copyright (C) 1995-2014 The Theorema Group

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
 
     If you modify this file, then a new entry must have been added to the respective file in
     the "English" directory already.

     In this file, either
      1) copy the english entry into the corresponding section named "UNTRANSLATED" (there are
         several in this file 
	       or
      2) translate the english entry and add it in correct alphabetical order here 
         (case-insensitive).
      
   *********************************************************************************************
   -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- 
   *********************************************************************************************
 *)

(* ::Section:: *)
(* Public Declaration Part: executes in Theorema`Provers` *)

With[ {lang = "German"},
(* TRANSLATED *)	
	MessageName[ initialProofSituation, "usage", lang] = "Die Beweissituation am Anfang des Beweises";
	MessageName[ invalidProofNode, "usage", lang] = "Wird verwendet, wenn eine Beweisstrategie einen ung\[UDoubleDot]ltigen Beweisknoten erzeugt";

	MessageName[ levelSat, "usage", lang] = "Level Saturation";

	MessageName[ noApplicableRule, "usage", lang] = "Beweis scheitert, weil keine regel anwendbar ist";

	MessageName[ openProofSituation, "usage", lang] = "Eine offene Beweissituation";

	MessageName[ proofAlternatives, "usage", lang] = "Beweisalternativen wenn verschiedene Beweisregeln anwendbar sind";

	MessageName[ searchDepthLimit, "usage", lang] = "Beweis stoppt beim Erreichen der maximalen Suchtiefe";

(* UNTRANSLATED *)

] (* With *)

(* ::Section:: *)
(* Private Implementation Part: executes in Theorema`Provers`Private` *)

Begin["`Private`"]

With[ {lang = "German"},
(* TRANSLATED *)

inlineTheoremaExpressionSeq[ {f_}, lang] := inlineTheoremaExpression[f];
inlineTheoremaExpressionSeq[ {f_, g_}, lang] := {inlineTheoremaExpression[f], " und ", inlineTheoremaExpression[g]};
inlineTheoremaExpressionSeq[ {f_, m__, g_}, lang] := Join[ {inlineTheoremaExpression[f]}, 
	Riffle[ Map[ inlineTheoremaExpression, {m}], ", ", {1, -2, 2}],
	{" und ", inlineTheoremaExpression[g]}];
inlineTheoremaExpressionSeq[ args___] := unexpected[ inlineTheoremaExpressionSeq, {args}];

formulaReferenceSequence[ {f_}, lang] := formulaReference[f];
formulaReferenceSequence[ {f_, g_}, lang] := {formulaReference[f], " und ", formulaReference[g]};
formulaReferenceSequence[ {f_, m__, g_}, lang] := Join[ {formulaReference[f]}, 
	Riffle[ Map[ formulaReference, {m}], ", ", {1, -2, 2}],
	{" und ", formulaReference[g]}];
formulaReferenceSequence[ args___] := unexpected[ formulaReferenceSequence, {args}];



proofStepText[ initialProofSituation, lang, {}, {{goal_FML$}}, pVal_] := {If[ pVal === proved, textCell[ "Wir beweisen:"], textCell[ "Wir sollen beweisen:"]], 
         goalCell[ goal],
         textCell[ "ohne zus\[ADoubleDot]tzliche Annahmen."]
         };
proofStepText[ initialProofSituation, lang, {}, {{goal_FML$, kb__FML$}}, pVal_] := {If[ pVal === proved, textCell[ "Wir beweisen:"], textCell[ "Wir sollen beweisen:"]], 
         goalCell[ goal],
         textCell[ "unter den zus\[ADoubleDot]tzliche Annahmen:"], 
         assumptionListCells[ {kb}, ",", "."]
         };

proofStepText[ invalidProofNode, lang, expr_, ___] := {textCell[ "Die Beweisstrategie hat einen ung\[UDoubleDot]ltigen Beweisknoten erzeugt."],
	Cell[ BoxData[ ToBoxes[ expr]], "Print"]};


proofStepText[ levelSat, lang, u_List, g_List, pVal_] := Module[{i, cells = {textCell[ "Aus dem verf\[UDoubleDot]gbaren Wissen kann neues Wissen hergeleitet werden."]}},
	Do[
		cells = Join[ cells, {textCell[ "Aus ", formulaReferenceSequence[ u[[i]], lang], " folgt"], assumptionListCells[ g[[i]], ",", "."]}],
		{i, Length[ u]}
	];
	cells
];

proofStepText[ noApplicableRule, lang, ps_, {}, pVal_] := 
	{Cell[ CellGroupData[
		Join[{textCell[ "Es ist keine Beweisregel anwendbar. Die offene Beweissituation lautet:"]},
			proofStepText[ openProofSituation, lang, ps, {}]
		]
	]]};


(* The data for openProofSituation comes from a PRFSIT$, which has no proofValue yet. Hence, we cannot pass a pVal as last parameter,
   like we do it in all other proofStepText cases. This is no problem, since we don't need a pVal here anyway. *)         
proofStepText[ openProofSituation, lang, {ps:{goal_FML$, {}, ___}}, {}] := {textCell[ "Offene Beweissituation"], 
		textCell[ "Wir haben zu beweisen:"],
		goalCell[ goal],
    	textCell[ "ohne zus\[ADoubleDot]tzliche Annahmen."],
    	Cell[ CellGroupData[ {Cell[ "Beweisituationsdaten (zum Debuggen)", "Text"],
			 Cell[ BoxData[ ToBoxes[ ps]], "Input"]}, Closed]]
		};

proofStepText[ openProofSituation, lang, {ps:{goal_FML$, kb_, ___}}, {}] := {textCell[ "Offene Beweissituation"], 
		textCell[ "Wir haben zu beweisen:"],
		goalCell[ goal],
    	textCell[ "unter den zus\[ADoubleDot]tzliche Annahmen:"], 
        assumptionListCells[ kb, ",", "."],
    	Cell[ CellGroupData[ {Cell[ "Beweisituationsdaten (zum Debuggen)", "Text"],
			 Cell[ BoxData[ ToBoxes[ ps]], "Input"]}, Closed]]
		};

proofStepText[ proofAlternatives, lang, ___] := {textCell[ "Wir haben verschiedene M\[ODoubleDot]glichkeiten, den Beweis fortzusetzen."]};

subProofHeader[ proofAlternatives, lang, ___, pVal_, {p_}] := {textCell[ ToString[ StringForm[ "Alternative ``:", p]]]};

proofStepText[ searchDepthLimit, lang, ps_, {}, ___] :=
	Join[{textCell[ "Maximale Suchtiefe erreicht! Die Offene Beweissituation lautet:"]}, 
		proofStepText[ openProofSituation, lang, ps, {}]
	];

proofStepText[ step_Symbol, lang, r___] := {
	textCell[ ToString[ StringForm[ "Es gibt keinen Text zu '``'. Bitte in der Funktion 'proofStepText' einen entsprechenden Fall implementieren. Parameter: ``", step, {r}]]]
	};

subProofHeader[ step_Symbol, lang, ___] := {
	textCell[ ToString[ StringForm[ "Es gibt keinen Text zu Unterbeweisen zu '``'. Bitte in der Funktion 'subProofHeader' einen entsprechenden Fall implementieren. Parameter: ``", step, {r}]]]
	};

(* UNTRANSLATED *)

] (* With *)

End[]
