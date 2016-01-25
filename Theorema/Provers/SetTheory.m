(* Theorema 
    Copyright (C) 2010 The Theorema Group

    This file is part of Theorema 2.0
    
    Theorema 2.0 is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Theorema 2.0 is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

BeginPackage[ "Theorema`Provers`SetTheory`"]

Needs[ "Theorema`Provers`"]
Needs[ "Theorema`Common`"]
Needs[ "Theorema`Language`"]
Needs[ "Theorema`Provers`BasicTheoremaLanguage`"]

Begin["`Private`"]



(* ::Subsection:: *)
(* AND *)

inferenceRule[ andGoal] = 
PRFSIT$[ g:FML$[ _, And$TM[ c__], lab_, ___] /; FreeQ[ {c}, _META$], k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {conj},
		conj = MapIndexed[ makeGoalFML[ formula -> #1, label -> lab <> "." <> ToString[ #2[[1]]]]&, {c}];
		makeANDNODE[ makePRFINFO[ name -> andGoal, used -> g], 
			Map[ toBeProved[ goal -> #, kb -> k, rest]&, conj]
		]
	]
]

inferenceRule[ andKB] = 
PRFSIT$[ g_, {pre___, k:FML$[ _, And$TM[ c__], lab_, ___], post___}, id_, rest___?OptionQ] :> performProofStep[
	Module[ {conj},
		conj = MapIndexed[ makeAssumptionFML[ formula -> #1, label -> lab <> "." <> ToString[ #2[[1]]]]&, {c}];
		makeANDNODE[ makePRFINFO[ name -> andKB, used -> k], 
			toBeProved[ goal -> g, kb -> joinKB[ conj, {pre, post}], rest]
		]
	]
]


(* ::Subsection:: *)
(* OR *)

inferenceRule[ orGoal] = 
PRFSIT$[ g:FML$[ _, Or$TM[ a__, b_], lab_, ___] /; FreeQ[ {a, b}, _META$], k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {negAssum, newG},
		negAssum = MapIndexed[ makeAssumptionFML[ formula -> Not$TM[#1], label -> lab <> "." <> ToString[ #2[[1]]]]&, {a}];
		newG = makeGoalFML[ formula -> b];
		makeANDNODE[ makePRFINFO[ name -> orGoal, used -> g], 
			toBeProved[ goal -> newG, kb -> joinKB[ negAssum, k], rest]
		]
	]
]

inferenceRule[ orKB] = 
PRFSIT$[ g_, {pre___, k:FML$[ _, Or$TM[ c__], lab_, ___], post___}, id_, rest___?OptionQ] :> performProofStep[
	Module[ {caseAssum},
		caseAssum = MapIndexed[ makeAssumptionFML[ formula -> #1, label -> lab <> "." <> ToString[ #2[[1]]]]&, {c}];
		makeANDNODE[ makePRFINFO[ name -> orKB, used -> k], 
			Map[ Block[ {$rewriteRules = {}}, toBeProved[ goal -> g, kb -> prependKB[{pre, post}, #], rest]]&, caseAssum]
		]
	]
]



(* ::Section:: *)
(* Quantifiers *)

(* ::Subsection:: *)
(* FORALL *)

inferenceRule[ forallGoal] = 
ps:PRFSIT$[ g:FML$[ _, u:Forall$TM[ rng_, cond_, A_], __], k_List, id_, rest___?OptionQ] :> performProofStep[
	Module[ {faBui, simp, rc, r, c, f, fix, newConds, newGoal, locC},
		(* we use computation regardless whether it is activated or not ... *)
		faBui = buiActProve[ "Forall"];
		buiActProve[ "Forall"] = True;
		simp = computeInProof[ u];
		buiActProve[ "Forall"] = faBui;
		If[ MatchQ[ simp, _Forall$TM],
			(* no simplification *)
			rc = rngToCondition[ rng];
			If[ !FreeQ[ rc, $Failed], 
				$Failed,
				(* else *)
				{{r, c, f}, fix} = arbitraryButFixed[ {rc, cond, A}, rng, {g, k}];
				locC = getOptionalComponent[ ps, "constants"];
				newGoal = makeGoalFML[ formula -> f];
				newConds = Map[ makeAssumptionFML[ formula -> #]&, DeleteCases[ Append[ r, c], True]];
				makeANDNODE[ makePRFINFO[ name -> forallGoal, used -> g, "abf" -> rngConstants[ fix]], 
					toBeProved[ goal -> newGoal, kb -> joinKB[ newConds, k], "constants" -> Prepend[ locC, fix], rest]]
			],
			(* else *)
			simp = makeGoalFML[ formula -> simp];
			makeANDNODE[ makePRFINFO[ name -> forallGoal, used -> g], 
				toBeProved[ goal -> simp, kb -> k, rest]]
		]
	]
]


(* ::Section:: *)
(* Rule composition *)
	
setTheoryRules = {"Set Theory Rules",
	{goalRewriting, True, True, 22},
	{knowledgeRewriting, True, True, 25},
	{elementarySubstitution, True, True, 8},
	{expandDef, True, True, 80},
	{implicitDef, True, True, 80}
};

registerRuleSet[ "Set Theory Prover", setTheoryBasicLanguageRules, {
	terminationRules,
	quantifierRules, 
	connectiveRules, 
	equalityRules,
	rewritingRules,
	specialArithmeticRules,
	setTheoryRules,
	{contradiction, False, True, 100}
	}]

End[]

EndPackage[]