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

BeginPackage[ "Theorema`Provers`BasicTheoremaLanguage`"]

Needs[ "Theorema`Provers`"]
Needs[ "Theorema`Common`"]
Needs[ "Theorema`Language`"]

Begin["`Private`"]


(* ::Section:: *)
(* Termination rules *)

inferenceRule[ goalInKB] = 
PRFSIT$[ goal:FML$[ _, g_, _], {___, k:FML$[ _, g_, _], ___}, i_String, ___] :> 
	proofSucceeds[ makePRFINFO[ name -> goalInKB, used -> {goal, k}, id -> i]]

inferenceRule[ contradictionKB] = 
PRFSIT$[ goal_FML$, {___, k:FML$[ _, phi_, _], ___, c:FML$[ _, Not$TM[ phi_], _], ___} | {___, k:FML$[ _, Not$TM[ phi_], _], ___, c:FML$[ _, phi_, _], ___}, i_String, ___] :> 
	proofSucceeds[ makePRFINFO[ name -> contradictionKB, used -> {k, c}, id -> i]]

inferenceRule[ falseInKB] =
PRFSIT$[ goal_FML$, {___, k:FML$[ _, False | Not$TM[ True], _], ___}, i_String, ___] :> 
	proofSucceeds[ makePRFINFO[ name -> falseInKB, used -> k, id -> i]]

inferenceRule[ trueGoal] =
PRFSIT$[ goal:FML$[ _, True | Not$TM[ False], _], _List, i_String, ___] :> 
	proofSucceeds[ makePRFINFO[ name -> trueGoal, used -> goal, id -> i]]
	
(* ::Section:: *)
(* Connectives *)

(* ::Subsection:: *)
(* NOT *)

inferenceRule[ notGoal] = 
PRFSIT$[ g:FML$[ _, Not$TM[ a_], lab_], k_List, i_String, rest___?OptionQ] :> 
	Module[ {opp},
		opp = makeFML[ formula -> a];
		makeANDNODE[ makePRFINFO[ name -> notGoal, used -> g, generated -> opp, id -> i], 
			newSubgoal[ goal -> makeFML[ formula -> False, label -> "F"], kb -> Prepend[ k, opp], rest]
		]
	]

inferenceRule[ contradiction] = 
PRFSIT$[ g:FML$[ _, a_, lab_] /; !TrueQ[ !a] && FreeQ[ g, _META$], k_List, i_String, rest___?OptionQ] :> 
	Module[ {opp},
		opp = makeFML[ formula -> Not$TM[ a]];
		makeANDNODE[ makePRFINFO[ name -> contradiction, used -> g, generated -> opp, id -> i], 
			newSubgoal[ goal -> makeFML[ formula -> False, label -> "F"], kb -> Prepend[ k, opp], rest]
		]
	]
	
(* ::Subsection:: *)
(* AND *)

inferenceRule[ andGoal] = 
PRFSIT$[ g:FML$[ _, And$TM[ c__], lab_] /; FreeQ[ g, _META$], k_List, i_String, rest___?OptionQ] :> 
	Module[ {conj},
		conj = MapIndexed[ makeFML[ formula -> #1, label -> lab <> "." <> ToString[ #2[[1]]]]&, {c}];
		makeANDNODE[ makePRFINFO[ name -> andGoal, used -> g, generated -> conj, id -> i], 
			Map[ newSubgoal[ goal -> #, kb -> k, rest]&, conj]
		]
	]

inferenceRule[ andKB] = 
PRFSIT$[ g_, {pre___, k:FML$[ _, And$TM[ c__], lab_], post___}, i_String, rest___?OptionQ] :> 
	Module[ {conj},
		conj = MapIndexed[ makeFML[ formula -> #1, label -> lab <> "." <> ToString[ #2[[1]]]]&, {c}];
		makeANDNODE[ makePRFINFO[ name -> andKB, used -> k, generated -> conj, id -> i], 
			newSubgoal[ goal -> g, kb -> Join[ {pre}, conj, {post}], rest]
		]
	]


(* ::Subsection:: *)
(* OR *)

inferenceRule[ orGoal] = 
PRFSIT$[ g:FML$[ _, Or$TM[ a__, b_], lab_], k_List, i_String, rest___?OptionQ] :> 
	Module[ {negAssum, newG},
		negAssum = MapIndexed[ makeFML[ formula -> Not$TM[#1], label -> lab <> "." <> ToString[ #2[[1]]]]&, {a}];
		newG = makeFML[ formula -> b];
		makeANDNODE[ makePRFINFO[ name -> orGoal, used -> g, generated -> Append[ negAssum, newG], id -> i], 
			newSubgoal[ goal -> newG, kb -> Join[ negAssum, k], rest]
		]
	]

inferenceRule[ orKB] = 
PRFSIT$[ g_, {pre___, k:FML$[ _, Or$TM[ c__], lab_], post___}, i_String, rest___?OptionQ] :> 
	Module[ {caseAssum},
		caseAssum = MapIndexed[ makeFML[ formula -> #1, label -> lab <> "." <> ToString[ #2[[1]]]]&, {c}];
		makeANDNODE[ makePRFINFO[ name -> orKB, used -> k, generated -> caseAssum, id -> i], 
			Map[ newSubgoal[ goal -> g, kb -> {#, pre, post}, rest]&, caseAssum]
		]
	]


(* ::Subsection:: *)
(* IMPLIES *)

inferenceRule[ implGoalDirect] = 
PRFSIT$[ g:FML$[ _, Implies$TM[ P_, Q_], _], k_List, i_String, rest___?OptionQ] :> 
	Module[ {left, right},
		left = makeFML[ formula -> P];
		right = makeFML[ formula -> Q];
		makeANDNODE[ makePRFINFO[ name -> implGoalDirect, used -> g, generated -> {left, right}, id -> i], 
			newSubgoal[ goal -> right, kb -> Prepend[ k, left], rest]]
	]

inferenceRule[ implGoalCP] = 
PRFSIT$[ g:FML$[ _, Implies$TM[ P_, Q_], _], k_List, i_String, rest___?OptionQ] :> 
	Module[ {negLeft, negRight},
		negLeft = makeFML[ formula -> Not$TM[ P]];
		negRight = makeFML[ formula -> Not$TM[ Q]];
		makeANDNODE[ makePRFINFO[ name -> implGoalCP, used -> g, generated -> {negRight, negLeft}, id -> i], 
			newSubgoal[ goal -> negLeft, kb -> Prepend[ k, negRight], rest]]
	]

inferenceRule[ modusPonens] = 
ps:PRFSIT$[ g_, k:{___, impl:FML$[ _, Implies$TM[ P_, Q_], _], ___, lhs:FML$[ _, P_, _], ___}, i_String, rest___?OptionQ]|
ps:PRFSIT$[ g_, k:{___, lhs:FML$[ _, P_, _], ___, impl:FML$[ _, Implies$TM[ P_, Q_], _], ___}, i_String, rest___?OptionQ] :> 
	Catch[
        Module[ {rhs, locInfo = ps.local, mp, implK = impl.key, lhsK = lhs.key},
            mp = getLocalInfo[ locInfo, "modusPonens"];
            If[ MemberQ[ mp, {lhsK, implK}],
            	(* Modus Ponens has already been applied for those forms *)
                Throw[ $Failed]
            ];
            rhs = makeFML[ formula -> Q];
            locInfo = putLocalInfo[ locInfo, "modusPonens" -> Prepend[ mp, {lhsK, implK}]];
            makeANDNODE[ makePRFINFO[ name -> modusPonens, used -> {impl, lhs}, generated -> rhs, id -> i], 
                newSubgoal[ goal -> g, kb -> Prepend[ k, rhs], local -> locInfo, rest]]
        ]
    ]


(* ::Subsection:: *)
(* IFF *)

inferenceRule[ equivGoal] = 
PRFSIT$[ g:FML$[ _, Iff$TM[ P_, Q_], _], k_List, i_String, rest___?OptionQ] :> 
	Module[ {left2right, right2left},
		left2right = makeFML[ formula -> Implies$TM[ P, Q]];
		right2left = makeFML[ formula -> Implies$TM[ Q, P]];
		makeANDNODE[ makePRFINFO[ name -> equivGoal, used -> g, generated -> {left2right, right2left}, id -> i], 
			{newSubgoal[ goal -> left2right, kb -> k, rest],
			newSubgoal[ goal -> right2left, kb -> k, rest]}
		]
	]

(* ::Section:: *)
(* Quantifiers *)

(* ::Subsection:: *)
(* FORALL *)

inferenceRule[ forallGoal] = 
PRFSIT$[ g:FML$[ _, u:Forall$TM[ rng_, cond_, A_], _], k_List, i_String, rest___?OptionQ] :> 
	Module[ {faBui, simp, rc, r, c, f, fix, newConds, newGoal},
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
				newConds = Map[ makeFML[ formula -> #]&, DeleteCases[ Append[ r, c], True]];
				newGoal = makeFML[ formula -> f];
				makeANDNODE[ makePRFINFO[ name -> forallGoal, used -> g, generated -> Prepend[ newConds, newGoal], id -> i, "abf" -> fix], 
					newSubgoal[ goal -> newGoal, kb -> Join[ newConds, k], rest]]
			],
			(* else *)
			simp = makeFML[ formula -> simp];
			makeANDNODE[ makePRFINFO[ name -> forallGoal, used -> g, generated -> simp, id -> i], 
				newSubgoal[ goal -> simp, kb -> k, rest]]
		]
	]

(* ::Subsection:: *)
(* EXITSTS *)

inferenceRule[ existsGoal] = 
PRFSIT$[ g:FML$[ _, u:Exists$TM[ rng_, cond_, A_], _], k_List, i_String, rest___?OptionQ] :> 
	Module[ {simp, rc, r, c, f, meta, newGoal},
		simp = computeInProof[ u];
		If[ MatchQ[ simp, _Exists$TM],
			(* no simplification *)
			rc = rngToCondition[ rng];
			If[ !FreeQ[ rc, $Failed], 
				$Failed,
				(* else *)
				{{r, c, f}, meta} = introduceMeta[ {rc, cond, A}, rng, {g, k}];
				newGoal = makeFML[ formula -> Apply[ And$TM, DeleteCases[ Join[ r, {c, f}], True]]];
				makeANDNODE[ makePRFINFO[ name -> existsGoal, used -> g, generated -> newGoal, id -> i, "meta" -> meta], 
					newSubgoal[ goal -> newGoal, kb -> k, rest]]
			],
			(* else *)
			simp = makeFML[ formula -> simp];
			makeANDNODE[ makePRFINFO[ name -> existsGoal, used -> g, generated -> simp, id -> i], 
				newSubgoal[ goal -> simp, kb -> k, rest]]
		]
	]

inferenceRule[ existsKB] = 
PRFSIT$[ g_, k:{pre___, e:FML$[ _, u:Exists$TM[ rng_, cond_, A_], _], post___}, i_String, rest___?OptionQ] :> 
	Module[ {simp, r, c, f, fix, newConds},
		simp = computeInProof[ u];
		If[ MatchQ[ simp, _Exists$TM],
			(* no simplification *)
			{{r, c, f}, fix} = arbitraryButFixed[ {rngToCondition[ rng], cond, A}, rng, {g, k}];
			newConds = Map[ makeFML[ formula -> #]&, DeleteCases[ Join[ r, {c, f}], True]];
			makeANDNODE[ makePRFINFO[ name -> existsKB, used -> e, generated -> newConds, id -> i, "abf" -> fix], 
				newSubgoal[ goal -> g, kb -> Join[ newConds, {pre, post}], rest]],
			(* else *)
			simp = makeFML[ formula -> simp];
			makeANDNODE[ makePRFINFO[ name -> existsKB, used -> e, generated -> simp, id -> i], 
				newSubgoal[ goal -> g, kb -> {simp, pre, post}, rest]]
		]
	]


(* ::Section:: *)
(* substitution *)

inferenceRule[ elementarySubstitution] = 
ps:PRFSIT$[ g_, k_List, i_String, rest___?OptionQ] :> 
	Module[ {locInfo = ps.local, rules, usedSubst, newForm, newG, newK = {}, substApplied = False, j, usedForms, genForms, replBy = {}},
		rules = getLocalInfo[ locInfo, "elemSubstRules"];
		If[ rules === {},
			(* There are no substitutions available -> rule does not apply *)
			$Failed,
			(* else: we have substitutions *)
			{newForm, usedSubst} = replaceRecursivelyAndTrack[ g.formula, rules];
			If[ usedSubst =!= {},
				(* rewrite applied *)
				newG = makeFML[ formula -> newForm];
				substApplied = True,
				(* else: no subst in goal *)
				newG = g
			];
			(* The first used and generated are old/new goal. If they are identical, then the proof header won't print any text for the goal part *)
			usedForms = {{g}};
			genForms = {{newG}};
			AppendTo[ replBy, Union[ usedSubst]];
			Do[
                {newForm, usedSubst} = replaceRecursivelyAndTrack[ k[[j]].formula, rules];
                If[ usedSubst =!= {},
                    (* rewrite applied *)
                    newForm = makeFML[ formula -> newForm];
                    AppendTo[ newK, newForm];
                    AppendTo[ usedForms, {k[[j]]}];
                    AppendTo[ genForms, {newForm}];
					AppendTo[ replBy, Union[ usedSubst]];
                    substApplied = True,
                    (* else: no subst in this formula *)
                    AppendTo[ newK, k[[j]]]
                ],
                {j, Length[ k]}
            ];
            If[ substApplied,
            	makeANDNODE[ makePRFINFO[ name -> elementarySubstitution, used -> usedForms, generated -> genForms, id -> i, "usedSubst" -> replBy], 
					newSubgoal[ goal -> newG, kb -> newK, local -> locInfo, rest]],
				$Failed
            ]
		]
	]

(* ::Section:: *)
(* Expand Definitions *)

inferenceRule[ expandDef] = 
ps:PRFSIT$[ g_, k_List, i_String, rest___?OptionQ] :> 
	Module[ {locInfo = ps.local, rules, usedDefs, newForm, newG, newK = {}, defExpand = False, j, usedForms, genForms, replBy = {}},
		rules = getLocalInfo[ locInfo, "definitionRules"];
		If[ rules === {},
			(* There are no definitions available at all in this proof -> expanding defs does not apply *)
			$Failed,
			(* else: we have definition rewrite rules *)
			{newForm, usedDefs} = replaceAndTrack[ g.formula, rules];
			If[ usedDefs =!= {},
				(* rewrite applied *)
				newG = makeFML[ formula -> newForm];
				defExpand = True,
				(* else: no def expansion in goal *)
				newG = g
			];
			(* The first used and generated are old/new goal. If they are identical, then the proof header won't print any text for the goal part *)
			usedForms = {{g}};
			genForms = {{newG}};
			AppendTo[ replBy, Union[ usedDefs]];
			Do[
                {newForm, usedDefs} = replaceAndTrack[ k[[j]].formula, rules];
                If[ usedDefs =!= {},
                    (* rewrite applied *)
                    newForm = makeFML[ formula -> newForm];
                    AppendTo[ newK, newForm];
                    AppendTo[ usedForms, {k[[j]]}];
                    AppendTo[ genForms, {newForm}];
					AppendTo[ replBy, Union[ usedDefs]];
                    defExpand = True,
                    (* else: no def expansion in this formula *)
                    AppendTo[ newK, k[[j]]]
                ],
                {j, Length[ k]}
            ];
            If[ defExpand,
            	makeANDNODE[ makePRFINFO[ name -> expandDef, used -> usedForms, generated -> genForms, id -> i, "usedDefs" -> replBy], 
					newSubgoal[ goal -> newG, kb -> newK, local -> locInfo, rest]],
				$Failed
            ]
		]
	]


(* ::Section:: *)
(* Equalities in KB *)

inferenceRule[ eqKB] = 
ps:PRFSIT$[ g_, k:{___, FML$[ _, (Iff$TM|Equal$TM)[ _, _?isQuantifierFree], lab_], ___}, i_String, rest___?OptionQ] :> 
	Module[ {locInfo = ps.local, rules, form, elemSubs = {}, nonSubs = {}, j},
		rules = getLocalInfo[ locInfo, "elemSubstRules"];
		Do[
        	form = k[[j]];
        	Switch[ form,
        		FML$[ _, (Iff$TM|Equal$TM)[ lhs_, rhs_?isQuantifierFree], _],
        		AppendTo[ elemSubs, form],
        		_,
        		AppendTo[ nonSubs, form]
        	],
        	{j, Length[k]}
        ];
        locInfo = putLocalInfo[ locInfo, "elemSubstRules" -> defsToRules[ elemSubs]];
		makeANDNODE[ makePRFINFO[ name -> eqKB, used -> {elemSubs}, generated -> {}, id -> i], 
			newSubgoal[ goal -> g, kb -> nonSubs, local -> locInfo, rest]
		]
	]


(* ::Section:: *)
(* Rule composition *)

terminationRules = {"Termination Rules",
	{goalInKB, True, True, 1, "term"},
	{falseInKB, True, True, 1, "term"},
	{trueGoal, True, True, 1, "term"},
	{contradictionKB, True, True, 1, "term"}
	};

connectiveRules = {"Connectives Rules", 
	{notGoal, True, True, 30},
	{andGoal, True, True, 5},
	{andKB, True, False, 5},
	{orGoal, True, True, 5},
	{orKB, True, True, 19},
	{implGoalDirect, True, True, 5},
	{implGoalCP, False, False, 10},
	{modusPonens, True, True, 30, "levelSat2"},
	{equivGoal, True, True, 10}};

equalityRules = {"Equality Rules", 
	{eqGoal, False, False, 20},
	{eqKB, True, True, 3}
	};

registerRuleSet[ "Quantifier Rules", quantifierRules, {
	{forallGoal, True, True, 10},
	{forallKB, True, True, 70},
	{existsGoal, True, True, 10},
	{existsKB, True, True, 11}
	}]

registerRuleSet[ "Basic Theorema Language Rules", basicTheoremaLanguageRules, {
	terminationRules,
	quantifierRules, 
	connectiveRules, 
	equalityRules,
	{elementarySubstitution, True, True, 4},
	{expandDef, True, True, 80},
	{contradiction, True, True, 100}
	}]

End[]

EndPackage[]