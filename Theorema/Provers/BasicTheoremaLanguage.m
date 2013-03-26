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
PRFSIT$[ goal:FML$[ _, g_, __], {___, k:FML$[ _, g_, __], ___}, ___] :> 
	proofSucceeds[ makePRFINFO[ name -> goalInKB, used -> {goal, k}]]

inferenceRule[ contradictionKB] = 
PRFSIT$[ goal_FML$, {___, k:FML$[ _, phi_, __], ___, c:FML$[ _, Not$TM[ phi_], __], ___} | {___, k:FML$[ _, Not$TM[ phi_], __], ___, c:FML$[ _, phi_, __], ___}, ___] :> 
	proofSucceeds[ makePRFINFO[ name -> contradictionKB, used -> {k, c}]]

inferenceRule[ falseInKB] =
PRFSIT$[ goal_FML$, {___, k:FML$[ _, False | Not$TM[ True], __], ___}, ___] :> 
	proofSucceeds[ makePRFINFO[ name -> falseInKB, used -> k]]

inferenceRule[ trueGoal] =
PRFSIT$[ goal:FML$[ _, True | Not$TM[ False], __], _List, ___] :> 
	proofSucceeds[ makePRFINFO[ name -> trueGoal, used -> goal]]
	
(* ::Section:: *)
(* Connectives *)

(* ::Subsection:: *)
(* NOT *)

inferenceRule[ notGoal] = 
PRFSIT$[ g:FML$[ _, Not$TM[ a_], __], k_List, id_, rest___?OptionQ] :> 
	Module[ {opp},
		opp = makeFML[ formula -> a];
		makeANDNODE[ makePRFINFO[ name -> notGoal, used -> g, generated -> opp], 
			newSubgoal[ goal -> makeFML[ formula -> False, label -> "F"], kb -> prependKB[ k, opp], rest]
		]
	]

inferenceRule[ contradiction] = 
PRFSIT$[ g:FML$[ _, a_, __] /; !TrueQ[ !a] && FreeQ[ g, _META$], k_List, id_, rest___?OptionQ] :> 
	Module[ {opp},
		opp = makeFML[ formula -> Not$TM[ a]];
		makeANDNODE[ makePRFINFO[ name -> contradiction, used -> g, generated -> opp], 
			newSubgoal[ goal -> makeFML[ formula -> False, label -> "F"], kb -> prependKB[ k, opp], rest]
		]
	]
	
(* ::Subsection:: *)
(* AND *)

inferenceRule[ andGoal] = 
PRFSIT$[ g:FML$[ _, And$TM[ c__], lab_, ___] /; FreeQ[ {c}, _META$], k_List, id_, rest___?OptionQ] :> 
	Module[ {conj},
		conj = MapIndexed[ makeFML[ formula -> #1, label -> lab <> "." <> ToString[ #2[[1]]]]&, {c}];
		makeANDNODE[ makePRFINFO[ name -> andGoal, used -> g, generated -> conj], 
			Map[ newSubgoal[ goal -> #, kb -> k, rest]&, conj]
		]
	]

inferenceRule[ andKB] = 
PRFSIT$[ g_, {pre___, k:FML$[ _, And$TM[ c__], lab_, ___], post___}, id_, rest___?OptionQ] :> 
	Module[ {conj},
		conj = MapIndexed[ makeFML[ formula -> #1, label -> lab <> "." <> ToString[ #2[[1]]]]&, {c}];
		makeANDNODE[ makePRFINFO[ name -> andKB, used -> k, generated -> conj], 
			newSubgoal[ goal -> g, kb -> joinKB[ {pre}, conj, {post}], rest]
		]
	]


(* ::Subsection:: *)
(* OR *)

inferenceRule[ orGoal] = 
PRFSIT$[ g:FML$[ _, Or$TM[ a__, b_], lab_, ___] /; FreeQ[ {a, b}, _META$], k_List, id_, rest___?OptionQ] :> 
	Module[ {negAssum, newG},
		negAssum = MapIndexed[ makeFML[ formula -> Not$TM[#1], label -> lab <> "." <> ToString[ #2[[1]]]]&, {a}];
		newG = makeFML[ formula -> b];
		makeANDNODE[ makePRFINFO[ name -> orGoal, used -> g, generated -> Append[ negAssum, newG]], 
			newSubgoal[ goal -> newG, kb -> joinKB[ negAssum, k], rest]
		]
	]

inferenceRule[ orKB] = 
PRFSIT$[ g_, {pre___, k:FML$[ _, Or$TM[ c__], lab_, ___], post___}, id_, rest___?OptionQ] :> 
	Module[ {caseAssum},
		caseAssum = MapIndexed[ makeFML[ formula -> #1, label -> lab <> "." <> ToString[ #2[[1]]]]&, {c}];
		makeANDNODE[ makePRFINFO[ name -> orKB, used -> k, generated -> caseAssum], 
			Map[ newSubgoal[ goal -> g, kb -> prependKB[{pre, post}, #], rest]&, caseAssum]
		]
	]


(* ::Subsection:: *)
(* IMPLIES *)

inferenceRule[ implGoalDirect] = 
PRFSIT$[ g:FML$[ _, Implies$TM[ P_, Q_], __], k_List, id_, rest___?OptionQ] :> 
	Module[ {left, right},
		left = makeFML[ formula -> P];
		right = makeFML[ formula -> Q];
		makeANDNODE[ makePRFINFO[ name -> implGoalDirect, used -> g, generated -> {left, right}], 
			newSubgoal[ goal -> right, kb -> prependKB[ k, left], rest]]
	]

inferenceRule[ implGoalCP] = 
PRFSIT$[ g:FML$[ _, Implies$TM[ P_, Q_], __], k_List, id_, rest___?OptionQ] :> 
	Module[ {negLeft, negRight},
		negLeft = makeFML[ formula -> Not$TM[ P]];
		negRight = makeFML[ formula -> Not$TM[ Q]];
		makeANDNODE[ makePRFINFO[ name -> implGoalCP, used -> g, generated -> {negRight, negLeft}], 
			newSubgoal[ goal -> negLeft, kb -> prependKB[ k, negRight], rest]]
	]

inferenceRule[ modusPonens] = 
ps:PRFSIT$[ g_, k:{___, impl:FML$[ _, Implies$TM[ P_, Q_], __], ___, lhs:FML$[ _, P_, __], ___}, id_, rest___?OptionQ]|
ps:PRFSIT$[ g_, k:{___, lhs:FML$[ _, P_, __], ___, impl:FML$[ _, Implies$TM[ P_, Q_], __], ___}, id_, rest___?OptionQ] :> 
	Catch[
        Module[ {rhs, locInfo = ps.local, mp, implK = impl.key, lhsK = lhs.key},
            mp = getLocalInfo[ locInfo, "modusPonens"];
            If[ MemberQ[ mp, {lhsK, implK}],
            	(* Modus Ponens has already been applied for those forms *)
                Throw[ $Failed]
            ];
            rhs = makeFML[ formula -> Q];
            locInfo = putLocalInfo[ locInfo, "modusPonens" -> Prepend[ mp, {lhsK, implK}]];
            makeANDNODE[ makePRFINFO[ name -> modusPonens, used -> {impl, lhs}, generated -> rhs], 
                newSubgoal[ goal -> g, kb -> prependKB[ k, rhs], local -> locInfo, rest]]
        ]
    ]


(* ::Subsection:: *)
(* IFF *)

inferenceRule[ equivGoal] = 
PRFSIT$[ g:FML$[ _, Iff$TM[ P_, Q_], __], k_List, id_, rest___?OptionQ] :> 
	Module[ {left2right, right2left},
		left2right = makeFML[ formula -> Implies$TM[ P, Q]];
		right2left = makeFML[ formula -> Implies$TM[ Q, P]];
		makeANDNODE[ makePRFINFO[ name -> equivGoal, used -> g, generated -> {left2right, right2left}], 
			{newSubgoal[ goal -> left2right, kb -> k, rest],
			newSubgoal[ goal -> right2left, kb -> k, rest]}
		]
	]

(* ::Section:: *)
(* Quantifiers *)

(* ::Subsection:: *)
(* FORALL *)

inferenceRule[ forallGoal] = 
ps:PRFSIT$[ g:FML$[ _, u:Forall$TM[ rng_, cond_, A_], __], k_List, id_, rest___?OptionQ] :> 
	Module[ {faBui, simp, rc, r, c, f, fix, newConds, newGoal, locInfo, locC},
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
				locInfo = ps.local;
				locC = getLocalInfo[ locInfo, "constants"];
				locInfo = putLocalInfo[ locInfo, "constants" -> Prepend[ locC, fix]];
				newConds = Map[ makeFML[ formula -> #]&, DeleteCases[ Append[ r, c], True]];
				newGoal = makeFML[ formula -> f];
				makeANDNODE[ makePRFINFO[ name -> forallGoal, used -> g, generated -> Prepend[ newConds, newGoal], "abf" -> rngConstants[ fix]], 
					newSubgoal[ goal -> newGoal, kb -> joinKB[ newConds, k], local -> locInfo, rest]]
			],
			(* else *)
			simp = makeFML[ formula -> simp];
			makeANDNODE[ makePRFINFO[ name -> forallGoal, used -> g, generated -> simp], 
				newSubgoal[ goal -> simp, kb -> k, rest]]
		]
	]

(* ::Subsection:: *)
(* EXITSTS *)

inferenceRule[ existsGoal] = 
PRFSIT$[ g:FML$[ _, u:Exists$TM[ rng_, cond_, A_], __], k_List, id_, rest___?OptionQ] :> 
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
				makeANDNODE[ makePRFINFO[ name -> existsGoal, used -> g, generated -> newGoal, "meta" -> meta], 
					newSubgoal[ goal -> newGoal, kb -> k, rest]]
			],
			(* else *)
			simp = makeFML[ formula -> simp];
			makeANDNODE[ makePRFINFO[ name -> existsGoal, used -> g, generated -> simp], 
				newSubgoal[ goal -> simp, kb -> k, rest]]
		]
	]

inferenceRule[ existsKB] = 
ps:PRFSIT$[ g_, k:{pre___, e:FML$[ _, u:Exists$TM[ rng_, cond_, A_], __], post___}, id_, rest___?OptionQ] :> 
	Module[ {simp, r, c, f, fix, newConds, locInfo, locC},
		simp = computeInProof[ u];
		If[ MatchQ[ simp, _Exists$TM],
			(* no simplification *)
			{{r, c, f}, fix} = arbitraryButFixed[ {rngToCondition[ rng], cond, A}, rng, {g, k}];
			locInfo = ps.local;
			locC = getLocalInfo[ locInfo, "constants"];
			locInfo = putLocalInfo[ locInfo, "constants" -> Prepend[ locC, fix]];
			newConds = Map[ makeFML[ formula -> #]&, DeleteCases[ Join[ r, {c, f}], True]];
			makeANDNODE[ makePRFINFO[ name -> existsKB, used -> e, generated -> newConds, "abf" -> rngConstants[ fix]], 
				newSubgoal[ goal -> g, kb -> joinKB[ newConds, {pre, post}], local -> locInfo, rest]],
			(* else *)
			simp = makeFML[ formula -> simp];
			makeANDNODE[ makePRFINFO[ name -> existsKB, used -> e, generated -> simp], 
				newSubgoal[ goal -> g, kb -> prependKB[ {pre, post}, simp], rest]]
		]
	]


(* ::Section:: *)
(* substitution *)

inferenceRule[ elementarySubstitution] = 
ps:PRFSIT$[ g_, k_List, id_, rest___?OptionQ] :> 
	Module[ {locInfo = ps.local, rules, usedSubst, cond, newForm, newG, substCond = {}, usedInCond = {}, newK = {}, substApplied = False, j, usedForms, genForms, replBy = {}},
		rules = getLocalInfo[ locInfo, "elemSubstRules"];
		If[ rules === {},
			(* There are no substitutions available -> rule does not apply *)
			$Failed,
			(* else: we have substitutions *)
			{newForm, usedSubst, cond} = replaceRecursivelyAndTrack[ g.formula, rules];
			If[ usedSubst =!= {},
				(* rewrite applied *)
				newG = makeFML[ formula -> newForm];
				If[ !TrueQ[ cond],
					AppendTo[ substCond, cond];
					AppendTo[ usedInCond, g]
				];
				substApplied = True,
				(* else: no subst in goal *)
				newG = g
			];
			(* The first used and generated are old/new goal. If they are identical, then the proof header won't print any text for the goal part *)
			usedForms = {{g}};
			genForms = {{newG}};
			AppendTo[ replBy, Union[ usedSubst]];
			Do[
                {newForm, usedSubst, cond} = replaceRecursivelyAndTrack[ k[[j]].formula, rules];
                If[ usedSubst =!= {},
                    (* rewrite applied *)
                    newForm = makeFML[ formula -> newForm];
                    If[ !TrueQ[ cond],
						AppendTo[ substCond, cond];
						AppendTo[ usedInCond, k[[j]]]
					];
                    appendToKB[ newK, newForm];
                    AppendTo[ usedForms, {k[[j]]}];
                    AppendTo[ genForms, {newForm}];
					AppendTo[ replBy, Union[ usedSubst]];
                    substApplied = True,
                    (* else: no subst in this formula *)
                    appendToKB[ newK, k[[j]]]
                ],
                {j, Length[ k]}
            ];
            If[ substApplied,
            	makeANDNODE[ makePRFINFO[ name -> elementarySubstitution, used -> usedForms, generated -> genForms, "usedSubst" -> replBy], 
					newSubgoal[ goal -> newG, kb -> newK, local -> locInfo, rest]],
				$Failed
            ]
		]
	]

(* ::Section:: *)
(* Expand Definitions *)

inferenceRule[ expandDef] = 
ps:PRFSIT$[ g_, k_List, id_, rest___?OptionQ] :> 
	Module[ {locInfo = ps.local, rules, usedDefs, cond, new, newG, newForm, newK = {}, defExpand = False, defCond = {}, usedInCond = {}, j, usedForms, genForms, replBy = {}, newGoals},
		rules = getLocalInfo[ locInfo, "definitionRules"];
		If[ rules === {},
			(* There are no definitions available at all in this proof -> expanding defs does not apply *)
			$Failed,
			(* else: we have definition rewrite rules *)
			{new, usedDefs, cond} = replaceAndTrack[ g.formula, rules];
			If[ usedDefs =!= {} && freeVariables[ cond] === {},
				(* rewrite applied *)
				(* in this case, the result is of the form {newForm, cond}, where cond are conditions to be fulfilled in order to allow the rewrite *)
				newG = makeFML[ formula -> new];
				If[ !TrueQ[ cond],
					AppendTo[ defCond, cond];
					AppendTo[ usedInCond, g]
				];
				defExpand = True,
				(* else: no def expansion in goal *)
				newG = g
			];
			(* The first used and generated are old/new goal. If they are identical, then the proof header won't print any text for the goal part *)
			usedForms = {{g}};
			genForms = {{newG}};
			AppendTo[ replBy, Union[ usedDefs]];
			Do[
                {new, usedDefs, cond} = replaceAndTrack[ k[[j]].formula, rules];
                If[ usedDefs =!= {} && freeVariables[ cond] === {},
                    (* rewrite applied *)
                    newForm = makeFML[ formula -> new];
					If[ !TrueQ[ cond],
						AppendTo[ defCond, cond];
						AppendTo[ usedInCond, k[[j]]]
					];
                    appendToKB[ newK, newForm];
                    AppendTo[ usedForms, {k[[j]]}];
                    AppendTo[ genForms, {newForm}];
					AppendTo[ replBy, Union[ usedDefs]];
                    defExpand = True,
                    (* else: no def expansion in this formula *)
                    appendToKB[ newK, k[[j]]]
                ],
                {j, Length[ k]}
            ];
            If[ defExpand,
            	newGoals = {newSubgoal[ goal -> newG, kb -> newK, local -> locInfo, rest]};
            	If[ defCond =!= {},
            		newForm = makeFML[ formula -> makeConjunction[ defCond, And$TM]];
            		AppendTo[ newGoals, newSubgoal[ goal -> newForm, kb -> k, local -> locInfo, rest]],
            		(* else *)
            		newForm = True
            	];
            	(*
            		If no conditions have been generated, then newGoals contains only ONE SUBGOAL and the last element of usedForms is {}.
            		Otherwise, we have TWO SUBGOALS, and the last element of usedForms is non-empty. We can rely on this when generating the proof text.
            	*)
            	AppendTo[ usedForms, usedInCond];
            	AppendTo[ genForms, {newForm}];
            	makeANDNODE[ makePRFINFO[ name -> expandDef, used -> usedForms, generated -> genForms, "usedDefs" -> replBy], 
					newGoals],
				$Failed
            ]
		]
	]


(* ::Section:: *)
(* Equalities in KB *)

inferenceRule[ eqIffKB] = 
ps:PRFSIT$[ g_, k:{___, FML$[ _, (Iff$TM|Equal$TM)[ _, _?isQuantifierFree], __], ___}, id_, rest___?OptionQ] :> 
	Module[ {locInfo = ps.local, rules, form, elemSubs = {}, nonSubs = {}, j},
		rules = getLocalInfo[ locInfo, "elemSubstRules"];
		Do[
        	form = k[[j]];
        	Switch[ form,
        		FML$[ _, (Iff$TM|Equal$TM)[ lhs_, rhs_?isQuantifierFree], __],
        		appendToKB[ elemSubs, form],
        		_,
        		appendToKB[ nonSubs, form]
        	],
        	{j, Length[k]}
        ];
        locInfo = putLocalInfo[ locInfo, "elemSubstRules" -> Join[ rules, defsToRules[ elemSubs]]];
		makeANDNODE[ makePRFINFO[ name -> eqIffKB, used -> {elemSubs}, generated -> {}], 
			newSubgoal[ goal -> g, kb -> nonSubs, local -> locInfo, rest]
		]
	]


(* ::Section:: *)
(* Instantiation *)

(*
  We assume the local info of the PRFSIT has an entry "constants" -> L. The list L is a list of elementary ranges, e.g. SIMPRNG$, SETRNG$, etc.
  Elements of the form RNG$[...] in L are ranges that have not yet been processed for instantiation, i.e. if L is free of RNG$_ then there
  are no new contants for instantiation, otherwise we need to instantiate using RNG$ and then add the ranges (without the RNG$ wrapper) to L.
*)

inferenceRule[ instantiate] = 
ps:PRFSIT$[ g_, K_List, id_, rest___?OptionQ] :> 
	Module[ {locInfo = ps.local, oldConst, newConst, univKB = Cases[ K, FML$[ _, _Forall$TM, _]], instForm, orig = {}, new = {}, inst = {}, i},
        (
        instForm = Map[ instantiateForall[ #, newConst]&, univKB];
        (* for each form in univKB we get a list {forms, inst}, where
        	forms is a list of instantiations of form and
        	inst is a list of substitutions, such that inst_i applied to form gives forms_i.
        *)
        Do[
        	If[ instForm[[ i, 1]] === {},
        		Continue[],
        		(* else *)
        		AppendTo[ orig, {univKB[[i]]}];
        		AppendTo[ new, instForm[[ i, 1]]];
        		AppendTo[ inst, instForm[[ i, 2]]]
        	],
        	{i, Length[ instForm]}
        ];
        locInfo = putLocalInfo[ locInfo, "constants" -> Join[ Apply[ List, newConst], oldConst]];
		makeANDNODE[ makePRFINFO[ name -> instantiate, used -> orig, generated -> new, "instantiation" -> inst], 
			newSubgoal[ goal -> g, kb -> Fold[ joinKB[ #2, #1]&, K, new], local -> locInfo, rest]
		]
		) /; ({newConst, oldConst} = constants[ locInfo]; newConst =!= {})
	]

constants[ loc_List] :=
	Module[{L = getLocalInfo[ loc, "constants"], new, old},
		new = Cases[ L, _RNG$];
		old = Complement[ L, new];
		{Apply[ Join, new], old}
	]
newConstants[ args___] := unexpected[ newConstants, {args}]

instantiateForall[ f:FML$[ _, Forall$TM[ R1_RNG$, C_, A_], __], R2_RNG$] :=
    Module[ {possibleInst = Select[ Tuples[ {R1, R2}], compatibleRange], inst = {}, subst = {}, S, i},
        Do[
        	S = MapThread[ Rule, {rngVariables[ RNG$[ possibleInst[[i, 1]]]], rngConstants[ RNG$[ possibleInst[[i, 2]]]]}];
            AppendTo[ inst, makeFML[ formula -> substituteFree[ simplifiedForall[ Forall$TM[ DeleteCases[ R1, possibleInst[[i, 1]]], C, A]], S]]];
            subst = Join[ subst, S],
        	{i, Length[ possibleInst]}
        ];
        {inst, subst}
    ]
instantiateForall[ args___] := unexpected[ instantiateForall, {args}]

compatibleRange[ {SIMPRNG$[ _], _}] := True
compatibleRange[ {STEPRNG$[ _, l1_Integer, u1_Integer, s_], STEPRNG$[ _, l2_Integer, u2_Integer, s_]}] /; l1 <= l2 && u1 >= u2 := True
compatibleRange[ {SETRNG$[ _, s_Set$TM], SETRNG$[ _, s_Set$TM]}] := True
compatibleRange[ {_, _}] := False
compatibleRange[ args___] := unexpected[ compatibleRange, {args}]


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
	{eqIffKB, True, True, 3}
	};

registerRuleSet[ "Quantifier Rules", quantifierRules, {
	{forallGoal, True, True, 10},
	{forallKB, True, True, 70},
	{instantiate, True, True, 35},
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