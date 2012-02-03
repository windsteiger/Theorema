(* Mathematica Package *)

BeginPackage["Theorema`Language`FormulaManipulation`"]

Needs[ "Theorema`Common`"]

Begin["`Private`"]


(* ::Subsubsection:: *)
(* splitForm *)

splitAnd[ expr:(h:Theorema`Language`And$TM|Theorema`Computation`Language`And$TM|And)[ __], v_List] :=
	Module[ {depSingle = {}, depMulti = {}, p, l = Length[ expr]},
		Do[
			p = expr[[i]];
			If[ freeVariables[ p] === v, 
				AppendTo[ depSingle, p],
				AppendTo[ depMulti, p]
			],
			{i, l}
		];
		{ makeConjunction[ depSingle, h], makeConjunction[ depMulti, h]}
	]
splitAnd[ expr_, v_List] :=
    If[ freeVariables[ expr] === v,
        { expr, True},
        { True, expr}
    ]
splitAnd[ args___] := unexpected[ splitAnd, {args}]

makeConjunction[ l_List, a_] :=
    Switch[ Length[ l],
        0,
        True,
        1,
        l[[1]],
        _,
        Apply[ a, l]
    ]
makeConjunction[ args___] := unexpected[ makeConjunction, {args}]

makeDisjunction[ l_List, a_] :=
    Switch[ Length[ l],
        0,
        False,
        1,
        l[[1]],
        _,
        Apply[ a, l]
    ]
makeDisjunction[ args___] := unexpected[ makeDisjunction, {args}]


(* ::Subsubsection:: *)
(* freeVariables *)

freeVariables[ q_[ r:(Theorema`Language`RNG$|Theorema`Computation`Language`RNG$)[x__], cond_, expr_]] := 
	Complement[ freeVariables[ {x, cond, expr}], variables[ r]]
freeVariables[ Hold[ l___]] := freeVariables[ {l}]
freeVariables[ l_List] := Apply[ Union, Map[ freeVariables, l]]
freeVariables[ f_[x___]] := freeVariables[ {f, x}]
freeVariables[ v:(Theorema`Language`VAR$|Theorema`Computation`Language`VAR$)[_]] := {v}
freeVariables[ c_] := {}
freeVariables[ args___] := unexpected[ freeVariables, {args}]


(* ::Subsubsection:: *)
(* variables *)

variables[ (Theorema`Language`RNG$|Theorema`Computation`Language`RNG$)[r___]] := Map[ #[[1]]&, {r}]
variables[ args___] := unexpected[ variables, {args}]


(* ::Subsubsection:: *)
(* specifiedVariables *)

specifiedVariables[ (Theorema`Language`RNG$|Theorema`Computation`Language`RNG$)[r___]] := Map[ extractVar, {r}]
specifiedVariables[ args___] := unexpected[ specifiedVariables, {args}]

extractVar[ r_[ (Theorema`Language`VAR$|Theorema`Computation`Language`VAR$)[ v_], ___]] := v
extractVar[ r_[ v_, ___]] := v
extractVar[ args___] := unexpected[ extractVar, {args}]


(* ::Subsubsection:: *)
(* substituteFree *)

Clear[ substituteFree]
substituteFree[ expr_Hold, {}] := expr
substituteFree[ Hold[], _] := Hold[]
substituteFree[ Hold[ q_[ r:(Theorema`Language`RNG$|Theorema`Computation`Language`RNG$)[ rng__], cond_, form_]], rules_List] :=
	Module[ {qvars = variables[ r], vars},
		vars = Select[ rules, !MemberQ[ qvars, #[[1]]]&];
		applyHold[ Hold[q], joinHold[ substituteFree[ Hold[r], vars], joinHold[ substituteFree[ Hold[cond], vars], substituteFree[ Hold[form], vars]]]]
	]
substituteFree[ Hold[ f_[x___]], rules_List] :=
	Module[ { sx = Map[ substituteFree[ Hold[#], rules]&, Hold[x]]},
		sx = Fold[ joinHold, Hold[], {ReleaseHold[ sx]}];
		applyHold[ substituteFree[ Hold[f], rules], sx]
	]
substituteFree[ x:Hold[ (Theorema`Language`VAR$|Theorema`Computation`Language`VAR$)[_]], rules_List] := x /. rules
substituteFree[ x:Hold[_], rules_List] := x
substituteFree[ expr_, rule_Rule] := substituteFree[ expr, {rule}]
substituteFree[ expr_, rules_List] := ReleaseHold[ substituteFree[ Hold[ expr], rules]]
substituteFree[ args___] := unexpected[ substituteFree, {args}]


(* ::Subsubsection:: *)
(* makeSet *)

makeSet[ x___] := Apply[ ToExpression[ "Set$TM"], Union[ {x}]]


(* ::Subsubsection:: *)
(* transferToComputation *)

transferToComputation[ form_, key_] :=
	Module[{stripUniv},
		stripUniv = stripUniversalQuantifiers[ form];
		ToExpression[ executableForm[ stripUniv, key]]
	]
transferToComputation[ args___] := unexpected[ transferToComputation, {args}]

stripUniversalQuantifiers[ Theorema`Language`Forall$TM[ r_, c_, f_]] :=
	Module[ {rc, vars, cond, inner},
		rc = rangeToCondition[ r];
		{inner, cond, vars} = stripUniversalQuantifiers[ f];
		cond = Join[ rc, cond];
		{inner, If[ !TrueQ[ c], Prepend[ cond, c], cond], Join[ variables[ r], vars]}
	]
stripUniversalQuantifiers[ Theorema`Language`Implies$TM[ l_, r_]] :=
	Module[ {vars, cond, inner},
		{inner, cond, vars} = stripUniversalQuantifiers[ r];
		{inner, Prepend[ cond, l], vars}
	]
stripUniversalQuantifiers[ expr_] := {expr, {}, {}}
stripUniversalQuantifiers[ args___] := unexpected[ stripUniversalQuantifiers, {args}]

rangeToCondition[ Theorema`Language`RNG$[ rng__]] := Map[ singleRangeToCondition, {rng}]
rangeToCondition[ args___] := unexpected[ rangeToCondition, {args}]

singleRangeToCondition[ Theorema`Language`SETRNG$[ x_, A_]] := Theorema`Language`Element$TM[ x, A]
singleRangeToCondition[ Theorema`Language`PREDRNG$[ x_, P_]] := P[ x]
singleRangeToCondition[ Theorema`Language`STEPRNG$[ x_, l_, h_, 1]] := 
	Theorema`Language`And$TM[ Theorema`Language`isInteger$TM[x], Theorema`Language`LessEqual$TM[ l, x], Theorema`Language`LessEqual$TM[ x, h]]
singleRangeToCondition[ _] := Sequence[]
singleRangeToCondition[ args___] := unexpected[ singleRangeToCondition, {args}]


executableForm[ {(Theorema`Language`Iff$TM|Theorema`Language`IffDef$TM|Theorema`Language`Equal$TM|Theorema`Language`EqualDef$TM)[ l_, r_], c_List, var_List}, key_] :=
    Block[ { $ContextPath = {"System`"}, $Context = "Global`"},
        With[ { left = execLeft[ Hold[l]], 
        	cond = makeConjunction[ Prepend[ c, "DUMMY$COND"], Theorema`Computation`Language`And$TM],
        	right = execRight[ Hold[r]]},
            StringReplace[ left <> "/;" <> execRight[ Hold[ cond]] <> ":=" <> right,
            	{ "DUMMY$COND" -> "Theorema`Computation`Language`Private`activeComputationKB[" <> ToString[ key, InputForm] <> "]",
            		"Theorema`Language`" -> "Theorema`Computation`Language`",
            		"Theorema`Knowledge`" -> "Theorema`Computation`Knowledge`"}
            ]
        ]
    ]
executableForm[ expr_, key_] := Null
executableForm[ args___] := unexpected[ executableForm, {args}]

execLeft[ e_Hold] := 
	Module[ {s},
		s = e /. Theorema`Language`VAR$[a_] :> Apply[ Pattern, {a, Blank[]}];
		ReleaseHold[ Map[ ToString[ Unevaluated[#]]&, s]]
	]
execLeft[ args___] := unexpected[ execLeft, {args}]

execRight[ e_Hold] := 
	Module[ {s},
		s = e /. Theorema`Language`VAR$[a_] -> a;
		ReleaseHold[ Map[ ToString[ Unevaluated[#]]&, s]]
	]
execRight[ args___] := unexpected[ execRight, {args}]


End[]

EndPackage[]