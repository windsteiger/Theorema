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
	Complement[ freeVariables[ {x, cond, expr}], specifiedVariables[ r]]
freeVariables[ Hold[ l___]] := freeVariables[ {l}]
freeVariables[ l_List] := Apply[ Union, Map[ freeVariables, l]]
freeVariables[ f_[x___]] := freeVariables[ {f, x}]
freeVariables[ v:(Theorema`Language`VAR$|Theorema`Computation`Language`VAR$)[_]] := {v}
freeVariables[ c_] := {}
freeVariables[ args___] := unexpected[ freeVariables, {args}]


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
	Module[ {qvars = Map[ #[[1]]&, {rng}], vars},
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


End[]

EndPackage[]