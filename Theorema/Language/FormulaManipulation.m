(* ::Package:: *)

(* Mathematica Package *)

BeginPackage["Theorema`Language`FormulaManipulation`"]

Needs[ "Theorema`Common`"]

Begin["`Private`"]


(* ::Subsubsection:: *)
(* splitAnd *)


(*
	splitAnd[ expr_, v_List] splits a conjunction expr into 1. a conjunction of subexpr with free variables v and 2. the rest 
	splitAnd[ expr_, v_List, False] splits a conjunction expr into 1. a conjunction of subexpr containing the free variables in v and 2. the rest 
*)
splitAnd[ expr:(h:Theorema`Language`And$TM|Theorema`Computation`Language`And$TM|And)[ __], v_List, sub_:True] :=
	Module[ {depSingle = {}, depMulti = {}, p, l, e = simplifiedAnd[ expr], fi, i},
		l = Length[ e];
		Do[
			p = e[[i]];
			fi = freeVariables[ p];
			If[ (sub && fi === v) || (!sub && Intersection[ v, fi] =!= {}), 
				AppendTo[ depSingle, p],
				AppendTo[ depMulti, p]
			],
			{i, l}
		];
		{ makeConjunction[ depSingle, h], makeConjunction[ depMulti, h]}
	]
splitAnd[ expr_, v_List, sub_:True] :=
    Module[ {fi = freeVariables[ expr]},
        If[ (sub && fi === v) || (!sub && Intersection[ v, fi] =!= {}),
            { expr, True},
            { True, expr}
        ]
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
(* simplifiedAnd *)

simplifiedAnd[ True] := True
simplifiedAnd[ h_[ True...]] := True
simplifiedAnd[ h_[ ___, False, ___]] := False

simplifiedAnd[ expr_] :=  
	Module[ {simp = Flatten[ expr //. {True -> Sequence[], (Theorema`Language`And$TM|Theorema`Computation`Language`And$TM)[a_] -> a}]},
		If[ Length[ simp] === 0,
			True,
			(* else *)
			simp
		]
	]
simplifiedAnd[ args___] := unexpected[ simplifiedAnd, {args}]

(* ::Subsubsection:: *)
(* simplifiedOr *)

simplifiedOr[ h_[ False...]] := False
simplifiedOr[ h_[ ___, True, ___]] := True

simplifiedOr[ expr_] :=  
	Module[ {simp = Flatten[ expr //. {False -> Sequence[], (Theorema`Language`Or$TM|Theorema`Computation`Language`Or$TM)[a_] -> a}]},
		If[ Length[ simp] === 0,
			False,
			(* else *)
			simp
		]
	]
simplifiedOr[ args___] := unexpected[ simplifiedOr, {args}]


(* ::Subsubsection:: *)
(* simplifiedImplies *)

simplifiedImplies[ Theorema`Language`Implies$TM[ True, A_]] := A
simplifiedImplies[ Theorema`Language`Implies$TM[ False, _]] := True
simplifiedImplies[ Theorema`Language`Implies$TM[ _, True]] := True
simplifiedImplies[ Theorema`Language`Implies$TM[ A_, Theorema`Language`Implies$TM[ B_, C_]]] := 
	simplifiedImplies[ Theorema`Language`Implies$TM[ simplifiedAnd[ Theorema`Language`And$TM[ A, B]], C]]
simplifiedImplies[ i_Theorema`Language`Implies$TM] := i
simplifiedImplies[ args___] := unexpected[ simplifiedImplies, {args}]

(* ::Subsubsection:: *)
(* simplifiedNot *)

simplifiedNot[ Theorema`Language`Not$TM[ Theorema`Language`Not$TM[ A_]]] := A
simplifiedNot[ Theorema`Language`Not$TM[ Theorema`Language`And$TM[ A__]]] := Apply[ Theorema`Language`Or$TM, Map[ Theorema`Language`Not$TM, {A}]]
simplifiedNot[ Theorema`Language`Not$TM[ Theorema`Language`Or$TM[ A__]]] := Apply[ Theorema`Language`And$TM, Map[ Theorema`Language`Not$TM, {A}]]
simplifiedNot[ Theorema`Language`Not$TM[ Theorema`Language`Implies$TM[ A_, B_]]] := Theorema`Language`And$TM[ A, Theorema`Language`Not$TM[ B]]
simplifiedNot[ Theorema`Language`Not$TM[ Theorema`Language`Iff$TM[ A_, B_]]] := 
	Theorema`Language`Or$TM[ Theorema`Language`And$TM[ A, Theorema`Language`Not$TM[ B]], Theorema`Language`And$TM[ B, Theorema`Language`Not$TM[ A]]]
simplifiedNot[ n_Theorema`Language`Not$TM] := n
simplifiedNot[ args___] := unexpected[ simplifiedNot, {args}]

(* ::Subsubsection:: *)
(* simplifiedForall *)

simplifiedForall[ Theorema`Language`Forall$TM[ Theorema`Language`RNG$[], C_, A_]] := simplifiedImplies[ Theorema`Language`Implies$TM[ C, A]]
simplifiedForall[ f_Theorema`Language`Forall$TM] := f
simplifiedForall[ args___] := unexpected[ simplifiedForall, {args}]


(* ::Subsubsection:: *)
(* standardForm *)

standardFormQuantifier[ Theorema`Language`Forall$TM[ r1_Theorema`Language`RNG$, C1_, Theorema`Language`Forall$TM[ r2_Theorema`Language`RNG$, C2_, body_]]] :=
	standardFormQuantifier[ Theorema`Language`Forall$TM[ Join[ r1, r2], simplifiedAnd[ Theorema`Language`And$TM[ C1, C2]], body]]
standardFormQuantifier[ Theorema`Language`Forall$TM[ r_Theorema`Language`RNG$, C_, body_]] :=
	Theorema`Language`Forall$TM[ r, True, simplifiedImplies[ Theorema`Language`Implies$TM[ C, body]]]
standardFormQuantifier[ f_] := f
standardFormQuantifier[ args___] := unexpected[ standardFormQuantifier, {args}]

(* ::Subsubsection:: *)
(* thinnedExpression *)

thinnedExpression[ e_, drop_List] :=
	Fold[ thinnedExpression, e, drop]
thinnedExpression[ e_, v_] := DeleteCases[ e, _?(!FreeQ[ #, v]&)]
thinnedExpression[ args___] := unexpected[ thinnedExpression, {args}]


(* ::Subsubsection:: *)
(* freeVariables *)


freeVariables[ q_[ r:(Theorema`Language`RNG$|Theorema`Computation`Language`RNG$)[x__], cond_, expr_]] := 
	Complement[ freeVariables[ {x, cond, expr}], rngVariables[ r]]
freeVariables[ Hold[ l___]] := freeVariables[ {l}]
freeVariables[ l_List] := Apply[ Union, Map[ freeVariables, l]]
freeVariables[ f_[x___]] := freeVariables[ {f, x}]
freeVariables[ v:(Theorema`Language`VAR$|Theorema`Computation`Language`VAR$)[_]] := {v}
freeVariables[ c_] := {}
freeVariables[ args___] := unexpected[ freeVariables, {args}]


(* ::Subsubsection:: *)
(* rngVariables *)

rngVariables[ (Theorema`Language`RNG$|Theorema`Computation`Language`RNG$)[r___]] := Map[ First, {r}]
rngVariables[ args___] := unexpected[ rngVariables, {args}]

(* ::Subsubsection:: *)
(* rngConstants *)

rngConstants[ (Theorema`Language`RNG$|Theorema`Computation`Language`RNG$)[r___]] := Map[ First, {r}]
rngConstants[ args___] := unexpected[ rngConstants, {args}]


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
	Module[ {qvars = rngVariables[ r], vars},
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
substituteFree[ expr_, rule_?OptionQ] := substituteFree[ expr, {rule}]
substituteFree[ expr_, rules_List] := ReleaseHold[ substituteFree[ Hold[ expr], rules]]
substituteFree[ args___] := unexpected[ substituteFree, {args}]

(* ::Subsubsection:: *)
(* isQuantifierFree *)

isQuantifierFree[ expr_] :=
	FreeQ[ expr,
		_Theorema`Language`RNG$|
		_Theorema`Computation`Language`RNG$]
isQuantifierFree[ args___] := unexpected[ isQuantifierFree, {args}]

(* ::Subsubsection:: *)
(* isLogQuantifierFree *)

isLogQuantifierFree[ expr_] := FreeQ[ expr, _Theorema`Language`Forall$TM|_Theorema`Language`Exists$TM]
isLogQuantifierFree[ args___] := unexpected[ isLogQuantifierFree, {args}]

(* ::Subsubsection:: *)
(* sequenceFree *)

isSequenceFree[ expr_, level_:{1}] := 
	FreeQ[ expr,
		_Theorema`Language`SEQ0$|
		_Theorema`Computation`Language`SEQ0$|
		Theorema`Language`VAR$[_Theorema`Language`SEQ0$]|
		Theorema`Language`Computation`VAR$[_Theorema`Language`Computation`SEQ0$]|
		_Theorema`Language`SEQ1$|
		_Theorema`Computation`Language`SEQ1$|
		Theorema`Language`VAR$[_Theorema`Language`SEQ1$]|
		Theorema`Language`Computation`VAR$[_Theorema`Language`Computation`SEQ1$], level]
isSequenceFree[ args___] := unexpected[ isSequenceFree, {args}]

(* ::Subsubsection:: *)
(* variableFree *)

isVariableFree[ expr_, level_:{1}] := 
	FreeQ[ expr,
		_Theorema`Language`VAR$|_Theorema`Computation`Language`VAR$, level]
isVariableFree[ args___] := unexpected[ isVariableFree, {args}]

(* ::Subsubsection:: *)
(* transferToComputation *)

transferToComputation[ form_, key_] :=
	Module[{stripUniv, exec},
		stripUniv = stripUniversalQuantifiers[ form];
		exec = executableForm[ stripUniv, key];
		(* Certain equalities cannot be made executable and generate an error when translated to Mma. 
		   Since this operation is part of the preprocesing, we catch the error,
		   otherwise preprocessing would end in a premature state. *)
		Quiet[ Check[ ToExpression[ exec], Null], {SetDelayed::nosym}]
	]
transferToComputation[ args___] := unexpected[ transferToComputation, {args}]

(*
	stripUniversalQuantifiers[ form] transforms form into a list {f, c, v}, where
		f is the innermost formula being neither a universal quantified formula nor an implication
		c is a list of conditions being applicable to f
		v is a list of universally quantified variables contained in f 
*)
stripUniversalQuantifiers[ Theorema`Language`Forall$TM[ r_, c_, f_]] :=
	Module[ {rc, vars, cond, inner},
		rc = rngToCondition[ r];
		{inner, cond, vars} = stripUniversalQuantifiers[ f];
		cond = Join[ rc, cond];
		{inner, If[ !TrueQ[ c], joinConditions[ cond, c], cond], Join[ rngVariables[ r], vars]}
	]
stripUniversalQuantifiers[ Theorema`Language`Implies$TM[ l_, r_]] :=
	Module[ {vars, cond, inner},
		{inner, cond, vars} = stripUniversalQuantifiers[ r];
		{inner, joinConditions[ cond, l], vars}
	]
stripUniversalQuantifiers[ expr_] := {expr, {}, {}}
stripUniversalQuantifiers[ args___] := unexpected[ stripUniversalQuantifiers, {args}]

joinConditions[ c_List, newCond_Theorema`Language`And$TM] := Join[ Apply[ List, simplifiedAnd[ newCond]], c]
joinConditions[ c_List, newCond_] := Prepend[ c, newCond]
joinConditions[ args___] := unexpected[ joinConditions, {args}]

(*
was used in stripUniversalQuantifiers: turned out that rngToCondition does the same.


rangeToCondition[ Theorema`Language`RNG$[ rng__]] := Map[ singleRangeToCondition, {rng}]
rangeToCondition[ args___] := unexpected[ rangeToCondition, {args}]

singleRangeToCondition[ Theorema`Language`SETRNG$[ x_, A_]] := Theorema`Language`Element$TM[ x, A]
singleRangeToCondition[ Theorema`Language`PREDRNG$[ x_, P_]] := P[ x]
singleRangeToCondition[ Theorema`Language`STEPRNG$[ x_, l_, h_, 1]] := 
	Theorema`Language`And$TM[ Theorema`Language`isInteger$TM[x], Theorema`Language`LessEqual$TM[ l, x], Theorema`Language`LessEqual$TM[ x, h]]
singleRangeToCondition[ _] := Sequence[]
singleRangeToCondition[ args___] := unexpected[ singleRangeToCondition, {args}]
*)

executableForm[ {(Theorema`Language`Iff$TM|Theorema`Language`IffDef$TM|Theorema`Language`Equal$TM|Theorema`Language`EqualDef$TM)[ l_, r_], c_List, var_List}, key_] :=
    Block[ { $ContextPath = {"System`"}, $Context = "Global`"},
        With[ { left = execLeft[ Hold[l], var], 
        	cond = makeConjunction[ Prepend[ c, "DUMMY$COND"], And],
        	right = execRight[ Hold[r], var]},
        	(* The complicated DUMMY$COND... construction is necessary because the key itself contains strings,
        	   and we need to get the escaped strings into the Hold *)
            StringReplace[ left <> "/;" <> execRight[ Hold[ cond], var] <> ":=" <> right,
            	{ "DUMMY$COND" -> "Theorema`Common`kbSelectCompute[" <> ToString[ key, InputForm] <> "]",
            		"Theorema`Language`" -> "Theorema`Computation`Language`",
            		"Theorema`Knowledge`" -> "Theorema`Computation`Knowledge`"}
            ]
        ]
    ]
(* We return a string "$Failed", because when returning the expression $Failed (or also Null) the 
   ToExpression[...] in the calling transferToComputation calls openEnvironment once more (which means that $PreRead
   seems to be applied ???), resulting in messing up the contexts. With the string "$Failed" this
   does not happen *)
executableForm[ expr_, key_] := "$Failed"
executableForm[ args___] := unexpected[ executableForm, {args}]

execLeft[ e_Hold, var_List] := 
	Module[ {s},
		s = substituteFree[ e, Map[ varToPattern, var]];
		ReleaseHold[ Map[ ToString[ Unevaluated[#]]&, s]]
	]
execLeft[ args___] := unexpected[ execLeft, {args}]

execRight[ e_Hold, var_List] := 
	Module[ {s},
		s = substituteFree[ e, Map[ stripVar, var]] /. {Theorema`Language`Assign$TM -> Set,
			Theorema`Language`SetDelayed$TM -> SetDelayed, 
			Theorema`Language`CompoundExpression$TM -> CompoundExpression};
		ReleaseHold[ Map[ Function[ expr, ToString[ Unevaluated[ expr]], {HoldAll}], s]]
	]
execRight[ args___] := unexpected[ execRight, {args}]

stripVar[ v:Theorema`Language`VAR$[Theorema`Language`SEQ0$[a_]]] := v -> ToExpression[ "SEQ0$" <> ToString[a]]
stripVar[ v:Theorema`Language`VAR$[Theorema`Language`SEQ1$[a_]]] := v -> ToExpression[ "SEQ1$" <> ToString[a]]
stripVar[ v:Theorema`Language`VAR$[a_]] := v -> ToExpression[ "VAR$" <> ToString[a]]
stripVar[ args___] := unexpected[ stripVar, {args}]

varToPattern[ v:Theorema`Language`VAR$[Theorema`Language`SEQ0$[a_]]] := With[ {new = ToExpression[ "SEQ0$" <> ToString[a]]}, v :> Apply[ Pattern, {new, BlankNullSequence[]}]]
varToPattern[ v:Theorema`Language`VAR$[Theorema`Language`SEQ1$[a_]]] := With[ {new = ToExpression[ "SEQ1$" <> ToString[a]]}, v :> Apply[ Pattern, {new, BlankSequence[]}]]
varToPattern[ v:Theorema`Language`VAR$[a_]] := With[ {new = ToExpression[ "VAR$" <> ToString[a]]}, v :> Apply[ Pattern, {new, Blank[]}]]
varToPattern[ args___] := unexpected[ varToPattern, {args}]

(* ::Subsubsection:: *)
(* formulaListToRules *)

(*
	formulaListToRules[ l_List] converts l into a list {f, b, e}, where 
	f is a list of forward rewrite rules (for rewriting the kb) and
	b is a list of backward rewrite rules (for rewriting the goal).
	e is a list of elementary substitution.
*)
formulaListToRules[ l_List] := MapThread[ Join, Map[ formulaToRules, l]]
formulaListToRules[ args___] := unexpected[ formulaListToRules, {args}]


(* ::Subsubsection:: *)
(* formulaToRules *)

(*
	Convert a formula to a list of reasonable rewrite rules.
*)
formulaToRules[ orig:FML$[ _, form_, __]] :=
	Module[{stripUniv, ruleList},
		stripUniv = stripUniversalQuantifiers[ form];
		ruleList = makeRules[ stripUniv, orig]
	]
formulaToRules[ args___] := unexpected[ formulaToRules, {args}]

(*
	We expect the list at pos. 1 to be the result of stripUniversalQuantifiers, i.e. all universal quantifiers are stripped, implications are processed.
	It is of the form {form, c, var}, where form is neither forall nor implies, c is a list of conditions, and var is a list of (universally quantified) variables.
	Result is a list of forward rules, a list of backward rules, and a list of elementary substitutions and/or definition rules.
*)
makeRules[ {(Theorema`Language`IffDef$TM|Theorema`Language`EqualDef$TM)[ l_, r_], c_List, var_List}, ref_] := 
	{{}, {}, {makeSingleRule[ {l, r, c, var}, ref]}}
makeRules[ {Theorema`Language`Iff$TM[ l_, r_], c_List, var_List}, ref_] := 
	MapThread[ Join, {makeRules[ {r, joinConditions[ c, l], var}, ref], makeRules[ {l, joinConditions[ c, r], var}, ref]}]
(* Special case equality: we can rewrite left to right and right to left, but we can also rewrite the equality as a whole. *)
makeRules[ {form:Theorema`Language`Equal$TM[ l_, r_], c_List, var_List}, ref_] :=
    Module[ {forward = MapIndexed[ makeSingleRule[ {#1, form, Drop[ c, #2], var}, ref]&, c], backward = {}},
        If[ c =!= {},
        	(* in this case, forward is also empty, we need not do anything *)
            backward = {makeSingleRule[ {form, makeConjunction[ c, Theorema`Language`And$TM], {}, var}, ref, "backward"]}
        ];
        {forward, backward, {makeSingleRule[ {l, r, c, var}, ref], makeSingleRule[ {r, l, c, var}, ref]}}
    ]
(* We do not introduce backward rules for the negated implications *)
makeRules[ {form:Theorema`Language`And$TM[ f__], c:{__}, var_List}, ref_] := 
	{Join[ 
		MapIndexed[ makeSingleRule[ {#1, form, Drop[ c, #2], var}, ref]&, c],
		Map[ makeSingleRule[ 
				{simplifiedNot[ Theorema`Language`Not$TM[ #]], makeDisjunction[ Map[ simplifiedNot[ Theorema`Language`Not$TM[ #]]&, c], Theorema`Language`Or$TM], {}, var}, 
				ref]&, {f}]
	], 
	Map[ makeSingleRule[ {#, makeConjunction[ c, Theorema`Language`And$TM], {}, var}, ref, "backward"]&, {f}],
	{}}
makeRules[ {form_, c:{__}, var_List}, ref_] := 
	{Append[
		MapIndexed[ makeSingleRule[ {#1, form, Drop[ c, #2], var}, ref]&, c],
		makeSingleRule[ {simplifiedNot[ Theorema`Language`Not$TM[ form]], makeDisjunction[ Map[ simplifiedNot[ Theorema`Language`Not$TM[ #]]&, c], Theorema`Language`Or$TM], {}, var}, ref]
	], 
	{makeSingleRule[ {form, makeConjunction[ c, Theorema`Language`And$TM], {}, var}, ref, "backward"]},
	{}}
makeRules[ {form_, c_List, var_List}, ref_] := {{}, {}, {}}
makeRules[ args___] := unexpected[ makeRules, {args}]

(*
	A "rewrite rule" is stored as {key, r}, where
	key ... is the key of the formula from which the rule has been derived,
	r   ... is the actual rule lhs:>rhs.
	
	We can use the key to filter rules before applying them to a formula with that key.
*)
(* Do not rewrite numbers and logical combinations *)
makeSingleRule[ {l_?NumberQ, r_, c_List, var_List}, ref_] := Sequence[]
makeSingleRule[ {_Theorema`Language`And$TM|_Theorema`Language`Or$TM|_Theorema`Language`Implies$TM|_Theorema`Language`Iff$TM, r_, c_List, var_List}, ref_] := Sequence[]
makeSingleRule[ {_Theorema`Language`Forall$TM|_Theorema`Language`Exists$TM, r_, c_List, var_List}, ref_] := Sequence[]
(* If the free variables left/right do not coincide, then do not generate a rewrite rule *)
makeSingleRule[ {l_, r_, c_List, var_List}, ref_] /; With[ {fr = freeVariables[ Append[ c, r]], fl = freeVariables[ l]}, Complement[ fr, fl] =!= {} || Complement[ fl, var] =!= {}] := 
	Sequence[]
	
makeSingleRule[ all:{l_, r_, c_List, var_List}, ref_] := {ref.key, mmaTransRule[ all, ref]}

(*
	For backward rules we allow to introduce an existential quantifier if additional free variables occur.
	The corresponding thing for forward rules is not done by rewriting, it should be achieved by instantiation.
*)
makeSingleRule[ {l_, r_, {}, var_List}, ref_, "backward"] := 
	Module[ {addVars = Complement[ freeVariables[ r], freeVariables[ l]], newF},
		If[ addVars === {},
			newF = r,
			(* else *)
			newF = Theorema`Language`Exists$TM[ Apply[ Theorema`Language`RNG$, Map[ Theorema`Language`SIMPRNG$, addVars]], True, r]
		];
		makeSingleRule[ {l, newF, {}, var}, ref]
	]
makeSingleRule[ {l_, r_, c_List, var_List}, ref_, "backward"] := 
	makeSingleRule[ { l, makeConjunction[ Append[ c, r], Theorema`Language`And$TM], {}, var}, ref, "backward"]

makeSingleRule[ args___] := unexpected[ makeSingleRule, {args}]

mmaTransRule[ {l_, r_, c_List, var_List}, ref_] :=
(*
	mmaTransRule[ {left, right, cond, var}, ref] translates left/right into a rewrite rule.
	cond, var are assumed to be come from 'stripUniversalQuantifiers' translating a universally quantified equality/equivalence into
	eq ... the pure equality/equivalence,
	cond ... the conditions on the variables contained in eq, and
	var ... the variables contained in eq.
	ref is the original (universally quantified) equality/equivalence formula. 
	When the resulting rewrite rule is applied, it will Sow[ref, "ref"] and Sow[cond, "cond"], which must be caught by an appropriate Reap, 
	see replace...AndTrack.
*)
    With[ {left = execLeft[ Hold[l], var], 
               cond = makeConjunction[ c, Theorema`Language`And$TM],
               right = execRight[ Hold[r], var]},
            ToExpression[ 
            	"RuleDelayed[" <> left <> "," <> 
            	"Sow[" <> ToString[ ref, InputForm] <> ",\"ref\"]; Sow[" <> execRight[ Hold[ cond], var] <> ",\"cond\"];" <> right <> "]"
            ]
        ]
        
mmaTransRule[ args___] := unexpected[ mmaTransRule, {args}]


(* ::Subsubsection:: *)
(* replace...AndTrack *)

(*
	All these functions return a list {e, form, cond}, where
	e is the resulting expression after replacement,
	form is a list of formulas used for replacement, i.e. the formulas from which the rewrite rules have been derived,
	cond is a condition, under which the replacement is allowed.
*)
replaceAndTrack[ expr:_Theorema`Language`VAR$|_Theorema`Language`SEQ$|_Theorema`Language`FIX$, _List] := {expr, {}, True}

replaceAndTrack[ expr_, repl_List] :=
	Module[ {e, uc},
		{e, uc} = Reap[ Replace[ expr, repl], {"ref", "cond"}];
		If[ uc === {{}, {}},
			{e, {}, True},
			(* else *)
			{e, uc[[1,1]], simplifiedAnd[ makeConjunction[ uc[[2,1]], Theorema`Language`And$TM]]}
		]
	]
replaceAndTrack[ args___] := unexpected[ replaceAndTrack, {args}]

replaceListAndTrack[ expr_, repl_List] := 
	Module[ {all},
		all = DeleteCases[ Map[ replaceAndTrack[ expr, {#}]&, repl], {expr, _, _}];
		If[ all === {},
			{{}, {}, {}},
			Transpose[ all]
		]
	]
replaceListAndTrack[ args___] := unexpected[ replaceListAndTrack, {args}]

replaceAllAndTrack[ expr_, repl_List] := 
	Module[ {e, uc},
		{e, uc} = Reap[ replaceAllExcept[ expr, repl, {}, Heads -> {Theorema`Language`VAR$, Theorema`Language`SEQ$, Theorema`Language`FIX$}], {"ref", "cond"}];
		If[ uc === {{}, {}},
			{e, {}, True},
			(* else *)
			{e, uc[[1,1]], simplifiedAnd[ makeConjunction[ uc[[2,1]], Theorema`Language`And$TM]]}
		]
	]
replaceAllAndTrack[ args___] := unexpected[ replaceAllAndTrack, {args}]

replaceRepeatedAndTrack[ expr_, repl_List] := 
(* We take care that no infinite rewritings occur using "MaxIterations" *)
	Module[ {e, uc},
		{e, uc} = Reap[ 
			Quiet[ replaceRepeatedExcept[expr, repl, {}, Heads -> {Theorema`Language`VAR$, Theorema`Language`SEQ$, Theorema`Language`FIX$}, MaxIterations -> 5], 
					ReplaceRepeated::rrlim],
				{"ref", "cond"}];
		If[ uc === {{}, {}},
			{e, {}, True},
			(* else *)
			{e, uc[[1,1]], simplifiedAnd[ makeConjunction[ uc[[2,1]], Theorema`Language`And$TM]]}
		]
	]
replaceRepeatedAndTrack[ args___] := unexpected[ replaceRepeatedAndTrack, {args}]

(* ::Subsubsection:: *)
(* filterRules *)

(*
	rules is a list of rewrite rules of the form {k, l:>r} as generated by makeSingleRule above.
	key is the key of the formula, to which the rules are intended to be applied.
	filterRules[ rules_List, key_] filters rules and returns the plain Mathematica rewrite rules that are applicable to the formula with key 'key'.
		It deletes rules where k=key because they are derived from the formula to which they should now be applied.
	filterRules[ rules_List, keyList_] deletes rules with k in the keyList. It returns a list of rules of the form {k, l:>r}, not the plain Mma rules.
*)
filterRules[ rules_List, key:{_, _}] := Cases[ rules, {Except[ key], r_} -> r]
filterRules[ rules_List, {keys:{_, _}..}] := DeleteCases[ rules, Alternatives[ keys]]
filterRules[ args___] := unexpected[ filterRules, {args}]


(* ::Section:: *)
(* FML$ datastructure *)

Options[ makeFML] = {key :> defKey[], formula -> True, label :> defLabel[], simplify -> True};

makeFML[ data___?OptionQ] :=
	Module[{k, f, l, s, fs},
		{k, f, l, s} = {key, formula, label, simplify} /. {data} /. Options[ makeFML];
		If[ TrueQ[ s],
			fs = computeInProof[ f],
			fs = f
		];
		makeTmaFml[ k, standardFormQuantifier[ fs], l, f]
	]
makeFML[ args___] := unexpected[ makeFML, {args}]

makeTmaFml[ key_List, fml_, label_String, fml_] := FML$[ key, fml, label]
makeTmaFml[ key_List, fmlSimp_, label_String, fml_] := FML$[ key, fmlSimp, label, "origForm" -> fml]
makeTmaFml[ args___] := unexpected[ makeTmaFml, {args}]

defKey[ ] := {"ID" <> $cellTagKeySeparator <> ToString[ Unique[ "formula"]], "Source" <> $cellTagKeySeparator <> "none"}
defKey[ args___] := unexpected[ defKey, {args}]

defLabel[ ] := ToString[ $formulaLabel++]
defLabel[ args___] := unexpected[ defLabel, {args}]

initFormulaLabel[ ] := $formulaLabel = 1;
initFormulaLabel[ args___] := unexpected[ initFormulaLabel, {args}]

FML$ /: Dot[ FML$[ k_, _, __], key] := k
FML$ /: Dot[ FML$[ _, fml_, __], formula] := fml
FML$ /: Dot[ FML$[ _, _, l_, ___], label] := l
FML$ /: Dot[ FML$[ k_, _, __], id] := k[[1]]
FML$ /: Dot[ FML$[ k_, _, __], source] := k[[2]]
FML$ /: Dot[ FML$[ _, _, _, ___, (Rule|RuleDelayed)[ key_String, val_], ___], key_] := val
FML$ /: Dot[ FML$[ _, _, _, ___], key_String] := {}
FML$ /: Dot[ f_FML$, s___] := unexpected[ Dot, {f, s}]

formulaReference[ fml_FML$] :=
    With[ { tag = fml.id, labelDisp = makeLabel[ fml.label], fmlDisp = theoremaDisplay[ fml.formula]},
        Cell[ BoxData[ ToBoxes[
            Button[ Tooltip[ Mouseover[ Style[ labelDisp, "FormReference"], Style[ labelDisp, "FormReferenceHover"]], fmlDisp],
               NotebookLocate[ tag], Appearance->None]
        ]]]
       ]
formulaReference[ args___] := unexpected[ formulaReference, {args}]


(* ::Section:: *)
(* ranges *)


(* ::Subsection:: *)
(* arbitraryButFixed *)


arbitraryButFixed[ expr_, rng_Theorema`Language`RNG$, kb_List:{}] :=
	(*
		Select all variable symbols from rng, then (for each v of them) find all FIX$[ v, n] constants in kb and take the maximal n, say n'.
		A new constant then has the form FIX$[ v, n'+1], hence, we substitute all free VAR$[v] by FIX$[ v, n'+1].
		If no FIX$[ v, n] occurs in kb, then n'+1 is -Infinity, we take 0 instead to create the first new constant FIX$[ v, 0]. 
		We return the expression with variables substituted by abf constants and a range expression expressing the ranges,
		from which the constants have been derived. 
	*)
	Module[{vars = specifiedVariables[ rng], subs},
		subs = Map[ Theorema`Language`VAR$[ #] -> Theorema`Language`FIX$[ #, Max[ Cases[ kb, Theorema`Language`FIX$[ #, n_] -> n, Infinity]] + 1]&, vars] /. -Infinity -> 0;
		{substituteFree[ expr, subs], rng /. subs} 
	]
arbitraryButFixed[ args___] := unexpected[ arbitraryButFixed, {args}]



(* ::Subsection:: *)
(* introduceMeta *)


introduceMeta[ expr_, rng_Theorema`Language`RNG$, forms_List:{}] :=
	(*
		Select all variable symbols from rng, then (for each v of them) find all META$[ v, n, ...] in kb and take the maximal n, say n'.
		A new meta variable then has the form META$[ v, n'+1, c], hence, we substitute all free VAR$[v] by META$[ v, n'+1, c].
		If no META$[ v, n, ...] occurs in kb, then n'+1 is -Infinity, we take 0 instead to create the first new meta variable META$[ v, 0, c]. *)
	Module[{vars = specifiedVariables[ rng], const, subs},
		const = Union[ Cases[ forms, _Theorema`Language`FIX$, Infinity]];
		subs = Map[ Theorema`Language`VAR$[ #] -> Theorema`Language`META$[ #, Max[ Cases[ forms, Theorema`Language`META$[ #, n_] -> n, Infinity]] + 1, const]&, vars] /. -Infinity -> 0;
		{substituteFree[ expr, subs], Map[ Part[ #, 2]&, subs]} 
	]
introduceMeta[ args___] := unexpected[ introduceMeta, {args}]


(* ::Subsection:: *)
(* instantiateExistGoalInteractive *)

instantiateExistGoalInteractive[ g:FML$[ _, Theorema`Language`Exists$TM[ rng_, __], ___], const_List, K_List] :=
	Module[{vars = rngVariables[ rng], inst, nn},
		inst = getExistGoalInstanceDialog[ vars, const, {g, K}];
		If[ inst === $Failed,
			Return[ $Failed],
			(* else *)
			nn = Position[ inst, Except[ Null], {1}, Heads -> False];
			(* Ignore Null in inst, these come from empty input fields -> these vars should not be instantiated *)
			inst = Map[ makeTmaExpression, Extract[ inst, nn]];
			Thread[ Extract[ vars, nn] -> inst]
		]
	]
instantiateExistGoalInteractive[ args___] := unexpected[ instantiateExistGoalInteractive, {args}]


(* ::Subsection:: *)
(* instantiateUnivKnowInteractive *)

instantiateUnivKnowInteractive[ K_List] :=
	Module[{},
		K
	]
instantiateUnivKnowInteractive[ args___] := unexpected[ instantiateUnivKnowInteractive, {args}]



(* ::Subsection:: *)
(* rngToCondition *)

(*
	rngToCondition[ r] converts the range r into a LIST of conditions.
*)
rngToCondition[ Theorema`Language`RNG$[ r__]] := Apply[ Join, Map[ singleRngToCondition, {r}]]
rngToCondition[ args___] := unexpected[ rngToCondition, {args}]

singleRngToCondition[ Theorema`Language`SIMPRNG$[ v_]] := {}
singleRngToCondition[ Theorema`Language`SETRNG$[ v_, S_]] := {Theorema`Language`Element$TM[ v, S]}
singleRngToCondition[ Theorema`Language`STEPRNG$[ v_, l_Integer?NonNegative, h_Integer, 1]] := 
	{Theorema`Language`GreaterEqual$TM[ v, l], Theorema`Language`LessEqual$TM[ v, h], Theorema`Language`Element$TM[ v, Theorema`Language`IntegerRange$TM[ 0, Infinity, True, False]]}
singleRngToCondition[ Theorema`Language`STEPRNG$[ v_, l_Integer, h_Integer, 1]] := 
	{Theorema`Language`GreaterEqual$TM[ v, l], Theorema`Language`LessEqual$TM[ v, h], Theorema`Language`Element$TM[ v, Theorema`Language`IntegerRange$TM[ -Infinity, Infinity, False, False]]}
singleRngToCondition[ Theorema`Language`STEPRNG$[ v_, l_, h_, s_Integer]] := 
	Module[ {new, step},
		step = If[ s === 1, new, Theorema`Language`Times$TM[ new, s]];
		{Theorema`Language`Exists$TM[ Theorema`Language`RNG$[ Theorema`Language`SETRNG$[ new, Theorema`Language`IntegerRange$TM[ 0, Infinity, True, False]]], True, 
			Theorema`Language`And$TM[ Theorema`Language`Equal$TM[ v, Theorema`Language`Plus$TM[ l, step]],
				If[ NonNegative[ s], Theorema`Language`LessEqual$TM, Theorema`Language`GreaterEqual$TM][ v, h]]]}
	]
singleRngToCondition[ Theorema`Language`PREDRNG$[ v_, P_]] := {P[ v]}
singleRngToCondition[ u_] := {$Failed}
singleRngToCondition[ args___] := unexpected[ singleRngToCondition, {args}]


(* ::Subsubsection:: *)
(* KB operations *)

(*
	The kb operations put the rewrite rules for appropriate formulas into a global variable. When we
	create a new proof sit (makePRFSIT) we put what has accumulated into the approriate places.
*)

(*
	joinKB can only join 2 KBs.
	kb1 are new formula, where we need to check for rewrite rules and duplicates.
	kb2 contains no duplicates and rewrite rules have already been generated.
*)
joinKB[ kb1:{___FML$}, kb2:{___FML$}] := Fold[ prependKB, kb2, Reverse[ kb1]]
joinKB[ args___] := unexpected[ joinKB, {args}]

appendKB[ kb:{___FML$}, fml_FML$] := 
	Module[ {member, trimmed},
		member = Catch[ Scan[ If[fml.formula === #.formula, Throw[ True]]&, kb]; False];
		If[ member,
			(* fml is already in kb, we leave kb unchanged *)
			kb,
			(* else *)
			trimmed = trimFormulaForRewriting[ fml];
			(* put rewrite rules to global variable, even if all are empty *)
			AppendTo[ $rewriteRules, Rest[ trimmed]];
			(* First[ trimmed] can be empty or {fml}, in either case Join does the right thing *)
			Join[ kb, First[ trimmed]]
		]
	]
appendKB[ args___] := unexpected[ appendKB, {args}]

prependKB[ kb:{___FML$}, fml_FML$] := 
	Module[ {member, trimmed},
		member = Catch[ Scan[ If[fml.formula === #.formula, Throw[ True]]&, kb]; False];
		If[ member,
			(* fml is already in kb, we leave kb unchanged *)
			kb,
			(* else *)
			trimmed = trimFormulaForRewriting[ fml];
			(* put rewrite rules to global variable, even if all are empty *)
			AppendTo[ $rewriteRules, Rest[ trimmed]];
			(* First[ trimmed] can be empty or {fml}, in either case Join does the right thing *)
			Join[ First[ trimmed], kb]
		]
	]
prependKB[ args___] := unexpected[ prependKB, {args}]

SetAttributes[ appendToKB, HoldFirst]
appendToKB[ kb_, fml_FML$] := (kb = appendKB[ kb, fml])
appendToKB[ args___] := unexpected[ appendToKB, {args}]

SetAttributes[ prependToKB, HoldFirst]
prependToKB[ kb_, fml_FML$] := (kb = prependKB[ kb, fml])
prependToKB[ args___] := unexpected[ prependToKB, {args}]

trimKBforRewriting[ k_List] :=
	Module[{sRules = {}, dRules = {}, kbRules = {}, goalRules = {}, thinnedKB = {}},
		Do[
        	{thinnedKB, kbRules, goalRules, sRules, dRules} = 
        		MapThread[ Join, {{thinnedKB, kbRules, goalRules, sRules, dRules}, trimFormulaForRewriting[ k[[i]]]}];
        	,
        	{i, Length[k]}
        ];
        {thinnedKB, kbRules, goalRules, sRules, dRules}
	]
trimKBforRewriting[ args___] := unexpected[ trimKBforRewriting, {args}]


trimFormulaForRewriting[ form_FML$] :=
    Module[ {sRules = {}, dRules = {}, kbRules = {}, goalRules = {}, kbForm = {}},
        Switch[ form,
            FML$[ _, (Theorema`Language`EqualDef$TM|Theorema`Language`Equal$TM)[ lhs_, rhs_], __]|FML$[ _, (Theorema`Language`IffDef$TM|Theorema`Language`Iff$TM)[ lhs_?isLogQuantifierFree, rhs_?isLogQuantifierFree], __],
            (* these are substitutions that we want to perform immediately -> elemSubstRules 
               subst coming from equalities are in pos 3, equivalences produce identical forward and backward rules, hence we take only the forward in pos 1
               and join them *)
            sRules = Apply[ Join, Delete[ formulaToRules[ form], 2]],
            FML$[ _, _?(!FreeQ[ #, _Theorema`Language`IffDef$TM|_Theorema`Language`EqualDef$TM]&), __],
            (* definition rules come in pos 3 *)
            dRules = formulaToRules[ form][[3]],
            _,
            {kbRules, goalRules, sRules} = formulaToRules[ form];
            AppendTo[ kbForm, form]
            ];
        {kbForm, kbRules, goalRules, sRules, dRules}
    ]
trimFormulaForRewriting[ args___] := unexpected[ trimFormulaForRewriting, {args}]


End[]

EndPackage[]
