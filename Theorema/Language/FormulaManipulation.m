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
(* thinnedExpression *)

thinnedExpression[ e_, drop_List] :=
	Fold[ thinnedExpression, e, drop]
thinnedExpression[ e_, v_] := DeleteCases[ e, _?(!FreeQ[ #, v]&)]
thinnedExpression[ args___] := unexpected[ thinnedExpression, {args}]


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


variables[ (Theorema`Language`RNG$|Theorema`Computation`Language`RNG$)[r___]] := Map[ First, {r}]
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
(* sequenceFree *)


isSequenceFree[ expr_, level_:{1}] := 
	FreeQ[ expr,
		_Theorema`Language`SEQ$|
		_Theorema`Computation`Language`SEQ$|
		Theorema`Language`VAR$[_Theorema`Language`SEQ$]|
		Theorema`Language`Computation`VAR$[_Theorema`Language`Computation`SEQ$], level]
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
		ToExpression[ exec]
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
        With[ { left = execLeft[ Hold[l], var], 
        	cond = makeConjunction[ Prepend[ c, "DUMMY$COND"], Theorema`Computation`Language`And$TM],
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

stripVar[ v:Theorema`Language`VAR$[a_]] := v -> ToExpression[ "VAR$" <> ToString[a]]
stripVar[ args___] := unexpected[ stripVar, {args}]

varToPattern[ v:Theorema`Language`VAR$[a_]] := With[ {new = ToExpression[ "VAR$" <> ToString[a]]}, v :> Apply[ Pattern, {new, Blank[]}]]
varToPattern[ args___] := unexpected[ varToPattern, {args}]

(* ::Subsubsection:: *)
(* defsToRules *)


defsToRules[ defList_List] := Map[ singleDefToRule, defList]
defsToRules[ args___] := unexpected[ defsToRules, {args}]

singleDefToRule[ orig:FML$[ _, form_, __]] :=
	Module[{stripUniv, r},
		stripUniv = stripUniversalQuantifiers[ form];
		r = ruleForm[ stripUniv, orig];
		ToExpression[ r]
	]
singleDefToRule[ args___] := unexpected[ singleDefToRule, {args}]

ruleForm[ {(Theorema`Language`Iff$TM|Theorema`Language`IffDef$TM|Theorema`Language`Equal$TM|Theorema`Language`EqualDef$TM)[ l_, r_], c_List, var_List}, ref_] :=
    Block[ {testMember},
        With[ {left = execLeft[ Hold[l], var], 
               cond = makeConjunction[ Map[ testMember[ $TMAKBatomic, #]&, c], And],
        		(* The complicated DUMMY$DEF... construction is necessary because ref itself contains strings (it's a whole formula incl key, label),
        	   	and we need to get the escaped strings into the Hold *)
               right = execRight[ Hold[r], var]},
            "RuleDelayed[" <> left <> "/;" <> execRight[ Hold[ cond] /. testMember -> MemberQ, var] <> "," <> "Sow[" <> ToString[ ref, InputForm] <> "];" <> right <> "]"
        ]
    ]
ruleForm[ expr_, key_] := $Failed
ruleForm[ args___] := unexpected[ ruleForm, {args}]

(*
	replaceAndTrack[ expr_, repl_List] results in {new, used} where
		new = expr /. repl and
		used is a list of formula keys corresponding to the formulae from which the applied replacements have been derived
*)
replaceAndTrack[ expr_, repl_List] := 
	Module[ {e, used},
		{e, used} = Reap[ expr /. repl];
		If[ used === {},
			{e, used},
			(* else *)
			{e, used[[1]]}
		]
	]
replaceAndTrack[ args___] := unexpected[ replaceAndTrack, {args}]

replaceRecursivelyAndTrack[ expr_, repl_List] := 
	Module[ {e, used},
		{e, used} = Reap[ expr //. repl];
		If[ used === {},
			{e, used},
			(* else *)
			{e, used[[1]]}
		]
	]
replaceRecursivelyAndTrack[ args___] := unexpected[ replaceRecursivelyAndTrack, {args}]


(* ::Section:: *)
(* FML$ datastructure *)

Options[ makeFML] = {key :> defKey[], formula -> True, label :> defLabel[], simplify -> True};

makeFML[ data__?OptionQ] :=
	Module[{k, f, l, s, fs},
		{k, f, l, s} = {key, formula, label, simplify} /. {data} /. Options[ makeFML];
		If[ TrueQ[ s],
			fs = computeInProof[ f],
			fs = f
		];
		makeTmaFml[ k, fs, l, f]
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
		If no FIX$[ v, n] occurs in kb, then n'+1 is -Infinity, we take 0 instead to create the first new constant FIX$[ v, 0]. *)
	Module[{vars = specifiedVariables[ rng], subs},
		subs = Map[ Theorema`Language`VAR$[ #] -> Theorema`Language`FIX$[ #, Max[ Cases[ kb, Theorema`Language`FIX$[ #, n_] -> n, Infinity]] + 1]&, vars] /. -Infinity -> 0;
		{substituteFree[ expr, subs], Map[ Part[ #, 2]&, subs]} 
	]
arbitraryButFixed[ args___] := unexpected[ arbitraryButFixed, {args}]



(* ::Subsection:: *)
(* introduceMeta *)


introduceMeta[ expr_, rng_Theorema`Language`RNG$, kb_List:{}] :=
	(*
		Select all variable symbols from rng, then (for each v of them) find all META$[ v, n, ...] in kb and take the maximal n, say n'.
		A new meta variable then has the form META$[ v, n'+1, c], hence, we substitute all free VAR$[v] by META$[ v, n'+1, c].
		If no META$[ v, n, ...] occurs in kb, then n'+1 is -Infinity, we take 0 instead to create the first new meta variable META$[ v, 0, c]. *)
	Module[{vars = specifiedVariables[ rng], const, subs},
		const = Union[ Cases[ kb, Theorema`Language`FIX$[ #, n_], Infinity]];
		subs = Map[ Theorema`Language`VAR$[ #] -> Theorema`Language`META$[ #, Max[ Cases[ kb, Theorema`Language`META$[ #, n_] -> n, Infinity]] + 1, const]&, vars] /. -Infinity -> 0;
		{substituteFree[ expr, subs], Map[ Part[ #, 2]&, subs]} 
	]
introduceMeta[ args___] := unexpected[ introduceMeta, {args}]



(* ::Subsection:: *)
(* rngToCondition *)


rngToCondition[ Theorema`Language`RNG$[ r__]] := Apply[ Join, Map[ singleRngToCondition, {r}]]
rngToCondition[ args___] := unexpected[ rngToCondition, {args}]

singleRngToCondition[ Theorema`Language`SIMPRNG$[ v_]] := {}
singleRngToCondition[ Theorema`Language`SETRNG$[ v_, S_]] := {Theorema`Language`Element$TM[ v, S]}
singleRngToCondition[ Theorema`Language`STEPRNG$[ v_, l_Integer?NonNegative, h_Integer, 1]] := 
	{Theorema`Language`GreaterEqual$TM[ v, l], Theorema`Language`LessEqual$TM[ v, h], Theorema`Language`Element$TM[ v, Theorema`Language`\[DoubleStruckCapitalN]0$TM]}
singleRngToCondition[ Theorema`Language`STEPRNG$[ v_, l_Integer, h_Integer, 1]] := 
	{Theorema`Language`GreaterEqual$TM[ v, l], Theorema`Language`LessEqual$TM[ v, h], Theorema`Language`Element$TM[ v, Theorema`Language`\[DoubleStruckCapitalZ]$TM]}
singleRngToCondition[ Theorema`Language`STEPRNG$[ v_, l_, h_, s_Integer]] := 
	Module[ {new, step},
		step = If[ s === 1, new, Theorema`Language`Times$TM[ new, s]];
		{Theorema`Language`Exists$TM[ Theorema`Language`RNG$[ Theorema`Language`SETRNG$[ new, Theorema`Language`\[DoubleStruckCapitalN]0$TM]], True, 
			Theorema`Language`And$TM[ Theorema`Language`Equal$TM[ v, Theorema`Language`Plus$TM[ l, step]],
				If[ NonNegative[ s], Theorema`Language`LessEqual$TM, Theorema`Language`GreaterEqual$TM][ v, h]]]}
	]
singleRngToCondition[ Theorema`Language`PREDRNG$[ v_, P_]] := {P[ v]}
singleRngToCondition[ u_] := {$Failed}
singleRngToCondition[ args___] := unexpected[ singleRngToCondition, {args}]


(* ::Section:: *)
(* Computation within proving *)


computeInProof[ expr_] :=
	Module[{simp},
		setComputationContext[ "prove"];
		simp = ToExpression[ StringReplace[ ToString[ expr], "Theorema`Language`" -> "Theorema`Computation`Language`"]];
		setComputationContext[ "none"];
		ToExpression[ StringReplace[ ToString[ simp], "Theorema`Computation`" -> "Theorema`"]]
	]
computeInProof[ args___] := unexpected[ computeInProof, {args}]

(* ::Subsubsection:: *)
(* KB operations *)

joinKB[ kb1:{___FML$}, kb2:{___FML$}] := DeleteDuplicates[ Join[ kb1, kb2], #1.formula === #2.formula&]
joinKB[ args___] := unexpected[ joinKB, {args}]

appendKB[ kb:{___FML$}, fml_FML$] := DeleteDuplicates[ Append[ kb, fml], #1.formula === #2.formula&]
appendKB[ args___] := unexpected[ appendKB, {args}]

prependKB[ kb:{___FML$}, fml_FML$] := DeleteDuplicates[ Prepend[ kb, fml], #1.formula === #2.formula&]
prependKB[ args___] := unexpected[ prependKB, {args}]


End[]

EndPackage[]
