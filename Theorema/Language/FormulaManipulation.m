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
substituteFree[ expr_, rule_Rule] := substituteFree[ expr, {rule}]
substituteFree[ expr_, rules_List] := ReleaseHold[ substituteFree[ Hold[ expr], rules]]
substituteFree[ args___] := unexpected[ substituteFree, {args}]


(* ::Subsubsection:: *)
(* sequenceFree *)

isSequenceFree[ expr_] := 
	FreeQ[ expr,
		_Theorema`Language`SEQ$|
		_Theorema`Computation`Language`SEQ$|
		Theorema`Language`VAR$[_Theorema`Language`SEQ$]|
		Theorema`Language`Computation`VAR$[_Theorema`Language`Computation`SEQ$], {1}]
isSequenceFree[ args___] := unexpected[ isSequenceFree, {args}]

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
		v is a list of variables contained in f 
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
        With[ { left = execLeft[ Hold[l]], 
        	cond = makeConjunction[ Prepend[ c, "DUMMY$COND"], Theorema`Computation`Language`And$TM],
        	right = execRight[ Hold[r]]},
        	(* The complicated DUMMY$COND... construction is necessary because the key itself contains strings,
        	   and we need to get the escaped strings into the Hold *)
            StringReplace[ left <> "/;" <> execRight[ Hold[ cond]] <> ":=" <> right,
            	{ "DUMMY$COND" -> "Theorema`Computation`Language`Private`activeComputationKB[" <> ToString[ key, InputForm] <> "]",
            		"Theorema`Language`" -> "Theorema`Computation`Language`",
            		"Theorema`Knowledge`" -> "Theorema`Computation`Knowledge`"}
            ]
        ]
    ]
(* We return a string "$Failed", because when returning the expression $Failed (or also Null) the 
   ToExpression[...] in the calling transferToComputation calls openEnvironment once more (which means that $PreRead
   seems to be applied???), resulting in messing up the contexts. With the string "$Failed" this
   does not happen *)
executableForm[ expr_, key_] := "$Failed"
executableForm[ args___] := unexpected[ executableForm, {args}]

execLeft[ e_Hold] := 
	Module[ {s},
		s = e /. Theorema`Language`VAR$[a_] :> Apply[ Pattern, {a, Blank[]}];
		ReleaseHold[ Map[ ToString[ Unevaluated[#]]&, s]]
	]
execLeft[ args___] := unexpected[ execLeft, {args}]

execRight[ e_Hold] := 
	Module[ {s},
		s = e /. {Theorema`Language`Assign$TM -> Set,
			Theorema`Language`SetDelayed$TM -> SetDelayed, 
			Theorema`Language`CompoundExpression$TM -> CompoundExpression,
			Theorema`Language`VAR$[a_] -> a};
		ReleaseHold[ Map[ Function[ expr, ToString[ Unevaluated[ expr]], {HoldAll}], s]]
	]
execRight[ args___] := unexpected[ execRight, {args}]


(* ::Subsubsection:: *)
(* defsToRules *)

defsToRules[ defList_List] := Map[ singleDefToRule, defList]
defsToRules[ args___] := unexpected[ defsToRules, {args}]

singleDefToRule[ orig:FML$[ _, form_, _]] :=
	Module[{stripUniv, r},
		stripUniv = stripUniversalQuantifiers[ form];
		r = ruleForm[ stripUniv, orig];
		ToExpression[ r]
	]
singleDefToRule[ args___] := unexpected[ singleDefToRule, {args}]

ruleForm[ {(Theorema`Language`Iff$TM|Theorema`Language`IffDef$TM|Theorema`Language`Equal$TM|Theorema`Language`EqualDef$TM)[ l_, r_], c_List, var_List}, ref_] :=
    Block[ {testMember},
        With[ {left = execLeft[ Hold[l]], 
               cond = makeConjunction[ Map[ testMember[ $TMAKBatomic, #]&, c], And],
        		(* The complicated DUMMY$DEF... construction is necessary because ref itself contains strings (it's a whole formula incl key, label),
        	   	and we need to get the escaped strings into the Hold *)
               right = StringReplace[ execRight[ Hold[ AppendTo[ $usedDefinitionsInRewrite, "DUMMY$DEF"]; r]],
               	"DUMMY$DEF" -> ToString[ ref, InputForm]]},
            "RuleDelayed[" <> left <> "/;" <> execRight[ Hold[ cond] /. testMember -> MemberQ] <> "," <> right <> "]"
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
	Block[{$usedDefinitionsInRewrite = {}},
		{expr /. repl, $usedDefinitionsInRewrite}
	]
replaceAndTrack[ args___] := unexpected[ replaceAndTrack, {args}]

(* ::Section:: *)
(* FML$ datastructure *)

Options[ makeFML] = {key :> defKey[], formula -> True, label :> defLabel[]};

makeFML[ data__?OptionQ] :=
	Module[{k, f, l},
		{k, f, l} = {key, formula, label} /. {data} /. Options[ makeFML];
		makeTmaFml[ k, f, l]
	]
makeFML[ args___] := unexpected[ makeFML, {args}]

makeTmaFml[ key_List, fml_, label_String] := FML$[ key, fml, label]
makeTmaFml[ args___] := unexpected[ makeTmaFml, {args}]

defKey[ ] := {"ID" <> $cellTagKeySeparator <> ToString[ Unique[ "formula"]], "Source" <> $cellTagKeySeparator <> "none"}
defKey[ args___] := unexpected[ defKey, {args}]

defLabel[ ] := ToString[ $formulaLabel++]
defLabel[ args___] := unexpected[ defLabel, {args}]

initFormulaLabel[ ] := $formulaLabel = 1;
initFormulaLabel[ args___] := unexpected[ initFormulaLabel, {args}]

FML$ /: Dot[ FML$[ k_, _, _], key] := k
FML$ /: Dot[ FML$[ _, fml_, _], formula] := fml
FML$ /: Dot[ FML$[ _, _, l_], label] := l
FML$ /: Dot[ FML$[ k_, _, _], id] := k[[1]]
FML$ /: Dot[ FML$[ k_, _, _], source] := k[[2]]

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
	Module[ {new},
		{Theorema`Language`Exists$TM[ Theorema`Language`RNG$[ Theorema`Language`SETRNG$[ new, Theorema`Language`\[DoubleStruckCapitalN]0$TM]], True, 
			Theorema`Language`And$TM[ Theorema`Language`Equal$TM[ v, Theorema`Language`Plus$TM[ l, Theorema`Language`Times$TM[ new, s]]],
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


End[]

EndPackage[]