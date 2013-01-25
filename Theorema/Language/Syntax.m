(* ::Package:: *)

(* 
Theorema editor: W. Windsteiger
Author(s):       W. Windsteiger

What is the purpose of the Theorema editor? Read more in /ProgrammersDoc/Guidelines.nb#1871658360
*)

BeginPackage["Theorema`Language`Syntax`"];

Needs["Theorema`Common`"]

Begin["`Private`"]

theoremaDisplay[ expr_] := DisplayForm[ ToBoxes[ expr, TheoremaForm]]
theoremaDisplay[ args___] := unexpected[ theoremaDisplay, {args}]

(* $tmaNonStandardOperators is initialized here and gets values added in Expression.m *)
$tmaNonStandardOperators = {};

(* 
	Load the expression-specific definition that should be availabale for both
	"Theorema`Language`" and "Theorema`Computation`Language`" *)
Clear[ MakeBoxes];
	
Block[ {$ContextPath = Append[ $ContextPath, "Theorema`Language`"]},
	Get[ FileNameJoin[{$TheoremaDirectory, "Theorema", "Language", "Expressions.m"}]];
]
Block[ {$ContextPath = Append[ $ContextPath, "Theorema`Computation`Language`"]},
	Get[ FileNameJoin[{$TheoremaDirectory, "Theorema", "Language", "Expressions.m"}]];
]
   
initParser[]:=
  Module[{},
    $parseTheoremaExpressions = False;
    $parseTheoremaGlobals = False;
  ]
initParser[args___] := unexpected[ initParser, {args}]


(* ::Section:: *)
(* Language classification *)


(* To add a new quantifier, just add a pair to this list *)	
$tmaQuantifiers =
    {{"\[ForAll]", "Forall"},
     {"\[Exists]", "Exists"},
     {"\[Intersection]", "IntersectionOf"},
     {"\[Union]", "UnionOf"},
	 {"min", "MinimumOf"},
	 {"max", "MaximumOf"}
    };

$tmaQuantifierSymbols = Transpose[ $tmaQuantifiers][[1]];
$tmaQuantifierNames = Flatten[ ToExpression[ Map[ {"Theorema`Language`" <> # <> "$TM", "Theorema`Computation`Language`" <> # <> "$TM"}&, Transpose[ $tmaQuantifiers][[2]]]]];
$tmaQuantifierToName = Dispatch[ Apply[ Rule, $tmaQuantifiers, {1}]];
$tmaNameToQuantifier = Dispatch[ MapThread[ Rule, {$tmaQuantifierNames, Flatten[ Map[ {#, #}&, $tmaQuantifierSymbols]]}]];

isQuantifierSymbol[ s_String] := MemberQ[ $tmaQuantifierSymbols, s]
isQuantifierSymbol[ _] := False
isQuantifierSymbol[ args___] := unexpected[ isQuantifierSymbol, {args}]

isQuantifierName[ f_] := MemberQ[ $tmaQuantifierNames, f]
isQuantifierName[ args___] := unexpected[ isQuantifierName, {args}]

(* $tmaNonStandardOperators is defined in Expression.m *)
$tmaNonStandardOperatorNames = Transpose[ $tmaNonStandardOperators][[1]];
$tmaNonStandardOperatorToBuiltin = Dispatch[ Apply[ Rule, $tmaNonStandardOperators, {1}]];

isNonStandardOperatorName[ f_] := MemberQ[ $tmaNonStandardOperatorNames, f]
isNonStandardOperatorName[ args___] := unexpected[ isNonStandardOperatorName, {args}]

isStandardOperatorName[ f_Symbol] :=
    Module[ {n = SymbolName[ f]},
        StringLength[ n] > 3 && StringTake[ n, -3] === "$TM"
    ]
isStandardOperatorName[ f_] := False
isStandardOperatorName[ args___] := unexpected[ isStandardOperatorName, {args}]

tmaToInputOperator[ op_Symbol] :=
    Module[ {n = SymbolName[ op]},
        If[ StringTake[ n, -1] == "$",
            ToExpression[ n],
            ToExpression[ StringDrop[ n, -3]]
        ]
    ]
tmaToInputOperator[ args___] := unexpected[ tmaToInputOperator, {args}]	



(* ::Section:: *)
(* MakeExpression *)


MakeExpression[RowBox[{a_, TagBox[op_, Identity, ___], b_}], fmt_] := 
	MakeExpression[RowBox[{a, op, b}], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

MakeExpression[ RowBox[{UnderscriptBox[ q_?isQuantifierSymbol, rng_], form_}], fmt_] :=
    standardQuantifier[ Replace[ q, $tmaQuantifierToName], rng, "True", form, fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[{UnderscriptBox[ UnderscriptBox[ q_?isQuantifierSymbol, rng_], cond_], form_}], fmt_] :=
    standardQuantifier[ Replace[ q, $tmaQuantifierToName], rng, cond, form, fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[{form_, UnderscriptBox[ "|"|":", rng_]}], fmt_] :=
    standardQuantifier[ "SequenceOf", rng, "True", form, fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[{form_, UnderscriptBox[ "|"|":", rng_], cond_}], fmt_] :=
    standardQuantifier[ "SequenceOf", rng, cond, form, fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[{form_, UnderscriptBox[ UnderscriptBox[ "|"|":", rng_], cond_]}], fmt_] :=
    standardQuantifier[ "SequenceOf", rng, cond, form, fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[{rng_, "|"|":", cond_}], fmt_] :=
    With[ { v = getSingleRangeVar[ rng]},
        If[ v =!= $Failed,
            standardQuantifier[ "SequenceOf", rng, cond, v, fmt],
            MakeExpression[ "nE", fmt]
        ]
    ] /; $parseTheoremaExpressions

MakeExpression[ RowBox[{UnderscriptBox[ "where", rng_], form_}], fmt_] :=
	(* We use the powerful toRangeBox in order to have the many variants, multiranges, etc. However, only ABBRVRNG$ makes sense in a "where",
	   but we do not consider it a syntax error to use one of the other ranges *)
     With[ {r = toRangeBox[ rng]},
		MakeExpression[ RowBox[{"QU$", "[", 
            RowBox[{ r, ",", RowBox[{ "Abbrev", "[", RowBox[{ r, ",", form}], "]"}]}],
             "]"}], fmt]
	]/; $parseTheoremaExpressions

MakeExpression[ RowBox[{left_, RowBox[{":", "\[NegativeThickSpace]\[NegativeThinSpace]", "\[DoubleLongLeftRightArrow]"}], right_}], fmt_] :=
    MakeExpression[ RowBox[{"IffDef", "[", RowBox[{left, ",", right}], "]"}], fmt] /; $parseTheoremaExpressions

MakeExpression[ SubscriptBox[ "\[DoubleStruckCapitalN]", "0"], fmt_] := MakeExpression[ "\[DoubleStruckCapitalN]0", fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {l_,"\[LeftArrow]"}], fmt_] := MakeExpression[ RowBox[{"LeftArrow", "[", l, "]"}], fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {l_,"\[LeftArrowBar]"}], fmt_] := MakeExpression[ RowBox[{"LeftArrowBar", "[", l, "]"}], fmt] /; $parseTheoremaExpressions



(* ::Subsection:: *)
(* Global Declarations *)


MakeExpression[RowBox[{a_, TagBox[ "\[DoubleLongRightArrow]", Identity, ___]}], fmt_] := 
	MakeExpression[RowBox[{a, "\[DoubleLongRightArrow]"}], fmt] /; $parseTheoremaGlobals

MakeExpression[ UnderscriptBox[ "\[ForAll]", rng_], fmt_] :=
    standardGlobalQuantifier[ "globalForall", rng, "True", fmt] /; $parseTheoremaGlobals

MakeExpression[ UnderscriptBox[ UnderscriptBox[ "\[ForAll]", rng_], cond_], fmt_] :=
    standardGlobalQuantifier[ "globalForall", rng, cond, fmt] /; $parseTheoremaGlobals

MakeExpression[ RowBox[ {UnderscriptBox[ "\[ForAll]", rng_], decl_}], fmt_] :=
    standardQuantifier[ "globalForall", rng, "True", decl, fmt] /; $parseTheoremaGlobals

MakeExpression[ RowBox[ {UnderscriptBox[ UnderscriptBox[ "\[ForAll]", rng_], cond_], decl_}], fmt_] :=
    standardQuantifier[ "globalForall", rng, cond, decl, fmt] /; $parseTheoremaGlobals

MakeExpression[ RowBox[ {cond_, "\[Implies]"|"\[DoubleLongRightArrow]"|"\[DoubleRightArrow]"}], fmt_] := 
	MakeExpression[ RowBox[{ "globalImplies", "[", cond, "]"}], fmt] /; $parseTheoremaGlobals

MakeExpression[ RowBox[{lhs_, ":=", UnderscriptBox[ "\[CapitalDelta]", rng_]}], fmt_] := 
	(* We don't use the powerful toRangeBox because in this expression, the range does not have the many variants, multiranges, etc.*)
	With[ {r = toDomSpecRangeBox[ rng]},
		MakeExpression[ RowBox[{ "domainConstruct", "[", RowBox[{lhs, ",", RowBox[ {"QU$", "[", RowBox[{r, ",", r}], "]"}]}], "]"}], fmt]
	] /; $parseTheoremaGlobals

toDomSpecRangeBox[ RowBox[{v_, "\[Superset]", d_}]] := RowBox[ {"RNG$", "[", RowBox[ {"DOMEXTRNG$", "[", RowBox[ {v, ",", d}], "]"}], "]"}]
toDomSpecRangeBox[ v_String] := RowBox[ {"RNG$", "[", makeRangeSequence[ v], "]"}]
toDomSpecRangeBox[args___] := unexpected[ toDomSpecRangeBox, {args}]

MakeExpression[ UnderscriptBox[ "where", rng_], fmt_] := 
	(* We the powerful toRangeBox in order to have the many variants, multiranges, etc. However, only ABBRVRNG$ makes sense in a "where",
	   but we do not consider it a syntax error to use one of the other ranges *)
	With[ {r = toRangeBox[ rng]},
		MakeExpression[ RowBox[{"QU$", "[", 
            RowBox[{ r, ",", RowBox[{ "globalAbbrev", "[", r, "]"}]}], "]"}], fmt]
	] /; $parseTheoremaGlobals


(* ::Subsection:: *)
(* Auxiliary parsing functions *)


(* QU$ is an auxiliary tag introduced in quantifier MakeExpressions, which should be eliminated during expression parsing
	in markVariables. Any remaining QU$ actually indicates an error, and it will evaluate through this definition and
	throw an exception. *)
QU$[args___] := unexpected[ QU$, {args}]


SetAttributes[ standardQuantifier, HoldRest]
standardQuantifier[ name_, rng_, cond_, expr_, fmt_] :=
    With[ {r = toRangeBox[ rng]},
        MakeExpression[ RowBox[{"QU$", "[", 
            RowBox[{ r, ",", RowBox[{ name, "[", RowBox[{ r, ",", cond, ",", expr}], "]"}]}],
             "]"}], fmt]
    ]
standardQuantifier[ args___] := unexpected[ standardQuantifier, {args}]
    
standardGlobalQuantifier[ name_, rng_, cond_, fmt_] :=
    With[ {r = toRangeBox[ rng]},
        MakeExpression[ RowBox[{"QU$", "[", 
            RowBox[{ r, ",", RowBox[{ name, "[", RowBox[{ r, ",", cond}], "]"}]}],
             "]"}], fmt]
    ]
standardGlobalQuantifier[ args___] := unexpected[ standardGlobalQuantifier, {args}]



(* ::Subsubsection:: *)
(* Ranges *)


Clear[ toRangeBox, makeRangeSequence]

toRangeBox[s_] :=
    RowBox[{"RNG$", "[", makeRangeSequence[s], "]"}]            
toRangeBox[args___] := unexpected[ toRangeBox, {args}]

makeRangeSequence[ RowBox[{v_, "\[Element]", s_}]] :=
	makeSingleSetRange[ v, s]

makeRangeSequence[ RowBox[{x___, y_, ",", RowBox[{v_, "\[Element]", s_}]}]] :=
    Sequence[ makeRangeSequence[ RowBox[{x, RowBox[{y, "\[Element]", s}]}]], ",",
    	makeSingleSetRange[ v, s]]

makeRangeSequence[ RowBox[{p_, "[", RowBox[{x__, ",", v_}], "]"}]] :=
	Sequence[ makeRangeSequence[ RowBox[{p, "[", RowBox[{x}], "]"}]], ",",
		makeSinglePredRange[ v, p]]

makeRangeSequence[ RowBox[{p_, "[", RowBox[{v_}], "]"}]] :=
	makeSinglePredRange[ v, p]

makeRangeSequence[ RowBox[{p_, "[", v_String, "]"}]] :=
	makeSinglePredRange[ v, p]

makeRangeSequence[ RowBox[{RowBox[{v_, "=", lower_}], ",", "\[Ellipsis]", ",", upper_}]] :=
    makeSingleStepRange[ v, lower, upper, "1"]

makeRangeSequence[ RowBox[{x___, y_, ",", RowBox[{v_, "=", lower_}], ",", "\[Ellipsis]", ",", upper_}]] :=
    Sequence[ makeRangeSequence[ RowBox[{x, RowBox[{y, "=", lower}], ",", "\[Ellipsis]", ",", upper}]], ",",
    	makeSingleStepRange[ v, lower, upper, "1"]]

makeRangeSequence[ RowBox[{RowBox[{v_, "=", lower_}], ",", OverscriptBox["\[Ellipsis]", step_], ",", upper_}]] :=
    makeSingleStepRange[ v, lower, upper, step]

makeRangeSequence[ RowBox[{x___, y_, ",", RowBox[{v_, "=", lower_}], ",", OverscriptBox["\[Ellipsis]", step_], ",", upper_}]] :=
    Sequence[ makeRangeSequence[ RowBox[{x, RowBox[{y, "=", lower}], ",", OverscriptBox["\[Ellipsis]", step], ",", upper}]], ",",
    	makeSingleStepRange[ v, lower, upper, step]]

makeRangeSequence[ RowBox[{a_, "=", e_}]] :=
	makeSingleAbbrevRange[ a, e]

makeRangeSequence[RowBox[{s_,",",r__}]] :=
    Sequence[ makeRangeSequence[s], ",", makeRangeSequence[RowBox[{r}]]]

makeRangeSequence[RowBox[{s_}]] :=
    makeRangeSequence[s]

makeRangeSequence[GridBox[ r_List]] := Apply[ Sequence, Riffle[ Map[ makeRangeSequence, Flatten[ r]], ","]]

makeRangeSequence[s_] :=
    RowBox[{"SIMPRNG$","[",s,"]"}]
makeRangeSequence[args___] := unexpected[ makeRangeSequence, {args}]

makeSingleSetRange[ v_, s_] := 
	RowBox[ {"SETRNG$", "[", RowBox[ {v, ",", s}], "]"}]
makeSingleSetRange[args___] := unexpected[ makeSingleSetRange, {args}]

makeSinglePredRange[ v_, p_] := 
	RowBox[ {"PREDRNG$", "[", RowBox[ {v, ",", p}], "]"}]
makeSinglePredRange[args___] := unexpected[ makeSinglePredRange, {args}]

makeSingleStepRange[ v_, lower_, upper_, step_] :=
	RowBox[ {"STEPRNG$", "[", RowBox[ {v, ",", lower, ",", upper, ",", step}], "]"}]
makeSingleStepRange[args___] := unexpected[ makeSingleStepRange, {args}]

makeSingleAbbrevRange[ a_, e_] :=
	RowBox[ {"ABBRVRNG$", "[", RowBox[ {a, ",", e}], "]"}]
makeSingleAbbrevRange[ args___] := unexpected[ makeSingleAbbrevRange, {args}]

getSingleRangeVar[ v_String] := v
getSingleRangeVar[ RowBox[{v_, "\[Element]", _}]] := v
getSingleRangeVar[ RowBox[{_, "[", v_String, "]"}]] := v
getSingleRangeVar[ RowBox[{RowBox[{v_, "=", _}], ",", "\[Ellipsis]", ",", _}]] := v
getSingleRangeVar[ r_] :=
	Module[ {},
		notification[ translate[ "ambiguousRange"], DisplayForm[ makeRangeBox[ r, TheoremaForm]]];
		$Failed
	]
getSingleRangeVar[ args___] := unexpected[ getSingleRangeVar, {args}]



(* ::Section:: *)
(* MakeBoxes *)


MakeBoxes[ (q_?isQuantifierName)[ rng_, True, form_], TheoremaForm] := 
	RowBox[ {UnderscriptBox[ Replace[ q, $tmaNameToQuantifier], makeRangeBox[ rng, TheoremaForm]],
		MakeBoxes[ form, TheoremaForm]}
	]

MakeBoxes[ (q_?isQuantifierName)[ rng_, cond_, form_], TheoremaForm] := 
	RowBox[ {UnderscriptBox[ UnderscriptBox[ Replace[ q, $tmaNameToQuantifier], makeRangeBox[ rng, TheoremaForm]], MakeBoxes[ cond, TheoremaForm]],
		MakeBoxes[ form, TheoremaForm]}
	]

MakeBoxes[ (op_?isNonStandardOperatorName)[ arg___], TheoremaForm] :=
    With[ {b = Replace[ op, $tmaNonStandardOperatorToBuiltin]},
        MakeBoxes[ b[ arg], TheoremaForm]
    ]

MakeBoxes[ (op_?isStandardOperatorName)[ arg__], TheoremaForm] :=
    With[ {b = tmaToInputOperator[ op]},
    	(* Special cases, because otherwise And uses && and Or uses || *)
    	Switch[ b,
    		And,
    		tmaInfixBox[ {arg}, "\[And]"],
    		Or,
    		tmaInfixBox[ {arg}, "\[Or]"],
    		Not,
    		RowBox[{ "\[Not]", MakeBoxes[ arg, TheoremaForm]}],
    		_,
        	MakeBoxes[ b[ arg], TheoremaForm]
    	]
    ]

MakeBoxes[ s_Symbol, TheoremaForm] := 
	Module[ {n = SymbolName[ s]},
		If[ StringLength[ n] > 3 && StringTake[ n, -3] === "$TM",
			StringDrop[ n, -3],
			n
		]
	]

tmaInfixBox[ args_List, op_String] := RowBox[ Riffle[ Map[ MakeBoxes[ #, TheoremaForm]&, args], op]]
tmaInfixBox[ args___] := unexpected[ tmaInfixBox, {args}]

(*

SetAttributes[\[Bullet]\[Bullet]range,HoldAll];

\[Bullet]range::usage="\[Bullet]range[range1,...] represents a range specification (mostly for variables). One single \[Bullet]range-object can contain more than one range specification.";

\[Bullet]\[Bullet]range::usage="\[Bullet]\[Bullet]range[range1,...] represents a range specification (mostly for variables). One single \[Bullet]\[Bullet]range-object can contain more than one range specification.";

ToRangeBox[x_]/;PrintMessage[ToRangeBox::usage]:=Null

ToHoldingRangeBox::usage="ToHoldingRangeBox[box] produces the range specification of a quantifier (with all the necessary attributes).";

ToTMRangeBox::usage="ToTMRangeBox[box] produces the range specification of a quantifier (without any attributes).";



ToHoldingRangeBox[x_]:=ToPreliminaryRangeBox[x]/.rangeToHoldingRange

ToTMRangeBox[x_]:=ToPreliminaryRangeBox[x]/.holdingRangeToRange

MakeRangeSequence::usage="MakeRangeSequence[boxes]] reads the individual range specifications.";

MakeRangeSequence[GridBox[{{s_},r__}]]:=Sequence[MakeRangeSequence[s],",",MakeRangeSequence[GridBox[{r}]]]

MakeRangeSequence[GridBox[{{s_}}]]:=MakeRangeSequence[s]

MakeRangeSequence[RowBox[{"(",x_,")"}]]:=x/;$SessionIdentifier==="Prog"

MakeRangeSequence[RowBox[{"(",x_,")"}]]:=MakeRangeSequence[x]

SetAttributes[\[Bullet]\[Bullet]predRange,HoldFirst];

\[Bullet]predRange::usage="\[Bullet]predRange[x,pred] denotes that the variable `x` statisfies the unary predicate `pred`.";

\[Bullet]\[Bullet]predRange::usage="\[Bullet]\[Bullet]predRange[x,pred] denotes that the variable `x` statisfies the unary predicate `pred`.";

MakeRangeSequence[RowBox[{pred_,"[",x_,"]"}]]:=RowBox[{"\[Bullet]predRange","[",x,",",pred,"]"}]

MakeRangeSequence[RowBox[{pred_,"[",RowBox[{x_}],"]"}]]:=RowBox[{"\[Bullet]predRange","[",x,",",pred,"]"}]

MakeRangeSequence[RowBox[{pred_,"[",RowBox[{x_,",",y__}],"]"}]]:=Sequence[RowBox[{"\[Bullet]predRange","[",x,",",pred,"]"}],",",MakeRangeSequence[RowBox[{pred,"[",RowBox[{y}],"]"}]]]

SetAttributes[\[Bullet]\[Bullet]setRange,HoldFirst];

\[Bullet]setRange::usage="\[Bullet]setRange[x,s] denotes that the variable `x` ranges over the set `s`.";

\[Bullet]\[Bullet]setRange::usage="\[Bullet]\[Bullet]setRange[x,s] denotes that the variable `x` ranges over the set `s`.";

MakeRangeSequence[RowBox[{i_, ",", j__,",",RowBox[{k_, "\[Element]", s_}]}]]:=Sequence[RowBox[{"\[Bullet]setRange","[",i,",",s,"]"}],",",MakeRangeSequence[RowBox[{j,",",RowBox[{k, "\[Element]", s}]}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_, "\[Element]", s_}]}]]:=Sequence[RowBox[{"\[Bullet]setRange","[",j,",",s,"]"}],",",RowBox[{"\[Bullet]setRange","[",k,",",s,"]"}]]

MakeRangeSequence[RowBox[{k_,"\[Element]",s_}]]:=RowBox[{"\[Bullet]setRange","[",k,",",s,"]"}]

SetAttributes[\[Bullet]\[Bullet]integerRange,HoldFirst];

\[Bullet]integerRange::usage="\[Bullet]integerRange[i,lower,upper] denotes that the variable `i` ranges over all integers from `lower` to `upper`.";

\[Bullet]\[Bullet]integerRange::usage="\[Bullet]\[Bullet]integerRange[i,lower,upper] denotes that the variable `i` ranges over all integers from `lower` to `upper`.";

MakeRangeSequence[RowBox[{i_, ",", j__,",",n      RowBox[{k_, "=", lower_}], ",", "...", ",", upper_}]]:=Sequence[RowBox[{"\[Bullet]integerRange","[",i,",",lower,",",upper,"]"}],",",MakeRangeSequence[RowBox[{j,",",n      RowBox[{k, "=", lower}], ",", "...", ",", upper}]]]

MakeRangeSequence[RowBox[{j_, ",", n      RowBox[{k_, "=", lower_}], ",", "...", ",", upper_}]]:=Sequence[RowBox[{"\[Bullet]integerRange","[",j,",",lower,",",upper,"]"}],",",RowBox[{"\[Bullet]integerRange","[",k,",",lower,",",upper,"]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,"=",lower_}],",","...",",",upper_}]]:=n	RowBox[{"\[Bullet]integerRange","[",k,",",lower,",",upper,"]"}]

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,"=",lower_}],",","..."}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",i,",",lower,",","\[Infinity]","]"}],",",MakeRangeSequence[RowBox[{j,",",RowBox[{k,"=",lower}],",","..."}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,"=",lower_}],",","..."}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",j,",",lower,",","\[Infinity]","]"}],",",RowBox[{"\[Bullet]integerRange","[",k,",",lower,",","\[Infinity]","]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,"=",lower_}],",","..."}]]:=n	RowBox[{"\[Bullet]integerRange","[",k,",",lower,",","\[Infinity]","]"}]

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,"=","..."}],",",upper_}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",i,",",RowBox[{"-", "\[Infinity]"}],",",upper,"]"}],",",MakeRangeSequence[RowBox[{j,",",RowBox[{k,"=","..."}],",",upper}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,"=","..."}],",",upper_}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",j,",",RowBox[{"-", "\[Infinity]"}],",",upper,"]"}],",",RowBox[{"\[Bullet]integerRange","[",k,",",RowBox[{"-", "\[Infinity]"}],",",upper,"]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,"=","..."}],",",upper_}]]:=n	RowBox[{"\[Bullet]integerRange","[",k,",",RowBox[{"-", "\[Infinity]"}],",",upper,"]"}]

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,"=","..."}]}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",i,",",RowBox[{"-", "\[Infinity]"}],",","\[Infinity]","]"}],",",nMakeRangeSequence[RowBox[{j,",",RowBox[{k,"=","..."}]}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,"=","..."}]}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",j,",",RowBox[{"-", "\[Infinity]"}],",","\[Infinity]","]"}],",",n	RowBox[{"\[Bullet]integerRange","[",k,",",RowBox[{"-", "\[Infinity]"}],",","\[Infinity]","]"}]]

MakeRangeSequence[RowBox[{k_,"=","..."}]]:=n	RowBox[{"\[Bullet]integerRange","[",k,",",RowBox[{"-", "\[Infinity]"}],",","\[Infinity]","]"}]

SetAttributes[\[Bullet]\[Bullet]domainRange,HoldFirst];

\[Bullet]domainRange::usage="\[Bullet]domainRange[i,domain,lower,upper] denotes that the variable `i` ranges over all elements of the enumerable domain `domain` from `lower` to `upper`.";

\[Bullet]\[Bullet]domainRange::usage="\[Bullet]\[Bullet]domainRange[i,domain,lower,upper] denotes that the variable `i` ranges over all elements of the enumerable domain `domain` from `lower` to `upper`.";

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","...",",",upper_}]]:=Sequence[RowBox[{"\[Bullet]domainRange","[",i,",",domain,",",lower,",",upper,"]"}],",",MakeRangeSequence[RowBox[{j,",",RowBox[{k,UnderscriptBox["=",domain],lower}],",","...",",",upper}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","...",",",upper_}]]:=Sequence[RowBox[{"\[Bullet]domainRange","[",j,",",domain,",",lower,",",upper,"]"}],",",RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",lower,",",upper,"]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","...",",",upper_}]]:=(DeclareUnderscriptDomain[domain];RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",lower,",",upper,"]"}])

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","..."}]]:=Sequence[n		RowBox[{"\[Bullet]domainRange","[",i,",",domain,",",lower,",",RowBox[{domain,"[","Last","]"}],"]"}],",",n		MakeRangeSequence[RowBox[{j,",",RowBox[{k,UnderscriptBox["=",domain],lower}],",","..."}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","..."}]]:=Sequence[n		RowBox[{"\[Bullet]domainRange","[",j,",",domain,",",lower,",",RowBox[{domain,"[","Last","]"}],"]"}],",",n		RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",lower,",",RowBox[{domain,"[","Last","]"}],"]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","..."}]]:=(DeclareUnderscriptDomain[domain];RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",lower,",",RowBox[{domain,"[","Last","]"}],"]"}])

MakeRangeSequence[n		RowBox[{i_,",",j__,",",RowBox[{k_,UnderscriptBox["=",domain_],"..."}],",",upper_}]]:=Sequence[n		RowBox[{"\[Bullet]domainRange","[",i,",",domain,",",RowBox[{domain,"[","First","]"}],",",upper,"]"}],",",MakeRangeSequence[n		RowBox[{j,",",RowBox[{k,UnderscriptBox["=",domain],"..."}],",",upper}]]]

MakeRangeSequence[n		RowBox[{j_,",",RowBox[{k_,UnderscriptBox["=",domain_],"..."}],",",upper_}]]:=Sequence[n		RowBox[{"\[Bullet]domainRange","[",j,",",domain,",",RowBox[{domain,"[","First","]"}],",",upper,"]"}],",",n		RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",RowBox[{domain,"[","First","]"}],",",upper,"]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,UnderscriptBox["=",domain_],"..."}],",",upper_}]]:=(DeclareUnderscriptDomain[domain];RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",RowBox[{domain,"[","First","]"}],",",upper,"]"}])

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,UnderscriptBox["=",domain_],"..."}]}]]:=Sequence[RowBox[{"\[Bullet]domainRange","[",i,",",domain,",",RowBox[{domain,"[","First","]"}],",",RowBox[{domain,"[","Last","]"}],"]"}],",",MakeRangeSequence[RowBox[{j,",",RowBox[{k,UnderscriptBox["=",domain],"..."}]}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,UnderscriptBox["=",domain_],"..."}]}]]:=Sequence[RowBox[{"\[Bullet]domainRange","[",j,",",domain,",",RowBox[{domain,"[","First","]"}],",",RowBox[{domain,"[","Last","]"}],"]"}],",",RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",RowBox[{domain,"[","First","]"}],",",RowBox[{domain,"[","Last","]"}],"]"}]]

MakeRangeSequence[RowBox[{k_,UnderscriptBox["=",domain_],"..."}]]:=n	(DeclareUnderscriptDomain[domain];RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",RowBox[{domain,"[","First","]"}],",",RowBox[{domain,"[","Last","]"}],"]"}])

SetAttributes[\[Bullet]\[Bullet]limitRange,HoldFirst];

MakeRangeSequence[RowBox[{i_, ",", j__, ",",RowBox[{k_,UnderscriptBox["\[LongRightArrow]"|"\[RightArrow]"|"->",dom_], s_}]}]]:=n	Sequence[RowBox[{"\[Bullet]limitRange","[",i,",",s,",",dom,"]"}],",",n		MakeRangeSequence[RowBox[{j,",",RowBox[{k, "\[LongRightArrow]", s}]}]]]

MakeRangeSequence[n    RowBox[{j_, ",", n      RowBox[{k_, UnderscriptBox["\[LongRightArrow]"|"\[RightArrow]"|"->",dom_], s_}]}]]:=Sequence[RowBox[{"\[Bullet]limitRange","[",j,",",s,",",dom,"]"}],",",RowBox[{"\[Bullet]limitRange","[",k,",",s,",",dom,"]"}]]

MakeRangeSequence[RowBox[{k_,UnderscriptBox["\[LongRightArrow]"|"\[RightArrow]"|"->",dom_],s_}]]:=RowBox[{"\[Bullet]limitRange","[",k,",",s,",",dom,"]"}]

MakeRangeSequence[RowBox[{i_, ",", j__, ",",RowBox[{k_,"\[LongRightArrow]"|"\[RightArrow]"|"->", s_}]}]]:=n	Sequence[RowBox[{"\[Bullet]limitRange","[",i,",",s,",","None","]"}],",",n		MakeRangeSequence[RowBox[{j,",",RowBox[{k, "\[LongRightArrow]", s}]}]]]

MakeRangeSequence[n    RowBox[{j_, ",", n      RowBox[{k_, "\[LongRightArrow]"|"\[RightArrow]"|"->", s_}]}]]:=Sequence[RowBox[{"\[Bullet]limitRange","[",j,",",s,",","None","]"}],",",RowBox[{"\[Bullet]limitRange","[",k,",",s,",","None","]"}]]

MakeRangeSequence[RowBox[{k_,"\[LongRightArrow]"|"\[RightArrow]"|"->",s_}]]:=RowBox[{"\[Bullet]limitRange","[",k,",",s,",","None","]"}]

SetAttributes[\[Bullet]\[Bullet]simpleRange,HoldFirst];


\[Bullet]locval::usage="\[Bullet]locval[x,v] declares `v` as a local value for `x`.";

MakeRangeSequence[RowBox[{x_,"="|"\[LeftArrow]"|"\[LongLeftArrow]",v_}]]:=RowBox[{"\[Bullet]locval","[",RowBox[{x,",",v}],"]"}]

MakeRangeBoxes::usage="MakeRangeBoxes[x,f] produces the nice-looking output for the range 'x' in output form 'f'.";

SetAttributes[MakeRangeBoxes,HoldAll];

MakeRangeBoxes[(\[Bullet]range|\[Bullet]\[Bullet]range)[x_Pattern,y___],f_]:=RowBox[{"(",RowBox[MakePatternRangeBoxes[{x,y},f]],")"}]

MakeRangeBoxes[(\[Bullet]range|\[Bullet]\[Bullet]range)[x:(_[_Pattern,___]),y___],f_]:=RowBox[{"(",RowBox[MakePatternRangeBoxes[{x,y},f]],")"}]

MakeRangeBoxes[(\[Bullet]range|\[Bullet]\[Bullet]range)[x_],f_]:=MakeSingleRangeBoxes[x,f]

MakeRangeBoxes[(\[Bullet]range|\[Bullet]\[Bullet]range)[x:(__ \[Bullet]simpleRange|__ \[Bullet]\[Bullet]simpleRange)],f_]:=RowBox[MakeSimpleRangeBoxes[{x},f]]

MakeRangeBoxes[(\[Bullet]range|\[Bullet]\[Bullet]range)[x__],f_]:=GridBox[MakeMultipleRangeBoxes[{x},f]]

MakeRangeBoxes[x_,f_]:=(PrintMessage[Theorema::strangeRange,ToString[x]];
MakeBoxes[x,f])

ClearAll[MakeSingleRangeBoxes];
((SetAttributes[MakeSingleRangeBoxes,HoldAll];))

MakeSingleRangeBoxes[(\[Bullet]simpleRange|\[Bullet]\[Bullet]simpleRange)[x_],f_]:=MakeBoxes[x,f]

MakeSingleRangeBoxes[(\[Bullet]predRange|\[Bullet]\[Bullet]predRange)[x_,t_],f_]:=MakeSingleRangeBoxes[\[Bullet]simpleRange[x],f]/;(TypeVar/.SessionContext[x])===\[Bullet]\[Bullet]predRange[x,t]

MakeSingleRangeBoxes[(\[Bullet]predRange|\[Bullet]\[Bullet]predRange)[x_,t_],f_]:=MakeBoxes[t[x],f]

MakeSingleRangeBoxes[(\[Bullet]setRange|\[Bullet]\[Bullet]setRange)[x_,s_],f_]:=MakeSingleRangeBoxes[\[Bullet]simpleRange[x],f]/;(TypeVar/.SessionContext[x])===\[Bullet]\[Bullet]setRange[x,s]

MakeSingleRangeBoxes[(\[Bullet]setRange|\[Bullet]\[Bullet]setRange)[x_,s_],f_]:=RowBox[{MakeBoxes[x,f],"\[Element]",MakeBoxes[s,f]}]

MakeSingleRangeBoxes[(\[Bullet]integerRange|\[Bullet]\[Bullet]integerRange)[x_,lower_,upper_],f_]:=MakeSingleRangeBoxes[\[Bullet]simpleRange[x],f]/;(TypeVar/.SessionContext[x])===\[Bullet]\[Bullet]integerRange[x,lower,upper]

MakeSingleRangeBoxes[(\[Bullet]integerRange|\[Bullet]\[Bullet]integerRange)[x_,lower_,upper_],f_]:=RowBox[{RowBox[{MakeBoxes[x,f],"=",MakeBoxes[lower,f]}],",","...",",",MakeBoxes[upper,f]}]

MakeSingleRangeBoxes[(\[Bullet]domainRange|\[Bullet]\[Bullet]domainRange)[x_,domain_,lower_,upper_],f_]:=MakeSingleRangeBoxes[\[Bullet]simpleRange[x],f]/;(TypeVar/.SessionContext[x])===\[Bullet]\[Bullet]domainRange[x,domain,lower,upper]

MakeSingleRangeBoxes[(\[Bullet]domainRange|\[Bullet]\[Bullet]domainRange)[x_,domain_,lower_,upper_],f_]:=RowBox[{RowBox[{MakeBoxes[x,f],UnderscriptBox["=",MakeBoxes[domain,f]],MakeBoxes[lower,f]}],",","...",",",MakeBoxes[upper,f]}]

MakeSingleRangeBoxes[(\[Bullet]limitRange|\[Bullet]\[Bullet]limitRange)[x_,y_],f_]:=MakeSingleRangeBoxes[\[Bullet]simpleRange[x],f]/;(TypeVar/.SessionContext[x])===\[Bullet]\[Bullet]limitRange[x,y]

MakeSingleRangeBoxes[(\[Bullet]limitRange|\[Bullet]\[Bullet]limitRange)[x_,y_],f_]:=RowBox[{MakeBoxes[x,f],"->",MakeBoxes[y,f]}]

MakeSingleRangeBoxes[(\[Bullet]locval)[x_,y_],f_]:=RowBox[{MakeBoxes[x,f],"\[LeftArrow]",MakeBoxes[y,f]}]

MakeSingleRangeBoxes[x_,f_]:=(PrintMessage[Theorema::strangeRange,ToString[x]];
RowBox[{"(",MakeBoxes[x,f],")"}])

SetAttributes[MakeSimpleRangeBoxes,HoldAll];

MakeSimpleRangeBoxes[{(\[Bullet]simpleRange|\[Bullet]\[Bullet]simpleRange)[x_]},f_]:={MakeBoxes[x,f]}

MakeSimpleRangeBoxes[{(\[Bullet]simpleRange|\[Bullet]\[Bullet]simpleRange)[x_],y__},f_]:=Prepend[Prepend[MakeSimpleRangeBoxes[{y},f],","],MakeBoxes[x,f]]

SetAttributes[MakeMultipleRangeBoxes,HoldAll];

MakeMultipleRangeBoxes[{x_},f_]:={{MakeSingleRangeBoxes[x,f]}}

MakeMultipleRangeBoxes[{x_,y__},f_]:=Prepend[MakeMultipleRangeBoxes[{y},f],{MakeSingleRangeBoxes[x,f]}]

SetAttributes[MakePatternRangeBoxes,HoldAll]

MakePatternRangeBoxes[{x_},f_]:={MakeBoxes[x,f]}

MakePatternRangeBoxes[{x_,y__},f_]:=Prepend[Prepend[MakePatternRangeBoxes[{y},f],","],MakeBoxes[x,f]]


ToConditionBox[]:="True"

ToConditionBox[RowBox[{}]]:="True"

ToConditionBox[RowBox[{s_}]]:=ToConditionBox[s]

ToConditionBox[s_]:=s

ToConditionBox[s__]:=RowBox[{s}]

SetAttributes[MakeConditionBoxes,HoldAll];

MakeConditionBoxes[x_,f_]:=MakeBoxes[x,f];


*)

initParser[];

End[];
EndPackage[];

