(* 
Theorema editor: W. Windsteiger
Author(s):       W. Windsteiger

What is the purpose of the Theorema editor? Read more in /ProgrammersDoc/Guidelines.nb#1871658360
*)

BeginPackage["Theorema`Language`Parser`"];

Needs["Theorema`Common`"]

Begin["`Private`"]

initParser[]:=
  Module[{},
    $parseTheoremaExpressions = False;
    $parseTheoremaGlobals = False;
  ]
initParser[args___] := unexpected[ initParser, {args}]

MakeExpression[RowBox[{a_, TagBox[op_, Identity, ___], b_}], fmt_] := 
	MakeExpression[RowBox[{a, op, b}], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

standardQuantifier[ name_, rng_, cond_, expr_, fmt_] :=
    With[ {r = toRangeBox[ rng]},
        MakeExpression[ RowBox[{"QU$", "[", 
            RowBox[{ r, ",", RowBox[{ name, "[", RowBox[{ r, ",", cond, ",", expr}], "]"}]}],
             "]"}], fmt]
    ]
standardQuantifier[ args___] := unexpected[ standardQuantifier, {args}]
    
MakeExpression[ RowBox[{UnderscriptBox[ q_?isQuantifierSymbol, rng_], form_}], fmt_] :=
    standardQuantifier[ Replace[ q, $tmaQuantifierToName], rng, "True", form, fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[{UnderscriptBox[ UnderscriptBox[ q_?isQuantifierSymbol, rng_], cond_], form_}], fmt_] :=
    standardQuantifier[ Replace[ q, $tmaQuantifierToName], rng, cond, form, fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[{left_, RowBox[{":", "\[NegativeThickSpace]\[NegativeThinSpace]", "\[DoubleLongLeftRightArrow]"}], right_}], fmt_] :=
    MakeExpression[ RowBox[{"IffDef", "[", RowBox[{left, ",", right}], "]"}], fmt] /; $parseTheoremaExpressions

QU$[args___] := unexpected[ QU$, {args}]

AppendTo[ $ContextPath, "Theorema`Language`"];

MakeBoxes[ (q_?isQuantifierName)[ rng_, True$TM|Theorema`Computation`Language`True$TM, form_], fmt_] := 
	RowBox[ {UnderscriptBox[ Replace[ q, $tmaNameToQuantifier], makeRangeBox[ rng, fmt]],
		MakeBoxes[ form, fmt]}
	]

MakeBoxes[ (q_?isQuantifierName)[ rng_, cond_, form_], fmt_] := 
	RowBox[ {UnderscriptBox[ UnderscriptBox[ Replace[ q, $tmaNameToQuantifier], makeRangeBox[ rng, fmt]], MakeBoxes[ cond, fmt]],
		MakeBoxes[ form, fmt]}
	]

MakeBoxes[ (op_?isNonStandardOperatorName)[ arg__], fmt_] :=
    With[ {b = Replace[ op, $tmaNonStandardOperatorToBuiltin]},
        MakeBoxes[ b[ arg], fmt]
    ]
MakeBoxes[ (op_?isStandardOperatorName)[ arg__], fmt_] :=
    With[ {b = tmaToInputOperator[ op]},
        MakeBoxes[ b[ arg], fmt]
    ]
MakeBoxes[ (VAR$|Theorema`Computation`Language`VAR$)[ v_], fmt_] := StyleBox[ MakeBoxes[ v, fmt], "ExpressionVariable"]

MakeBoxes[ s_Symbol, fmt_] := 
	Module[ {n = SymbolName[ s]},
		If[ StringLength[ n] > 3 && StringTake[ n, -3] === "$TM",
			StringDrop[ n, -3],
			n
		]
	]
	
(* To add a new quantifier, just add a pair to this list *)	
$tmaQuantifiers =
    {{"\[ForAll]", "Forall"},
     {"\[Exists]", "Exists"},
     {"\[Intersection]", "IntersectionOf"},
     {"\[Union]", "UnionOf"}
    };

$tmaQuantifierSymbols = Transpose[ $tmaQuantifiers][[1]];
$tmaQuantifierNames = Flatten[ ToExpression[ Map[ {"Theorema`Language`" <> # <> "$TM", "Theorema`Computation`Language`" <> # <> "$TM"}&, Transpose[ $tmaQuantifiers][[2]]]]];
$tmaQuantifierToName = Dispatch[ Apply[ Rule, $tmaQuantifiers, {1}]];
$tmaNameToQuantifier = Dispatch[ MapThread[ Rule, {$tmaQuantifierNames, Flatten[ Map[ {#, #}&, $tmaQuantifierSymbols]]}]];

isQuantifierSymbol[ s_String] := MemberQ[ $tmaQuantifierSymbols, s]
isQuantifierSymbol[ args___] := unexpected[ isQuantifierSymbol, {args}]

isQuantifierName[ f_] := MemberQ[ $tmaQuantifierNames, f]
isQuantifierName[ args___] := unexpected[ isQuantifierName, {args}]

$tmaNonStandardOperators = 
    {
     {Iff$TM, DoubleRightArrow},
     {EqualDef$TM, SetDelayed},
     {Equal$TM, Set},
     {Tuple$TM, AngleBracket}
    };

$tmaNonStandardOperatorNames = Transpose[ $tmaNonStandardOperators][[1]];
$tmaNonStandardOperatorToBuiltin = Dispatch[ Apply[ Rule, $tmaNonStandardOperators, {1}]];

isNonStandardOperatorName[ f_] := MemberQ[ $tmaNonStandardOperatorNames, f]
isNonStandardOperatorName[ args___] := unexpected[ isNonStandardOperatorName, {args}]

isStandardOperatorName[ f_] :=
    Module[ {n = SymbolName[ f]},
        StringLength[ n] > 3 && StringTake[ n, -3] === "$TM"
    ]
isStandardOperatorName[ args___] := unexpected[ isStandardOperatorName, {args}]

tmaToInputOperator[ op_] :=
    Module[ {n = SymbolName[ op]},
        If[ StringTake[ n, -1] == "$",
            ToExpression[ n],
            ToExpression[ StringDrop[ n, -3]]
        ]
    ]
tmaToInputOperator[ args___] := unexpected[ tmaToInputOperator, {args}]

(* ::Section:: *)
(* Global Declarations *)

standardGlobalQuantifier[ name_, rng_, cond_, fmt_] :=
    With[ {r = toRangeBox[ rng]},
        MakeExpression[ RowBox[{"QU$", "[", 
            RowBox[{ r, ",", RowBox[{ name, "[", RowBox[{ r, ",", cond}], "]"}]}],
             "]"}], fmt]
    ]
standardGlobalQuantifier[ args___] := unexpected[ standardGlobalQuantifier, {args}]

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
	
	
(* ::Section:: *)
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

makeRangeSequence[RowBox[{s_,",",r__}]] :=
    Sequence[ makeRangeSequence[s], ",", makeRangeSequence[RowBox[{r}]]]

makeRangeSequence[RowBox[{s_}]] :=
    makeRangeSequence[s]

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


makeRangeBox[ (RNG$|Theorema`Computation`Language`RNG$)[ s:(SIMPRNG$|Theorema`Computation`Language`SIMPRNG$)[_]..], fmt_] := RowBox[ Riffle[ Map[ makeRangeBox[ #, fmt]&, {s}], ","]]
makeRangeBox[ (RNG$|Theorema`Computation`Language`RNG$)[ s__], fmt_] := GridBox[ Map[ {makeRangeBox[ #, fmt]}&, {s}]]
makeRangeBox[ (SETRNG$|Theorema`Computation`Language`SETRNG$)[ v_, s_], fmt_] := RowBox[ {MakeBoxes[v, fmt], "\[Element]", MakeBoxes[ s, fmt]}]
makeRangeBox[ (PREDRNG$|Theorema`Computation`Language`PREDRNG$)[ v_, p_], fmt_] := RowBox[ {MakeBoxes[ p, fmt], "[", MakeBoxes[v, fmt], "]"}]
makeRangeBox[ (STEPRNG$|Theorema`Computation`Language`STEPRNG$)[ v_, lower_, upper_, step_], fmt_] := 
	RowBox[ {RowBox[ {MakeBoxes[v, fmt], "=", MakeBoxes[ lower, fmt]}], ",", makeEllipsisBox[ step, fmt], ",", MakeBoxes[ upper, fmt]}]
makeRangeBox[ (SIMPRNG$|Theorema`Computation`Language`SIMPRNG$)[ v_], fmt_] := MakeBoxes[ v, fmt]
makeRangeBox[args___] := unexpected[ makeRangeBox, {args}]

makeEllipsisBox[ 1, fmt_] := "\[Ellipsis]"
makeEllipsisBox[ step_, fmt_] := OverscriptBox[ "\[Ellipsis]", MakeBoxes[ step, fmt]]
makeEllipsisBox[ args___] := unexpected[ makeEllipsisBox, {args}]

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

MakeRangeSequence[RowBox[{i_, ",", j__,",",n      RowBox[{k_, "=", lower_}], ",", "\[Ellipsis]", ",", upper_}]]:=Sequence[RowBox[{"\[Bullet]integerRange","[",i,",",lower,",",upper,"]"}],",",MakeRangeSequence[RowBox[{j,",",n      RowBox[{k, "=", lower}], ",", "\[Ellipsis]", ",", upper}]]]

MakeRangeSequence[RowBox[{j_, ",", n      RowBox[{k_, "=", lower_}], ",", "\[Ellipsis]", ",", upper_}]]:=Sequence[RowBox[{"\[Bullet]integerRange","[",j,",",lower,",",upper,"]"}],",",RowBox[{"\[Bullet]integerRange","[",k,",",lower,",",upper,"]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,"=",lower_}],",","\[Ellipsis]",",",upper_}]]:=n	RowBox[{"\[Bullet]integerRange","[",k,",",lower,",",upper,"]"}]

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,"=",lower_}],",","\[Ellipsis]"}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",i,",",lower,",","\[Infinity]","]"}],",",MakeRangeSequence[RowBox[{j,",",RowBox[{k,"=",lower}],",","\[Ellipsis]"}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,"=",lower_}],",","\[Ellipsis]"}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",j,",",lower,",","\[Infinity]","]"}],",",RowBox[{"\[Bullet]integerRange","[",k,",",lower,",","\[Infinity]","]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,"=",lower_}],",","\[Ellipsis]"}]]:=n	RowBox[{"\[Bullet]integerRange","[",k,",",lower,",","\[Infinity]","]"}]

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,"=","\[Ellipsis]"}],",",upper_}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",i,",",RowBox[{"-", "\[Infinity]"}],",",upper,"]"}],",",MakeRangeSequence[RowBox[{j,",",RowBox[{k,"=","\[Ellipsis]"}],",",upper}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,"=","\[Ellipsis]"}],",",upper_}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",j,",",RowBox[{"-", "\[Infinity]"}],",",upper,"]"}],",",RowBox[{"\[Bullet]integerRange","[",k,",",RowBox[{"-", "\[Infinity]"}],",",upper,"]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,"=","\[Ellipsis]"}],",",upper_}]]:=n	RowBox[{"\[Bullet]integerRange","[",k,",",RowBox[{"-", "\[Infinity]"}],",",upper,"]"}]

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,"=","\[Ellipsis]"}]}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",i,",",RowBox[{"-", "\[Infinity]"}],",","\[Infinity]","]"}],",",nMakeRangeSequence[RowBox[{j,",",RowBox[{k,"=","\[Ellipsis]"}]}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,"=","\[Ellipsis]"}]}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",j,",",RowBox[{"-", "\[Infinity]"}],",","\[Infinity]","]"}],",",n	RowBox[{"\[Bullet]integerRange","[",k,",",RowBox[{"-", "\[Infinity]"}],",","\[Infinity]","]"}]]

MakeRangeSequence[RowBox[{k_,"=","\[Ellipsis]"}]]:=n	RowBox[{"\[Bullet]integerRange","[",k,",",RowBox[{"-", "\[Infinity]"}],",","\[Infinity]","]"}]

SetAttributes[\[Bullet]\[Bullet]domainRange,HoldFirst];

\[Bullet]domainRange::usage="\[Bullet]domainRange[i,domain,lower,upper] denotes that the variable `i` ranges over all elements of the enumerable domain `domain` from `lower` to `upper`.";

\[Bullet]\[Bullet]domainRange::usage="\[Bullet]\[Bullet]domainRange[i,domain,lower,upper] denotes that the variable `i` ranges over all elements of the enumerable domain `domain` from `lower` to `upper`.";

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","\[Ellipsis]",",",upper_}]]:=Sequence[RowBox[{"\[Bullet]domainRange","[",i,",",domain,",",lower,",",upper,"]"}],",",MakeRangeSequence[RowBox[{j,",",RowBox[{k,UnderscriptBox["=",domain],lower}],",","\[Ellipsis]",",",upper}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","\[Ellipsis]",",",upper_}]]:=Sequence[RowBox[{"\[Bullet]domainRange","[",j,",",domain,",",lower,",",upper,"]"}],",",RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",lower,",",upper,"]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","\[Ellipsis]",",",upper_}]]:=(DeclareUnderscriptDomain[domain];RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",lower,",",upper,"]"}])

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","\[Ellipsis]"}]]:=Sequence[n		RowBox[{"\[Bullet]domainRange","[",i,",",domain,",",lower,",",RowBox[{domain,"[","Last","]"}],"]"}],",",n		MakeRangeSequence[RowBox[{j,",",RowBox[{k,UnderscriptBox["=",domain],lower}],",","\[Ellipsis]"}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","\[Ellipsis]"}]]:=Sequence[n		RowBox[{"\[Bullet]domainRange","[",j,",",domain,",",lower,",",RowBox[{domain,"[","Last","]"}],"]"}],",",n		RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",lower,",",RowBox[{domain,"[","Last","]"}],"]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","\[Ellipsis]"}]]:=(DeclareUnderscriptDomain[domain];RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",lower,",",RowBox[{domain,"[","Last","]"}],"]"}])

MakeRangeSequence[n		RowBox[{i_,",",j__,",",RowBox[{k_,UnderscriptBox["=",domain_],"\[Ellipsis]"}],",",upper_}]]:=Sequence[n		RowBox[{"\[Bullet]domainRange","[",i,",",domain,",",RowBox[{domain,"[","First","]"}],",",upper,"]"}],",",MakeRangeSequence[n		RowBox[{j,",",RowBox[{k,UnderscriptBox["=",domain],"\[Ellipsis]"}],",",upper}]]]

MakeRangeSequence[n		RowBox[{j_,",",RowBox[{k_,UnderscriptBox["=",domain_],"\[Ellipsis]"}],",",upper_}]]:=Sequence[n		RowBox[{"\[Bullet]domainRange","[",j,",",domain,",",RowBox[{domain,"[","First","]"}],",",upper,"]"}],",",n		RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",RowBox[{domain,"[","First","]"}],",",upper,"]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,UnderscriptBox["=",domain_],"\[Ellipsis]"}],",",upper_}]]:=(DeclareUnderscriptDomain[domain];RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",RowBox[{domain,"[","First","]"}],",",upper,"]"}])

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,UnderscriptBox["=",domain_],"\[Ellipsis]"}]}]]:=Sequence[RowBox[{"\[Bullet]domainRange","[",i,",",domain,",",RowBox[{domain,"[","First","]"}],",",RowBox[{domain,"[","Last","]"}],"]"}],",",MakeRangeSequence[RowBox[{j,",",RowBox[{k,UnderscriptBox["=",domain],"\[Ellipsis]"}]}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,UnderscriptBox["=",domain_],"\[Ellipsis]"}]}]]:=Sequence[RowBox[{"\[Bullet]domainRange","[",j,",",domain,",",RowBox[{domain,"[","First","]"}],",",RowBox[{domain,"[","Last","]"}],"]"}],",",RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",RowBox[{domain,"[","First","]"}],",",RowBox[{domain,"[","Last","]"}],"]"}]]

MakeRangeSequence[RowBox[{k_,UnderscriptBox["=",domain_],"\[Ellipsis]"}]]:=n	(DeclareUnderscriptDomain[domain];RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",RowBox[{domain,"[","First","]"}],",",RowBox[{domain,"[","Last","]"}],"]"}])

SetAttributes[\[Bullet]\[Bullet]limitRange,HoldFirst];

MakeRangeSequence[RowBox[{i_, ",", j__, ",",RowBox[{k_,UnderscriptBox["\[LongRightArrow]"|"\[RightArrow]"|"\[Rule]",dom_], s_}]}]]:=n	Sequence[RowBox[{"\[Bullet]limitRange","[",i,",",s,",",dom,"]"}],",",n		MakeRangeSequence[RowBox[{j,",",RowBox[{k, "\[LongRightArrow]", s}]}]]]

MakeRangeSequence[n    RowBox[{j_, ",", n      RowBox[{k_, UnderscriptBox["\[LongRightArrow]"|"\[RightArrow]"|"\[Rule]",dom_], s_}]}]]:=Sequence[RowBox[{"\[Bullet]limitRange","[",j,",",s,",",dom,"]"}],",",RowBox[{"\[Bullet]limitRange","[",k,",",s,",",dom,"]"}]]

MakeRangeSequence[RowBox[{k_,UnderscriptBox["\[LongRightArrow]"|"\[RightArrow]"|"\[Rule]",dom_],s_}]]:=RowBox[{"\[Bullet]limitRange","[",k,",",s,",",dom,"]"}]

MakeRangeSequence[RowBox[{i_, ",", j__, ",",RowBox[{k_,"\[LongRightArrow]"|"\[RightArrow]"|"\[Rule]", s_}]}]]:=n	Sequence[RowBox[{"\[Bullet]limitRange","[",i,",",s,",","None","]"}],",",n		MakeRangeSequence[RowBox[{j,",",RowBox[{k, "\[LongRightArrow]", s}]}]]]

MakeRangeSequence[n    RowBox[{j_, ",", n      RowBox[{k_, "\[LongRightArrow]"|"\[RightArrow]"|"\[Rule]", s_}]}]]:=Sequence[RowBox[{"\[Bullet]limitRange","[",j,",",s,",","None","]"}],",",RowBox[{"\[Bullet]limitRange","[",k,",",s,",","None","]"}]]

MakeRangeSequence[RowBox[{k_,"\[LongRightArrow]"|"\[RightArrow]"|"\[Rule]",s_}]]:=RowBox[{"\[Bullet]limitRange","[",k,",",s,",","None","]"}]

SetAttributes[\[Bullet]\[Bullet]simpleRange,HoldFirst];


\[Bullet]locval::usage="\[Bullet]locval[x,v] declares `v` as a local value for `x`.";

MakeRangeSequence[RowBox[{x_,"="|"\[LeftArrow]"|"\[LongLeftArrow]",v_}]]:=RowBox[{"\[Bullet]locval","[",RowBox[{x,",",v}],"]"}]

MakeRangeBoxes::usage="MakeRangeBoxes[x,f] produces the nice-looking output for the range 'x' in output form 'f'.";

SetAttributes[MakeRangeBoxes,HoldAll];

MakeRangeBoxes[(\[Bullet]range|\[Bullet]\[Bullet]range)[x_Pattern,y___],f_]:=RowBox[{"(",RowBox[MakePatternRangeBoxes[{x,y},f]],")"}]

MakeRangeBoxes[(\[Bullet]range|\[Bullet]\[Bullet]range)[x:(_[_Pattern,___]),y___],f_]:=RowBox[{"(",RowBox[MakePatternRangeBoxes[{x,y},f]],")"}]

MakeRangeBoxes[(\[Bullet]range|\[Bullet]\[Bullet]range)[x_],f_]:=MakeSingleRangeBoxes[x,f]

MakeRangeBoxes[(\[Bullet]range|\[Bullet]\[Bullet]range)[x:(__\[Bullet]simpleRange|__\[Bullet]\[Bullet]simpleRange)],f_]:=RowBox[MakeSimpleRangeBoxes[{x},f]]

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

MakeSingleRangeBoxes[(\[Bullet]integerRange|\[Bullet]\[Bullet]integerRange)[x_,lower_,upper_],f_]:=RowBox[{RowBox[{MakeBoxes[x,f],"=",MakeBoxes[lower,f]}],",","\[Ellipsis]",",",MakeBoxes[upper,f]}]

MakeSingleRangeBoxes[(\[Bullet]domainRange|\[Bullet]\[Bullet]domainRange)[x_,domain_,lower_,upper_],f_]:=MakeSingleRangeBoxes[\[Bullet]simpleRange[x],f]/;(TypeVar/.SessionContext[x])===\[Bullet]\[Bullet]domainRange[x,domain,lower,upper]

MakeSingleRangeBoxes[(\[Bullet]domainRange|\[Bullet]\[Bullet]domainRange)[x_,domain_,lower_,upper_],f_]:=RowBox[{RowBox[{MakeBoxes[x,f],UnderscriptBox["=",MakeBoxes[domain,f]],MakeBoxes[lower,f]}],",","\[Ellipsis]",",",MakeBoxes[upper,f]}]

MakeSingleRangeBoxes[(\[Bullet]limitRange|\[Bullet]\[Bullet]limitRange)[x_,y_],f_]:=MakeSingleRangeBoxes[\[Bullet]simpleRange[x],f]/;(TypeVar/.SessionContext[x])===\[Bullet]\[Bullet]limitRange[x,y]

MakeSingleRangeBoxes[(\[Bullet]limitRange|\[Bullet]\[Bullet]limitRange)[x_,y_],f_]:=RowBox[{MakeBoxes[x,f],"\[Rule]",MakeBoxes[y,f]}]

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

$ContextPath = Drop[ $ContextPath, -1];

End[];
EndPackage[];

