(* This file is loaded twice:
	1) with "Theorema`Language`" in the context path so that the respective global symbols are taken from that context,
	2) with "Theorema`Computation`Language`" in the context path so that the respective global symbols are taken from that context.
		*)

(* ::Section:: *)
(* Language classification *)

$tmaNonStandardOperators = Join[ $tmaNonStandardOperators,
    {
     {Iff$TM, DoubleRightArrow},
     {EqualDef$TM, SetDelayed},
     {Tuple$TM, AngleBracket}
    }];

(* ::Section:: *)
(* MakeExpression *)

(* ::Subsection:: *)
(* Auxiliary parsing functions *)

makeSet[ SequenceOf$TM[ s__]] := ToExpression[ "SetOf$TM"][ s]
makeSet[ x___] := Apply[ ToExpression[ "Set$TM"], Union[ {x}]]

makeTuple[ SequenceOf$TM[ r:RNG$[ __STEPRNG$], c_, e_]] := ToExpression[ "TupleOf$TM"][ r, c, e]

makeTuple[ SequenceOf$TM[ r_, __]] := 
	Module[ {},
		notification[ translate[ "tupleOfRange"], DisplayForm[ makeRangeBox[ r, TheoremaForm]]];
		Throw[ $Failed]
	]
makeTuple[ x___] := ToExpression[ "Tuple$TM"][x]

(* ::Section:: *)
(* MakeBoxes *)

MakeBoxes[ \[DoubleStruckCapitalN]0$TM, TheoremaForm] := SubscriptBox[ "\[DoubleStruckCapitalN]", "0"]

MakeBoxes[ Set$TM[ arg__], TheoremaForm] := MakeBoxes[ {arg}, TheoremaForm]
MakeBoxes[ Set$TM[ ], TheoremaForm] := MakeBoxes[ "\[EmptySet]", TheoremaForm]

MakeBoxes[ SequenceOf$TM[ rng:RNG$[ SETRNG$[ v_, _]], cond_, v_], TheoremaForm] :=
	RowBox[ {makeRangeBox[ rng, TheoremaForm], "|", MakeBoxes[ cond, TheoremaForm]}]

MakeBoxes[ SequenceOf$TM[ rng_, True, form_], TheoremaForm] :=
	RowBox[ {MakeBoxes[ form, TheoremaForm], UnderscriptBox[ "|", makeRangeBox[ rng, TheoremaForm]]}]

MakeBoxes[ SequenceOf$TM[ rng_, cond_, form_], TheoremaForm] :=
	RowBox[ {MakeBoxes[ form, TheoremaForm], UnderscriptBox[ "|", makeRangeBox[ rng, TheoremaForm]], MakeBoxes[ cond, TheoremaForm]}]

MakeBoxes[ SetOf$TM[ rng_, cond_, form_], TheoremaForm] :=
	RowBox[ { "{", MakeBoxes[ SequenceOf$TM[ rng, cond, form], TheoremaForm], "}"}]

MakeBoxes[ TupleOf$TM[ rng_, cond_, form_], TheoremaForm] :=
	RowBox[ { "\[LeftAngleBracket]", MakeBoxes[ SequenceOf$TM[ rng, cond, form], TheoremaForm], "\[RightAngleBracket]"}]

MakeBoxes[ Abbrev$TM[ rng_, form_], TheoremaForm] :=
	RowBox[ {UnderscriptBox[ "let", makeRangeBox[ rng, TheoremaForm]], MakeBoxes[ form, TheoremaForm]}]

MakeBoxes[ IffDef$TM[ l_, r_], TheoremaForm] :=
    RowBox[ {MakeBoxes[ l, TheoremaForm],
        TagBox[ RowBox[{":", "\[NegativeThickSpace]\[NegativeThinSpace]", "\[DoubleLongLeftRightArrow]"}], Identity, SyntaxForm->"a\[Implies]b"], 
        MakeBoxes[ r, TheoremaForm]}]

MakeBoxes[ VAR$[ v_], TheoremaForm] := StyleBox[ MakeBoxes[ v, TheoremaForm], "ExpressionVariable"]
abfAnnotations = {
	{OverscriptBox, {"_", "^", "~"}}, 
	{SuperscriptBox, {"\[Prime]", "\[Prime]\[Prime]", "\[Prime]\[Prime]\[Prime]"}},
	{UnderscriptBox, {"_", "~"}}};
MakeBoxes[ FIX$[ c_, 0], TheoremaForm] := StyleBox[ MakeBoxes[ c, TheoremaForm], "ExpressionABF"]
MakeBoxes[ FIX$[ c_, n_Integer] /; n<9, TheoremaForm] := 
	Module[{i,j},
		{i,j} = QuotientRemainder[ n-1, 3];
		StyleBox[ abfAnnotations[[i+1,1]][MakeBoxes[ c, TheoremaForm], abfAnnotations[[i+1, 2, j+1]]], "ExpressionABF"]
	]
MakeBoxes[ FIX$[ c_, n_Integer], TheoremaForm] := StyleBox[ SuperscriptBox[ MakeBoxes[ c, TheoremaForm], RowBox[{"(", MakeBoxes[ n, StandardForm], ")"}]], "ExpressionABF"]

metaAnnotations = {"*", "**", "***", "\[Dagger]", "\[DoubleDagger]"};
MakeBoxes[ META$[ c_, n_Integer, dep_List] /; n<5, TheoremaForm] := StyleBox[ SuperscriptBox[ MakeBoxes[ c, TheoremaForm], metaAnnotations[[n+1]]], "ExpressionMeta"]
MakeBoxes[ META$[ c_, n_Integer, dep_List], TheoremaForm] := StyleBox[ SuperscriptBox[ MakeBoxes[ c, TheoremaForm], RowBox[{"(", MakeBoxes[ n, StandardForm], ")"}]], "ExpressionMeta"]

makeRangeBox[ RNG$[ s__SIMPRNG$], fmt_] := RowBox[ Riffle[ Map[ makeRangeBox[ #, fmt]&, {s}], ","]]
makeRangeBox[ RNG$[ s__], fmt_] := GridBox[ Map[ {makeRangeBox[ #, fmt]}&, {s}]]
makeRangeBox[ SETRNG$[ v_, s_], fmt_] := RowBox[ {MakeBoxes[v, fmt], "\[Element]", MakeBoxes[ s, fmt]}]
makeRangeBox[ PREDRNG$[ v_, p_], fmt_] := RowBox[ {MakeBoxes[ p, fmt], "[", MakeBoxes[v, fmt], "]"}]
makeRangeBox[ STEPRNG$[ v_, lower_, upper_, step_], fmt_] := 
	RowBox[ {RowBox[ {MakeBoxes[v, fmt], "=", MakeBoxes[ lower, fmt]}], ",", makeEllipsisBox[ step, fmt], ",", MakeBoxes[ upper, fmt]}]
makeRangeBox[ ABBRVRNG$[ a_, e_], fmt_] := RowBox[ {MakeBoxes[ a, fmt], "=", MakeBoxes[ e, fmt]}]
makeRangeBox[ DOMEXTRNG$[ v_, d_], fmt_] := RowBox[ {MakeBoxes[ v, fmt], "\[Superset]", MakeBoxes[ d, fmt]}]
makeRangeBox[ SIMPRNG$[ v_], fmt_] := MakeBoxes[ v, fmt]
makeRangeBox[args___] := unexpected[ makeRangeBox, {args}]

makeEllipsisBox[ 1, fmt_] := "\[Ellipsis]"
makeEllipsisBox[ step_, fmt_] := OverscriptBox[ "\[Ellipsis]", MakeBoxes[ step, fmt]]
makeEllipsisBox[ args___] := unexpected[ makeEllipsisBox, {args}]


(* ::Section:: *)
(* Global Declarations Display *)

MakeBoxes[ globalForall$TM[ rng_RNG$, True], TheoremaForm] :=
	UnderscriptBox[ "\[ForAll]", makeRangeBox[ rng, TheoremaForm]]
	
MakeBoxes[ globalForall$TM[ rng_RNG$, cond_], TheoremaForm] :=
	UnderscriptBox[ UnderscriptBox[ "\[ForAll]", makeRangeBox[ rng, TheoremaForm]], MakeBoxes[ cond, TheoremaForm]]	
	
MakeBoxes[ globalForall$TM[ rng_RNG$, cond_, form_], TheoremaForm] := 
	MakeBoxes[ Forall$TM[ rng, cond, form], TheoremaForm]

MakeBoxes[ globalImplies$TM[ c_], TheoremaForm] :=
	RowBox[ {MakeBoxes[ c, TheoremaForm], "\[Implies]"}]	

MakeBoxes[ domainConstruct$TM[ _, rng_RNG$], TheoremaForm] :=
	UnderscriptBox[ "domain", makeRangeBox[ rng, TheoremaForm]]	

MakeBoxes[ globalAbbrev$TM[ rng_RNG$], TheoremaForm] :=
	UnderscriptBox[ "let", makeRangeBox[ rng, TheoremaForm]]

