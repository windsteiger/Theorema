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
     {Equal$TM, Set},
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
		notification[ translate[ "tupleOfRange"], DisplayForm[ makeRangeBox[ r, StandardForm]]];
		Throw[ $Failed]
	]
makeTuple[ x___] := ToExpression[ "Tuple$TM"][x]

(* ::Section:: *)
(* MakeBoxes *)

MakeBoxes[ Set$TM[ arg__], fmt_] := MakeBoxes[ {arg}, fmt]
MakeBoxes[ Set$TM[ ], fmt_] := MakeBoxes[ "\[EmptySet]", fmt]

MakeBoxes[ SequenceOf$TM[ rng:RNG$[ SETRNG$[ v_, _]], cond_, v_], fmt_] :=
	RowBox[ {makeRangeBox[ rng, fmt], "|", MakeBoxes[ cond, fmt]}]

MakeBoxes[ SequenceOf$TM[ rng_, True, form_], fmt_] :=
	RowBox[ {MakeBoxes[ form, fmt], UnderscriptBox[ "|", makeRangeBox[ rng, fmt]]}]

MakeBoxes[ SequenceOf$TM[ rng_, cond_, form_], fmt_] :=
	RowBox[ {MakeBoxes[ form, fmt], UnderscriptBox[ "|", makeRangeBox[ rng, fmt]], MakeBoxes[ cond, fmt]}]

MakeBoxes[ SetOf$TM[ rng_, cond_, form_], fmt_] :=
	RowBox[ { "{", MakeBoxes[ SequenceOf$TM[ rng, cond, form], fmt], "}"}]

MakeBoxes[ TupleOf$TM[ rng_, cond_, form_], fmt_] :=
	RowBox[ { "\[LeftAngleBracket]", MakeBoxes[ SequenceOf$TM[ rng, cond, form], fmt], "\[RightAngleBracket]"}]

MakeBoxes[ IffDef$TM[ l_, r_], fmt_] :=
    RowBox[ {MakeBoxes[ l, fmt],
        TagBox[ RowBox[{":", "\[NegativeThickSpace]\[NegativeThinSpace]", "\[DoubleLongLeftRightArrow]"}], Identity, SyntaxForm->"a\[Implies]b"], 
        MakeBoxes[ r, fmt]}]

MakeBoxes[ VAR$[ v_], fmt_] := StyleBox[ MakeBoxes[ v, fmt], "ExpressionVariable"]

makeRangeBox[ RNG$[ s__SIMPRNG$], fmt_] := RowBox[ Riffle[ Map[ makeRangeBox[ #, fmt]&, {s}], ","]]
makeRangeBox[ RNG$[ s__], fmt_] := GridBox[ Map[ {makeRangeBox[ #, fmt]}&, {s}]]
makeRangeBox[ SETRNG$[ v_, s_], fmt_] := RowBox[ {MakeBoxes[v, fmt], "\[Element]", MakeBoxes[ s, fmt]}]
makeRangeBox[ PREDRNG$[ v_, p_], fmt_] := RowBox[ {MakeBoxes[ p, fmt], "[", MakeBoxes[v, fmt], "]"}]
makeRangeBox[ STEPRNG$[ v_, lower_, upper_, step_], fmt_] := 
	RowBox[ {RowBox[ {MakeBoxes[v, fmt], "=", MakeBoxes[ lower, fmt]}], ",", makeEllipsisBox[ step, fmt], ",", MakeBoxes[ upper, fmt]}]
makeRangeBox[ SIMPRNG$[ v_], fmt_] := MakeBoxes[ v, fmt]
makeRangeBox[args___] := unexpected[ makeRangeBox, {args}]

makeEllipsisBox[ 1, fmt_] := "\[Ellipsis]"
makeEllipsisBox[ step_, fmt_] := OverscriptBox[ "\[Ellipsis]", MakeBoxes[ step, fmt]]
makeEllipsisBox[ args___] := unexpected[ makeEllipsisBox, {args}]
