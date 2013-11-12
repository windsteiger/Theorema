(* Theorema 
    Copyright (C) 2010 The Theorema Group

    This file is part of Theorema 2.0
    
    Theorema 2.0 is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Theorema 2.0 is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)


(* This file is loaded twice:
	1) with "Theorema`Language`" in the context path so that the respective global symbols are taken from that context,
	2) with "Theorema`Computation`Language`" in the context path so that the respective global symbols are taken from that context.
*)

(* ::Section:: *)
(* Language classification *)

$tmaNonStandardOperators = Join[ $tmaNonStandardOperators,
    {
     {Iff$TM, DoubleLeftRightArrow},
     {EqualDef$TM, SetDelayed},
     {Tuple$TM, AngleBracket}
    }];

(* ::Section:: *)
(* MakeExpression *)

(* ::Subsection:: *)
(* Auxiliary parsing functions *)

(* The default cases for non-SequenceOf are in Syntax.m, otherwise the defs are in wrong order when
   this file is loaded twice
*)
makeSet[ SequenceOf$TM[ s__]] := ToExpression[ "SetOf$TM"][ s]

makeTuple[ SequenceOf$TM[ r:RNG$[ __STEPRNG$], c_, e_]] := ToExpression[ "TupleOf$TM"][ r, c, e]
makeTuple[ SequenceOf$TM[ r_, __]] := 
	Module[ {},
		notification[ translate[ "tupleOfRange"], DisplayForm[ makeRangeBox[ r, TheoremaForm]]];
		Throw[ $Failed]
	]

(* ::Section:: *)
(* MakeBoxes *)

(* ::Subsection:: *)
(* Number domains *)

MakeBoxes[ IntegerInterval$TM[ 1, DirectedInfinity[1], True, _], TheoremaForm] :=
	"\[DoubleStruckCapitalN]"
MakeBoxes[ IntegerInterval$TM[ l_?NonNegative, DirectedInfinity[1], True, _], TheoremaForm] :=
	SubscriptBox[ "\[DoubleStruckCapitalN]", MakeBoxes[ l, TheoremaForm]]
MakeBoxes[ IntegerInterval$TM[ l_?NonNegative, u_, True, True], TheoremaForm] :=
	SubscriptBox[ "\[DoubleStruckCapitalN]", RowBox[ {MakeBoxes[ l, TheoremaForm], ",", "\[Ellipsis]", ",", MakeBoxes[ u, TheoremaForm]}]]
MakeBoxes[ IntegerInterval$TM[ l_?NonNegative, u_, False, True], TheoremaForm] :=
	SubscriptBox[ "\[DoubleStruckCapitalN]", RowBox[ {RowBox[{"(", RowBox[ {MakeBoxes[ l, TheoremaForm], ",", "\[Ellipsis]", ",", MakeBoxes[ u, TheoremaForm]}]}], "]"}]]
MakeBoxes[ IntegerInterval$TM[ l_?NonNegative, u_, True, False], TheoremaForm] :=
	SubscriptBox[ "\[DoubleStruckCapitalN]", RowBox[ {RowBox[{"[", RowBox[ {MakeBoxes[ l, TheoremaForm], ",", "\[Ellipsis]", ",", MakeBoxes[ u, TheoremaForm]}]}], ")"}]]
MakeBoxes[ IntegerInterval$TM[ l_?NonNegative, u_, False, False], TheoremaForm] :=
	SubscriptBox[ "\[DoubleStruckCapitalN]", RowBox[{"(", RowBox[{MakeBoxes[ l, TheoremaForm], ",", "\[Ellipsis]", ",", MakeBoxes[ u, TheoremaForm]}], ")"}]]
	
MakeBoxes[ IntegerQR$TM[ m_], TheoremaForm] :=
	SubscriptBox[ "\[DoubleStruckCapitalZ]", MakeBoxes[ m, TheoremaForm]]
	
intervalToLetter[ r_Symbol] :=
	Switch[ r,
		Theorema`Language`IntegerInterval$TM, "\[DoubleStruckCapitalZ]",
		Theorema`Language`RationalInterval$TM, "\[DoubleStruckCapitalQ]",
		Theorema`Language`RealInterval$TM, "\[DoubleStruckCapitalR]"
	]

MakeBoxes[ (h:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[ DirectedInfinity[-1], DirectedInfinity[1], _, _], TheoremaForm] :=
	intervalToLetter[ h]
MakeBoxes[ IntegerInterval$TM[ l_, DirectedInfinity[1], True, _], TheoremaForm] :=
	If[ TrueQ[ NonPositive[ l]],
		SubscriptBox[ "\[DoubleStruckCapitalZ]", MakeBoxes[ l, TheoremaForm]],
		SubscriptBox[ "\[DoubleStruckCapitalZ]", RowBox[ {MakeBoxes[ l, TheoremaForm], ",", "\[Ellipsis]", ",", "\[Infinity]"}]]
	]
MakeBoxes[ (h:RationalInterval$TM|RealInterval$TM)[ l_, DirectedInfinity[1], True, _], TheoremaForm] :=
	SubscriptBox[ intervalToLetter[ h], MakeBoxes[ l, TheoremaForm]]
MakeBoxes[ (h:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[ l_, u_, True, True], TheoremaForm] :=
	SubscriptBox[ intervalToLetter[ h], RowBox[ {MakeBoxes[ l, TheoremaForm], ",", "\[Ellipsis]", ",", MakeBoxes[ u, TheoremaForm]}]]
MakeBoxes[ (h:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[ l_, u_, False, True], TheoremaForm] :=
	SubscriptBox[ intervalToLetter[ h], RowBox[ {RowBox[{"(", RowBox[ {MakeBoxes[ l, TheoremaForm], ",", "\[Ellipsis]", ",", MakeBoxes[ u, TheoremaForm]}]}], "]"}]]
MakeBoxes[ (h:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[ l_, u_, True, False], TheoremaForm] :=
	SubscriptBox[ intervalToLetter[ h], RowBox[ {RowBox[{"[", RowBox[ {MakeBoxes[ l, TheoremaForm], ",", "\[Ellipsis]", ",", MakeBoxes[ u, TheoremaForm]}]}], ")"}]]
MakeBoxes[ (h:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[ l_, u_, False, False], TheoremaForm] :=
	SubscriptBox[ intervalToLetter[ h], RowBox[{"(", RowBox[{MakeBoxes[ l, TheoremaForm], ",", "\[Ellipsis]", ",", MakeBoxes[ u, TheoremaForm]}], ")"}]]
	
MakeBoxes[ \[DoubleStruckCapitalC]P$TM, TheoremaForm] :=
	SubscriptBox[ MakeBoxes[ "\[DoubleStruckCapitalC]", TheoremaForm], "P"]
	
	
	
(* ::Subsection:: *)
(* Annotated Operators *)
	
(* ::Subsubsection:: *)
(* annotated operators without arguments *)

MakeBoxes[ Annotated$TM[ op_, SubScript$TM[ sc__]], TheoremaForm] :=
	MakeBoxes[ Subscript[ op, sc], TheoremaForm]
	
MakeBoxes[ Annotated$TM[ op_, SuperScript$TM[ sc_]], TheoremaForm] :=
	MakeBoxes[ Superscript[ op, sc], TheoremaForm]
MakeBoxes[ Annotated$TM[ op_, SuperScript$TM[ sc__]], TheoremaForm] :=
	SuperscriptBox[ MakeBoxes[ op, TheoremaForm], RowBox[ Riffle[ Apply[ List, Map[ makeTmaBoxes, HoldComplete[ sc]]], ","]]]
	
MakeBoxes[ Annotated$TM[ op_, SubScript$TM[ sub_], SuperScript$TM[ sup_]], TheoremaForm] :=
	MakeBoxes[ Subsuperscript[ op, sub, sup], TheoremaForm]
MakeBoxes[ Annotated$TM[ op_, SubScript$TM[ sub__], SuperScript$TM[ sup__]], TheoremaForm] :=
	SubsuperscriptBox[ MakeBoxes[ op, TheoremaForm],
		RowBox[ Riffle[ Apply[ List, Map[ makeTmaBoxes, HoldComplete[ sub]]], ","]],
		RowBox[ Riffle[ Apply[ List, Map[ makeTmaBoxes, HoldComplete[ sup]]], ","]]]
		
MakeBoxes[ Annotated$TM[ op_, OverScript$TM[ sc__]], TheoremaForm] :=
	MakeBoxes[ Overscript[ op, sc], TheoremaForm]

MakeBoxes[ Annotated$TM[ op_, UnderScript$TM[ un_], OverScript$TM[ ov_]], TheoremaForm] :=
	MakeBoxes[ Underoverscript[ op, un, ov], TheoremaForm]
MakeBoxes[ Annotated$TM[ op_, UnderScript$TM[ un__], OverScript$TM[ ov__]], TheoremaForm] :=
	UnderoverscriptBox[ MakeBoxes[ op, TheoremaForm],
		RowBox[ Riffle[ Apply[ List, Map[ makeTmaBoxes, HoldComplete[ un]]], ","]],
		RowBox[ Riffle[ Apply[ List, Map[ makeTmaBoxes, HoldComplete[ ov]]], ","]]]
	
	
(* ::Subsubsection:: *)
(* annotated operators with arguments *)

MakeBoxes[ aop_Annotated$TM[], TheoremaForm] :=
	Module[ {op, symbols, sym = MakeBoxes[ aop, TheoremaForm]},
		RowBox[
			{RowBox[ {TagBox[ "(", "AutoParentheses"], sym, TagBox[ ")", "AutoParentheses"]}], "[", "]"}
		] /; (symbols = Cases[ aop, _Symbol, Infinity, 1];
				Length[ symbols] > 0 && (op = First[ symbols]; isTmaOperatorName[ op]))
	]
MakeBoxes[ aop_Annotated$TM[ a_], TheoremaForm] :=
	Module[ {op, symbols, form, sym = MakeBoxes[ aop, TheoremaForm]},
		(
		form = getTmaOperatorForms[ op];
		Which[
			MemberQ[ form, Prefix],
			RowBox[ {sym, MakeBoxes[ a, TheoremaForm]}],
			MemberQ[ form, Postfix],
			RowBox[ {MakeBoxes[ a, TheoremaForm], sym}],
			True,
			RowBox[ {RowBox[ {TagBox[ "(", "AutoParentheses"], sym, TagBox[ ")", "AutoParentheses"]}],
				"[", MakeBoxes[ a, TheoremaForm], "]"}]
		]
		) /; (symbols = Cases[ aop, _Symbol, Infinity, 1];
				Length[ symbols] > 0 && (op = First[ symbols]; isTmaOperatorName[ op]))
	]
MakeBoxes[ aop_Annotated$TM[ a__], TheoremaForm] :=
	Module[ {op, symbols, form, sym = MakeBoxes[ aop, TheoremaForm]},
		(
		form = getTmaOperatorForms[ op];
		If[ MemberQ[ form, Infix],
			tmaInfixBox[ {a}, sym],
			RowBox[ {RowBox[ {TagBox[ "(", "AutoParentheses"], sym, TagBox[ ")", "AutoParentheses"]}], "[",
								RowBox[ Riffle[ Apply[ List, Map[ makeTmaBoxes, HoldComplete[ a]]], ","]], "]"}]
		]
		) /; (symbols = Cases[ aop, _Symbol, Infinity, 1];
				Length[ symbols] > 0 && (op = First[ symbols]; isTmaOperatorName[ op]))
	]
	

(* ::Subsection:: *)
(* Rest *)

MakeBoxes[ Radical$TM[ e_, 2], TheoremaForm] :=
	SqrtBox[ MakeBoxes[ e, TheoremaForm]]

MakeBoxes[ Radical$TM[ e_, r_], TheoremaForm] :=
	RadicalBox[ MakeBoxes[ e, TheoremaForm], MakeBoxes[ r, TheoremaForm]]

MakeBoxes[ Set$TM[ arg__], TheoremaForm] := MakeBoxes[ {arg}, TheoremaForm]
MakeBoxes[ Set$TM[ ], TheoremaForm] := MakeBoxes[ "\[EmptySet]", TheoremaForm]
(* An unevaluated 'makeSet' will turn into makeSet$TM when renaming back to standard context ... *)
MakeBoxes[ Theorema`Common`makeSet$TM[ arg__], TheoremaForm] := StyleBox[ MakeBoxes[ {arg}, TheoremaForm], "ExpressionVariable"]

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

MakeBoxes[ SEQ0$[ v_], TheoremaForm] := RowBox[ {MakeBoxes[ v, TheoremaForm], "..."}]
MakeBoxes[ SEQ1$[ v_], TheoremaForm] := RowBox[ {MakeBoxes[ v, TheoremaForm], ".."}]
MakeBoxes[ VAR$[ v_?isTmaOperatorName][args___], TheoremaForm] := MakeBoxes[ v[args], TheoremaForm]
MakeBoxes[ VAR$[ v_], TheoremaForm] := StyleBox[ MakeBoxes[ v, TheoremaForm], "ExpressionVariable"]
abfAnnotations = {
	{OverscriptBox, {"_", "^", "~"}}, 
	{SuperscriptBox, {"\[Prime]", "\[Prime]\[Prime]", "\[Prime]\[Prime]\[Prime]"}},
	{UnderscriptBox, {"_", "~"}}};
(* We only convert the 0-th a.b.f. operator into Infix/Prefix/Postifx form, because otherwise the abfAnnotations don't work. *)
MakeBoxes[ FIX$[ c_?isTmaOperatorName, 0][args___], TheoremaForm] := MakeBoxes[ c[args], TheoremaForm]
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

MakeBoxes[ r_RNG$, TheoremaForm] := makeRangeBox[ r, TheoremaForm]
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

MakeBoxes[ CaseDistinction$TM[ c__], TheoremaForm] :=
    RowBox[ {"\[Piecewise]",
        GridBox[ Map[ formatClause, {c}]]}]

formatClause[ Clause$TM[ c_, e_]] := {MakeBoxes[ e, TheoremaForm], "\[DoubleLeftArrow]", MakeBoxes[ c, TheoremaForm]}


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

