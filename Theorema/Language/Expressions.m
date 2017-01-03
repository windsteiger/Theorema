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

(* Default value for operations defined in a domain. Necessary for extension domains. *)
opDefInDom[ _] := {}

(* ::Section:: *)
(* Language classification *)

(* Uncomment the two commented 'MakeBoxes' definitions in "Syntax.m" when adding non-standard operators. *)
$tmaNonStandardOperators = Join[ $tmaNonStandardOperators, {}];
    
    
(* ::Section:: *)
(* Sequence expressions *)

(* 'sequenceType[ expr]' returns the "sequence-type" of the given expression, as a pair of the form '{n, exact}' (or '$Failed' if the expression is ill-typed).
	- '{n, True}' means that 'expr' is a sequence of length 'n' (if 'n' is 1, it is an individual expression), and
	- '{n, False}' means that 'expr' is a sequence of length *at least* 'n'.
	Remark: This function would probably better fit into "FormulaManipulation.m", but we implement it here because then the various symbols are automatically
	interpreted in both contexts.
*)
sequenceType[ HoldComplete[ VAR$[ (_Symbol)|{___, _Symbol}, ___]]] :=
	{1, True}
sequenceType[ HoldComplete[ VAR$[ (SEQ0$[ ___])|{___, SEQ0$[ ___]}, ___]]] :=
	{0, False}
sequenceType[ HoldComplete[ VAR$[ (SEQ1$[ ___])|{___, SEQ1$[ ___]}, ___]]] :=
	{1, False}
sequenceType[ HoldComplete[ (FIX$|META$)[ _Symbol, ___]]] :=
	{1, True}
sequenceType[ HoldComplete[ (FIX$|META$)[ _SEQ0$, ___]]] :=
	{0, False}
sequenceType[ HoldComplete[ (FIX$|META$)[ _SEQ1$, ___]]] :=
	{1, False}
sequenceType[ HoldComplete[ SEQ$[ exprs___]]] :=
	Module[ {len = 0, exact = True},
		Catch[
			Scan[
				With[ {t = sequenceType[ #]},
					If[ t === $Failed,
						Throw[ $Failed],
					(*else*)
						len += First[ t];
						exact = exact && Last[ t]
					]
				]&,
				HoldComplete /@ HoldComplete[ exprs]
			];
			Throw[ {len, exact}]
		]
	]
sequenceType[ HoldComplete[ DomainOperation$TM[ _, op_]]] :=
	If[ sequenceType[ op] === {1, True},
		{1, True},
		$Failed
	]
sequenceType[ HoldComplete[ Annotated$TM[ op_, ___]]] :=
	If[ sequenceType[ op] === {1, True},
		{1, True},
		$Failed
	]
sequenceType[ HoldComplete[ h_[ args___]]] :=
	sequenceType[ HoldComplete[ h]]
sequenceType[ HoldComplete[ FIX$|META$|SEQ$|SEQ0$|SEQ1$|VAR$]] :=
	$Failed
sequenceType[ HoldComplete[ _]] :=
	{1, True}
sequenceType[ HoldComplete[]] :=
	{0, True}
sequenceType[ HoldComplete[a_, b__]] :=
	sequenceType[ HoldComplete[ SEQ$[ a, b]]]
sequenceType[ Hold[ expr___]] :=
	sequenceType[ HoldComplete[ expr]]
sequenceType[ expr___] :=
	sequenceType[ HoldComplete[ expr]]


(* ::Section:: *)
(* MakeBoxes *)


(* ::Subsection:: *)
(* Quantifiers *)

(* Quantifiers without condition are displayed as quantifiers whose condition is 'True'. *)
MakeBoxes[ q_[ rng_RNG$, form_], TheoremaForm] :=
	MakeBoxes[ q[ rng, True, form], TheoremaForm]

MakeBoxes[ Annotated$TM[ TAG$[ q_, t_], SubScript$TM[ sub_]][ rng_RNG$, cond_, form_], TheoremaForm] :=
	makeQuantifierBox[ q, rng, form, cond, sub, t, TheoremaForm]
MakeBoxes[ DomainOperation$TM[ dom_, TAG$[ q_, t_]][ rng_RNG$, cond_, form_], TheoremaForm] :=
	makeQuantifierBox[ q, rng, form, cond, dom, t, TheoremaForm]
MakeBoxes[ TAG$[ q_, t_][ rng_RNG$, cond_, form_], TheoremaForm] :=
	makeQuantifierBox[ q, rng, form, cond, Null, t, TheoremaForm]
MakeBoxes[ Annotated$TM[ q_, SubScript$TM[ sub_]][ rng_RNG$, cond_, form_], TheoremaForm] :=
	makeQuantifierBox[ q, rng, form, cond, sub, Null, TheoremaForm]
MakeBoxes[ DomainOperation$TM[ dom_, q_][ rng_RNG$, cond_, form_], TheoremaForm] :=
	makeQuantifierBox[ q, rng, form, cond, dom, Null, TheoremaForm]
MakeBoxes[ q_[ rng_RNG$, cond_, form_], TheoremaForm] :=
	makeQuantifierBox[ q, rng, form, cond, Null, Null, TheoremaForm]

makeQuantifierBox[ q_, rng_RNG$, form_, cond_, sub_, tag_, fmt_] :=
	With[ {b0 = Replace[ q, $tmaNameToQuantifier], r = makeRangeBox[ rng, fmt], f = MakeBoxes[ form, fmt]},
	With[ {b1 = If[ MatchQ[ b0, {_, _}], If[ sub === Null, Insert[ b0, "|", 2], q], b0]},
	With[ {b2 = addTagToQuantifierBox[ If[ b1 === q, MakeBoxes[ q, fmt], b1], tag, TAG$]},
	With[ {b = If[ sub === Null, b2, SubscriptBox[ b2, MakeBoxes[ sub, fmt]]]},
		Which[
			MatchQ[ b, {_, _, _}],
			RowBox[
				{
					First[ b],
					Which[
						MatchQ[ {rng, form}, {RNG$[ SETRNG$[ v_, _]], v_}],
						RowBox[ {r, b[[2]], MakeBoxes[ cond, fmt]}],
						
						cond === True,
						RowBox[ {f, UnderscriptBox[ b[[2]], r]}],
						
						True,
						RowBox[ {f, UnderscriptBox[ b[[2]], r], MakeBoxes[ cond, fmt]}]
					],
					Last[ b]
				}
			],

			cond === True,
			RowBox[ {UnderscriptBox[ b, r], f}],
			
			True,
			RowBox[ {UnderscriptBox[ UnderscriptBox[ b, r], MakeBoxes[ cond, fmt]], f}]
		]
	]]]]
makeQuantifierBox[args___] := unexpected[ makeQuantifierBox, {args}]

(* We must explicitly pass 'TAG$' to 'addTagToQuantifierBox', since the definition in "Computation`"-context
	overwrites the one in "Language`"-context. *)
addTagToQuantifierBox[ box_, Null, _] := box
addTagToQuantifierBox[ {left_, middle_, right_}, tag_, h_] :=
	{tmaTagBox[ Left, left, tag, h], tmaTagBox[ None, middle, tag, h], tmaTagBox[ Right, right, tag, h]}
addTagToQuantifierBox[ box_, tag_, h_] :=
	tmaTagBox[ None, box, tag, h]

(* It is not possible to tag a range as a whole. *)
MakeBoxes[ r_RNG$, TheoremaForm] :=
	makeRangeBox[ r, TheoremaForm]
	
makeRangeBox[ RNG$[ s_], fmt_] :=
	makeRangeBox[ s, fmt]
makeRangeBox[ RNG$[ s__SIMPRNG$], fmt_] :=
	RowBox[ Riffle[ Map[ makeRangeBox[ #, fmt]&, {s}], ","]]
makeRangeBox[ RNG$[ s__], fmt_] :=
	GridBox[ Map[ {makeRangeBox[ #, fmt]}&, {s}]]
makeRangeBox[ TAG$[ rng_, tag_], fmt_] :=
	tmaTagBox[ None, makeRangeBox[ rng, fmt], tag, TAG$]
makeRangeBox[ SETRNG$[ v_, s_], fmt_] :=
	RowBox[ {MakeBoxes[v, fmt], "\[Element]", MakeBoxes[ s, fmt]}]
makeRangeBox[ PREDRNG$[ v_, p_], fmt_] :=
	RowBox[ {MakeBoxes[ p, fmt], "[", MakeBoxes[v, fmt], "]"}]
makeRangeBox[ STEPRNG$[ v_, lower_, upper_, step_], fmt_] :=
	RowBox[ {RowBox[ {MakeBoxes[v, fmt], "=", MakeBoxes[ lower, fmt]}], ",", makeEllipsisBox[ step, fmt], ",", MakeBoxes[ upper, fmt]}]
makeRangeBox[ ABBRVRNG$[ a_, e_, ___], fmt_] :=
	RowBox[ {MakeBoxes[ a, fmt], "=", MakeBoxes[ e, fmt]}]
makeRangeBox[ DOMEXTRNG$[ v_, d_], fmt_] :=
	RowBox[ {MakeBoxes[ v, fmt], "\[Superset]", MakeBoxes[ d, fmt]}]
makeRangeBox[ SIMPRNG$[ v_], fmt_] :=
	MakeBoxes[ v, fmt]
makeRangeBox[ r_, fmt_] :=
	With[ {b = Replace[ {r, fmt}, $tmaUserRangeToBox]},
		If[ ListQ[ b],
			MakeBoxes[ r, fmt],
		(*else*)
			b
		]
	]
makeRangeBox[ args___] := unexpected[ makeRangeBox, {args}]

makeEllipsisBox[ 1, fmt_] := "\[Ellipsis]"
makeEllipsisBox[ step_, fmt_] := OverscriptBox[ "\[Ellipsis]", MakeBoxes[ step, fmt]]
makeEllipsisBox[ args___] := unexpected[ makeEllipsisBox, {args}]
	
	
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
	
MakeBoxes[ IntegerQuotientRing$TM[ m_], TheoremaForm] :=
	SubscriptBox[ "\[DoubleStruckCapitalZ]", MakeBoxes[ m, TheoremaForm]]
MakeBoxes[ IntegerQuotientRingPM$TM[ m_], TheoremaForm] :=
	SubsuperscriptBox[ "\[DoubleStruckCapitalZ]", MakeBoxes[ m, TheoremaForm], "\[PlusMinus]"]
	
intervalToLetter[ r_Symbol] :=
	Switch[ r,
		Theorema`Language`IntegerInterval$TM|Theorema`Computation`Language`IntegerInterval$TM, "\[DoubleStruckCapitalZ]",
		Theorema`Language`RationalInterval$TM|Theorema`Computation`Language`RationalInterval$TM, "\[DoubleStruckCapitalQ]",
		Theorema`Language`RealInterval$TM|Theorema`Computation`Language`RealInterval$TM, "\[DoubleStruckCapitalR]"
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
	SubscriptBox[ "\[DoubleStruckCapitalC]", "P"]
	
	
	
(* ::Subsection:: *)
(* Annotated Operators *)
	
(* ::Subsubsection:: *)
(* annotated operators without arguments *)

(* It does not make sense to tag "Annotated$TM", "SubScript$TM" etc. *)

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
	With[ {opName = getTmaOperatorName[ aop], sym = MakeBoxes[ aop, TheoremaForm]},
		If[ getTmaOperatorForms[ opName] === {},
			RowBox[ {sym, "[", "]"}],
		(*else*)
			RowBox[
				{RowBox[ {TagBox[ "(", "AutoParentheses"], sym, TagBox[ ")", "AutoParentheses"]}], "[", "]"}
			]
		] /; opName =!= $Failed
	]
MakeBoxes[ aop_Annotated$TM[ a_], TheoremaForm] :=
	With[ {opName = getTmaOperatorName[ aop], sym = MakeBoxes[ aop, TheoremaForm]},
		With[ {form = getTmaOperatorForms[ opName]},
			Which[
				MemberQ[ form, Prefix],
				RowBox[ {sym, MakeBoxes[ a, TheoremaForm]}],
				MemberQ[ form, Postfix],
				RowBox[ {MakeBoxes[ a, TheoremaForm], sym}],
				form =!= {},
				RowBox[ {RowBox[ {TagBox[ "(", "AutoParentheses"], sym, TagBox[ ")", "AutoParentheses"]}],
					"[", MakeBoxes[ a, TheoremaForm], "]"}],
				True,
				RowBox[ {sym, "[", MakeBoxes[ a, TheoremaForm], "]"}]
			]
		] /; opName =!= $Failed
	]
MakeBoxes[ aop_Annotated$TM[ a__], TheoremaForm] :=
	With[ {opName = getTmaOperatorName[ aop], sym = MakeBoxes[ aop, TheoremaForm]},
		With[ {form = getTmaOperatorForms[ opName]},
			Which[
				MemberQ[ form, Infix],
				tmaInfixBox[ HoldComplete[ a], sym],
				form =!= {},
				RowBox[ {RowBox[ {TagBox[ "(", "AutoParentheses"], sym, TagBox[ ")", "AutoParentheses"]}], "[",
									tmaInfixBox[ HoldComplete[ a], ","], "]"}],
				True,
				RowBox[ {sym, "[", tmaInfixBox[ HoldComplete[ a], ","], "]"}]
			]
		] /; opName =!= $Failed
	]
	
(* ::Subsection:: *)
(* Domain underscripts *)

(* It does not make sense to tag "DomainOperation$TM". *)

MakeBoxes[ DomainOperation$TM[ dom_, op_], TheoremaForm] :=
	UnderscriptBox[ MakeBoxes[ op, TheoremaForm], MakeBoxes[ dom, TheoremaForm]]

MakeBoxes[ (d:(DomainOperation$TM[ dom_, op_]))[], TheoremaForm] :=
	With[ {opName = getTmaOperatorName[ op], box = MakeBoxes[ d, TheoremaForm]},
		If[ opName === $Failed,
		(* no (annotated) Theorema operator *)
			RowBox[ {box, "[", "]"}],
		(* (annotated) Theorema operator *)
			If[ getTmaOperatorForms[ opName] === {},
				RowBox[ {box, "[", "]"}],
			(*else*)
				RowBox[ {RowBox[ {TagBox[ "(", "AutoParentheses"], box, TagBox[ ")", "AutoParentheses"]}], "[", "]"}]
			]
		]
	]
MakeBoxes[ (d:(DomainOperation$TM[ dom_, op_]))[ a_], TheoremaForm] :=
	With[ {opName = getTmaOperatorName[ op],
			opBox = MakeBoxes[ d, TheoremaForm],
			aBox = MakeBoxes[ a, TheoremaForm]},
		If[ opName === $Failed || op === Element$TM || MatchQ[ op, TAG$[ Element$TM, ___]],	(* we don't want to wrap parentheses around the domain-membership predicate *)
		(* no (annotated) Theorema operator *)
			RowBox[ {opBox, "[", aBox, "]"}],
		(* (annotated) Theorema operator *)
			With[ {form = getTmaOperatorForms[ opName]},
				Which[
					MemberQ[ form, Prefix],
					RowBox[ {opBox, aBox}],
					MemberQ[ form, Postfix],
					RowBox[ {aBox, opBox}],
					form === {},
					RowBox[ {opBox, "[", aBox, "]"}],
					True,
					RowBox[ {RowBox[ {TagBox[ "(", "AutoParentheses"], opBox, TagBox[ ")", "AutoParentheses"]}], "[", aBox, "]"}]
				]
			]
		]
	]
MakeBoxes[ (d:(DomainOperation$TM[ dom_, op_]))[ a__], TheoremaForm] :=
	With[ {opName = getTmaOperatorName[ op], box = MakeBoxes[ d, TheoremaForm]},
		If[ opName === $Failed,
		(* no (annotated) Theorema operator *)
			RowBox[ {box, "[", RowBox[ Riffle[ Apply[ List, Map[ makeTmaBoxes, HoldComplete[ a]]], ","]], "]"}],
		(* (annotated) Theorema operator *)
			With[ {form = getTmaOperatorForms[ opName]},
				Which[
					MemberQ[ form, Infix],
					tmaInfixBox[ HoldComplete[ a], box],
					form === {},
					RowBox[ {box, "[", RowBox[ Riffle[ Apply[ List, Map[ makeTmaBoxes, HoldComplete[ a]]], ","]], "]"}],
					True,
					RowBox[ {RowBox[ {TagBox[ "(", "AutoParentheses"], box, TagBox[ ")", "AutoParentheses"]}], "[",
						RowBox[ Riffle[ Apply[ List, Map[ makeTmaBoxes, HoldComplete[ a]]], ","]], "]"}]
				]
			]
		]
	]
	
	
(* ::Subsection:: *)
(* Brackets *)

(* special brackets *)
Scan[
	With[ {left = #[[3]], right = #[[4]], name = #[[5]]},
		With[ {sym = If[ StringMatchQ[ name, __ ~~ ("$"|"$TM")], ToExpression[ name], ToExpression[ name <> "$TM"]]},
			MakeBoxes[ sym[ e___], TheoremaForm] :=
				RowBox[
					{
						TagBox[ left, Identity, SyntaxForm -> "("],
						tmaInfixBox[ HoldComplete[ e], ","],
						TagBox[ right, Identity, SyntaxForm -> ")"]
					}
				];
			MakeBoxes[ TAG$[ sym, t_][ e___], TheoremaForm] :=
				RowBox[
					{
						tmaTagBox[ Left, left, t, TAG$],
						tmaInfixBox[ HoldComplete[ e], ","],
						tmaTagBox[ Right, right, t, TAG$]
					}
				]
		]
	]&,
	specialBrackets
]

(* standard brackets; require only rules for pretty-printing *)
Scan[
	With[ {sym = First[ #], left = #[[2]], right = #[[3]]},
		If[ Last[ #],
			MakeBoxes[ sym[ e___], TheoremaForm] :=
				RowBox[
					{left, tmaInfixBox[ HoldComplete[ e], ","], right}	(* no 'TagBox[ ..., SyntaxForm -> "("]' necessary *)
				]
		];
		MakeBoxes[ TAG$[ sym, t_][ e___], TheoremaForm] :=
			RowBox[
				{
					tmaTagBox[ Left, left, t, TAG$],
					tmaInfixBox[ HoldComplete[ e], ","],
					tmaTagBox[ Right, right, t, TAG$]
				}
			]
	]&,
	{
		{List$TM, "{", "}", False},
		{BracketingBar$TM, "\[LeftBracketingBar]", "\[RightBracketingBar]", False},
		{DoubleBracketingBar$TM, "\[LeftDoubleBracketingBar]", "\[RightDoubleBracketingBar]", False},
		{Tuple$TM, "\[LeftAngleBracket]", "\[RightAngleBracket]", True},
		{Floor$TM, "\[LeftFloor]", "\[RightFloor]", True},
		{Ceiling$TM, "\[LeftCeiling]", "\[RightCeiling]", True}
	}
]

MakeBoxes[ TAG$[ Part$TM, t_][ h_, p___], TheoremaForm] :=
	RowBox[
		{
			MakeBoxes[ h, TheoremaForm],
			tmaTagBox[ Left, "\[LeftDoubleBracket]", t, TAG$],
			tmaInfixBox[ HoldComplete[ p], ","],
			tmaTagBox[ Right, "\[RightDoubleBracket]", t, TAG$]
		}
	]


(* ::Subsection:: *)
(* Rest *)

MakeBoxes[ Radical$TM[ e_, 2], TheoremaForm] :=
	SqrtBox[ MakeBoxes[ e, TheoremaForm]]

MakeBoxes[ Radical$TM[ e_, r_], TheoremaForm] :=
	RadicalBox[ MakeBoxes[ e, TheoremaForm], MakeBoxes[ r, TheoremaForm]]

MakeBoxes[ TAG$[ Set$TM, t_][ arg__], TheoremaForm] :=
	RowBox[ {tmaTagBox[ Left, "{", t, TAG$], tmaInfixBox[ HoldComplete[ arg], ","], tmaTagBox[ Right, "}", t, TAG$]}]
MakeBoxes[ TAG$[ Set$TM, t_][ ], TheoremaForm] := tmaTagBox[ None, "\[EmptySet]", t, TAG$]
MakeBoxes[ Set$TM[ arg__], TheoremaForm] :=
	RowBox[ {"{", tmaInfixBox[ HoldComplete[ arg], ","], "}"}]
MakeBoxes[ Set$TM[ ], TheoremaForm] := "\[EmptySet]"

MakeBoxes[ TAG$[ IffDef$TM, t_][ l_, r_], TheoremaForm] :=
	RowBox[
		{
			MakeBoxes[ l, TheoremaForm],
			tmaTagBox[ Infix, RowBox[ {":", "\[NegativeThickSpace]\[NegativeThinSpace]", "\[DoubleLongLeftRightArrow]"}], t, TAG$, ":="],
        	MakeBoxes[ r, TheoremaForm]
        }
	]
MakeBoxes[ IffDef$TM[ l_, r_], TheoremaForm] :=
	RowBox[
		{
			MakeBoxes[ l, TheoremaForm],
        	TagBox[ RowBox[ {":", "\[NegativeThickSpace]\[NegativeThinSpace]", "\[DoubleLongLeftRightArrow]"}], Identity, SyntaxForm -> "a:=b"], 
        	MakeBoxes[ r, TheoremaForm]
        }
	]

MakeBoxes[ TAG$[ Componentwise$TM, t_][ P_, args___], TheoremaForm] :=
    RowBox[ {MakeBoxes[ P, TheoremaForm], tmaTagBox[ Infix, "@", t, TAG$], MakeBoxes[ SEQ$[ args], TheoremaForm]}]
MakeBoxes[ Componentwise$TM[ P_, args___], TheoremaForm] :=
    RowBox[ {MakeBoxes[ P, TheoremaForm], "@", MakeBoxes[ SEQ$[ args], TheoremaForm]}]

MakeBoxes[ OperatorChain$TM[ args___], TheoremaForm] :=
    RowBox[ List @@ (makeTmaBoxes /@ HoldComplete[ args])]

MakeBoxes[ TAG$[ EmptyUpTriangle$TM, t_][ a_, b_], TheoremaForm] :=
	RowBox[ {MakeBoxes[ a, TheoremaForm], tmaTagBox[ Infix, "\[EmptyUpTriangle]", t, TAG$, "\[Union]"], MakeBoxes[ b, TheoremaForm]}]
MakeBoxes[ EmptyUpTriangle$TM[ a_, b_], TheoremaForm] :=
	RowBox[ {MakeBoxes[ a, TheoremaForm], "\[EmptyUpTriangle]", MakeBoxes[ b, TheoremaForm]}]

MakeBoxes[ TAG$[ Insert$TM, t_][ a_, b_, c_], TheoremaForm] :=
	SubscriptBox[ MakeBoxes[ a, TheoremaForm], RowBox[ {MakeBoxes[ b, TheoremaForm], tmaTagBox[ Infix, "\[RightArrow]", t, TAG$], MakeBoxes[ c, TheoremaForm]}]]
MakeBoxes[ Insert$TM[ a_, b_, c_], TheoremaForm] :=
	SubscriptBox[ MakeBoxes[ a, TheoremaForm], RowBox[ {MakeBoxes[ b, TheoremaForm], "\[RightArrow]", MakeBoxes[ c, TheoremaForm]}]]

MakeBoxes[ TAG$[ DeleteAt$TM, t_][ a_, b_], TheoremaForm] :=
	SubscriptBox[ MakeBoxes[ a, TheoremaForm], RowBox[ {MakeBoxes[ b, TheoremaForm], tmaTagBox[ Postfix, "\[LeftArrow]", t, TAG$]}]]
MakeBoxes[ DeleteAt$TM[ a_, b_], TheoremaForm] :=
	SubscriptBox[ MakeBoxes[ a, TheoremaForm], RowBox[ {MakeBoxes[ b, TheoremaForm], "\[LeftArrow]"}]]

MakeBoxes[ TAG$[ Delete$TM, t_][ a_, b__], TheoremaForm] :=
	With[ {box = tmaTagBox[ Postfix, "\[LeftArrowBar]", t, TAG$]},
		SubscriptBox[ MakeBoxes[ a, TheoremaForm], RowBox[ Riffle[ List @@ Replace[ HoldComplete[ b], x_ :> {MakeBoxes[ x, TheoremaForm], box}, {1}], ","]]]
	]
MakeBoxes[ Delete$TM[ a_, b__], TheoremaForm] :=
	SubscriptBox[ MakeBoxes[ a, TheoremaForm], RowBox[ Riffle[ List @@ Replace[ HoldComplete[ b], x_ :> {MakeBoxes[ x, TheoremaForm], "\[LeftArrowBar]"}, {1}], ","]]]

MakeBoxes[ TAG$[ Replace$TM, t_][ a_, p:Tuple$TM[ _, _]..], TheoremaForm] :=
	SubscriptBox[ MakeBoxes[ a, TheoremaForm], makeTupleOperationBox[ HoldComplete[ p], tmaTagBox[ Infix, "\[LeftArrowBar]", t, TAG$]]]
MakeBoxes[ Replace$TM[ a_, p:Tuple$TM[ _, _]..], TheoremaForm] :=
	SubscriptBox[ MakeBoxes[ a, TheoremaForm], makeTupleOperationBox[ HoldComplete[ p], "\[LeftArrowBar]"]]

MakeBoxes[ TAG$[ ReplacePart$TM, t_][ a_, p:Tuple$TM[ _, _]..], TheoremaForm] :=
	SubscriptBox[ MakeBoxes[ a, TheoremaForm], makeTupleOperationBox[ HoldComplete[ p], tmaTagBox[ Infix, "\[LeftArrow]", t, TAG$]]]
MakeBoxes[ ReplacePart$TM[ a_, p:Tuple$TM[ _, _]..], TheoremaForm] :=
	SubscriptBox[ MakeBoxes[ a, TheoremaForm], makeTupleOperationBox[ HoldComplete[ p], "\[LeftArrow]"]]

makeTupleOperationBox[ p_HoldComplete, box_] :=
	RowBox[
		Riffle[
			List @@ Replace[ p, _[ l_, r_] :> RowBox[ {MakeBoxes[ l, TheoremaForm], box, MakeBoxes[ r, TheoremaForm]}], {1}],
			","
		]
	]

(* It does not make sense to tag "SEQ$", "VAR$", etc. *)

MakeBoxes[ SEQ$[], TheoremaForm] :=
	RowBox[ {TagBox[ "\[VerticalEllipsis]", Identity, SyntaxForm -> "("], TagBox[ "\[VerticalEllipsis]", Identity, SyntaxForm -> ")"]}]
MakeBoxes[ SEQ$[ a_], TheoremaForm] :=
	MakeBoxes[ a, TheoremaForm]
MakeBoxes[ SEQ$[ a_, b__], TheoremaForm] :=
	RowBox[ {
		TagBox[ "\[VerticalEllipsis]", Identity, SyntaxForm -> "("],
		RowBox[ Riffle[ List @@ Replace[ HoldComplete[ a, b], x_ :> MakeBoxes[ x, TheoremaForm], {1}], ","]],
		TagBox[ "\[VerticalEllipsis]", Identity, SyntaxForm -> ")"]
	}]
MakeBoxes[ SEQ0$[ v_], TheoremaForm] := RowBox[ {MakeBoxes[ v, TheoremaForm], "..."}]
MakeBoxes[ SEQ1$[ v_], TheoremaForm] := RowBox[ {MakeBoxes[ v, TheoremaForm], ".."}]
MakeBoxes[ VAR$[ v_Symbol][ args___], TheoremaForm] :=
	Module[ {n},
		MakeBoxes@@Append[ applyHold[ ToExpression[ n, InputForm, Hold], Hold[ args]], TheoremaForm] /;
		With[ {m = Quiet[ Check[ SymbolName[ v], $Failed]]},
			m =!= $Failed && isTmaOperatorString[ n = removeVar[ m], False]
		]
	]
MakeBoxes[ VAR$[ v_], TheoremaForm] := StyleBox[ MakeBoxes@@Append[ removeVar[ v], TheoremaForm], "ExpressionVariable"]
abfAnnotations = {
	{OverscriptBox, {"_", "^", "~"}}, 
	{SuperscriptBox, {"\[Prime]", "\[Prime]\[Prime]", "\[Prime]\[Prime]\[Prime]"}},
	{UnderscriptBox, {"_", "~"}}};
(* We only convert the 0-th a.b.f. operator into Infix/Prefix/Postifx form, because otherwise the abfAnnotations don't work. *)
MakeBoxes[ FIX$[ c_Symbol, 0][args___], TheoremaForm] :=
	Module[ {n},
		MakeBoxes@@Append[ applyHold[ ToExpression[ n, InputForm, Hold], Hold[ args]], TheoremaForm] /;
		With[ {m = Quiet[ Check[ SymbolName[ c], $Failed]]},
			m =!= $Failed && isTmaOperatorString[ n = removeVar[ m], False]
		]
	]
MakeBoxes[ FIX$[ c_, 0], TheoremaForm] := StyleBox[ MakeBoxes@@Append[ removeVar[ c], TheoremaForm], "ExpressionABF"]
MakeBoxes[ FIX$[ c_, n_Integer] /; n<9, TheoremaForm] := 
	Module[{i,j},
		{i,j} = QuotientRemainder[ n-1, 3];
		StyleBox[ abfAnnotations[[i+1,1]][ MakeBoxes@@Append[ removeVar[ c], TheoremaForm], abfAnnotations[[i+1, 2, j+1]]], "ExpressionABF"]
	]
MakeBoxes[ FIX$[ c_, n_Integer], TheoremaForm] := StyleBox[ SuperscriptBox[ MakeBoxes@@Append[ removeVar[ c], TheoremaForm], RowBox[{"(", MakeBoxes[ n, StandardForm], ")"}]], "ExpressionABF"]

metaAnnotations = {"*", "**", "***", "\[Dagger]", "\[DoubleDagger]"};
MakeBoxes[ META$[ c_, n_Integer, dep_List] /; n<5, TheoremaForm] := StyleBox[ SuperscriptBox[ MakeBoxes@@Append[ removeVar[ c], TheoremaForm], metaAnnotations[[n+1]]], "ExpressionMeta"]
MakeBoxes[ META$[ c_, n_Integer, dep_List], TheoremaForm] := StyleBox[ SuperscriptBox[ MakeBoxes@@Append[ removeVar[ c], TheoremaForm], RowBox[{"(", MakeBoxes[ n, StandardForm], ")"}]], "ExpressionMeta"]

MakeBoxes[ TAG$[ CompoundExpression$TM, t_][ a_, b__], TheoremaForm] :=
    tmaInfixBox[ HoldComplete[ a, b], tmaTagBox[ Postfix, ";", t, TAG$], parenthesize]

MakeBoxes[ TAG$[ Piecewise$TM, t_][ Tuple$TM[ c__Tuple$TM]], TheoremaForm] :=
    RowBox[ {tmaTagBox[ Prefix, "\[Piecewise]", t, TAG$], GridBox[ Map[ formatClause, {c}]]}]
MakeBoxes[ TAG$[ Piecewise$TM, t_][ Tuple$TM[ c__Tuple$TM], d_], TheoremaForm] :=
    RowBox[ {tmaTagBox[ Prefix, "\[Piecewise]", t, TAG$],
        GridBox[ Append[ Map[ formatClause, {c}], {MakeBoxes[ d, TheoremaForm], "\[DoubleLeftArrow]", "otherwise"}]]}]
MakeBoxes[ Piecewise$TM[ Tuple$TM[ c__Tuple$TM]], TheoremaForm] :=
    RowBox[ {"\[Piecewise]", GridBox[ Map[ formatClause, {c}]]}]
MakeBoxes[ Piecewise$TM[ Tuple$TM[ c__Tuple$TM], d_], TheoremaForm] :=
    RowBox[ {"\[Piecewise]",
        GridBox[ Append[ Map[ formatClause, {c}], {MakeBoxes[ d, TheoremaForm], "\[DoubleLeftArrow]", "otherwise"}]]}]

formatClause[ Tuple$TM[ e_, c_]] := {MakeBoxes[ e, TheoremaForm], "\[DoubleLeftArrow]", MakeBoxes[ c, TheoremaForm]}


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

