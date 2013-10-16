(* Theorema 
    Copyright (C) 2010 The Theorema Group

    This file is part of Theorema.2
    
    Theorema.2 is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Theorema.2 is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

BeginPackage["Theorema`Language`Syntax`"];

Needs["Theorema`Common`"]

Begin["`Private`"]

theoremaDisplay[ expr_] := DisplayForm[ theoremaBoxes[ expr]]
theoremaDisplay[ args___] := unexpected[ theoremaDisplay, {args}]

theoremaBoxes[ expr_] := stripOutermostParen[ ToBoxes[ expr, TheoremaForm]]
theoremaBoxes[ args___] := unexpected[ theoremaBoxes, {args}]

(* The ToBoxes sometimes produces parentheses also around the entire expression. This is the place to remove them before display *)
stripOutermostParen[ FormBox[ RowBox[ {TagBox["(", "AutoParentheses"], e___, TagBox[")", "AutoParentheses"]}], TheoremaForm]] := e
stripOutermostParen[ e_] := e
stripOutermostParen[ args___] := unexpected[ stripOutermostParen, {args}]


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
     {"\[Sum]", "SumOf"},
     {"\[Product]", "ProductOf"},
     {"\[Integral]", "IntegralOf"},
     {"\[CurlyEpsilon]", "Such"},
     {"such", "Such"},
     {"the", "SuchUnique"},
     {"max", "MaximumOf"},
     {"min", "MinimumOf"}
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


(* In the following list,
	- the first element of each item is the symbol of the operator,
	- the second element is a list of possible syntax of the operator according to Mathematica,
	- the third element is the full name of the operator.
	Note that the second elements are not needed so far, but I think it is good to keep them for possible future use.
	Also note that the meaning of Infix/Prefix/Postfix is the following:
		If operator "?" with name "f" has "Infix" as possible syntax, then any expression of the form "a?b" is
		automatically transformed into "f[a, b]" (by Mathematica), whereas "a?" and "?b" would result in syntax
		errors. This behaviour is NOT affected by the Theorema parsing rules, which only transform "?"
		(without arguments) into "f".
	*)
$tmaOperators = {
	{"/@", {Infix}, "Map"}, {"//@", {Infix}, "MapAll"},
	{"@@", {Infix}, "Apply"}, {";;", {Infix}, "Span"},
	{"\[Rule]", {Infix}, "Rule"}, {"\[RuleDelayed]", {Infix}, "RuleDelayed"},
	{"\[VerticalTilde]", {Infix}, "VerticalTilde"}, {"\[VerticalBar]", {Infix}, "VerticalBar"},
	{"\[NotVerticalBar]", {Infix}, "NotVerticalBar"}, {"\[DoubleVerticalBar]", {Infix}, "DoubleVerticalBar"},
	{"\[NotDoubleVerticalBar]", {Infix}, "NotDoubleVerticalBar"}, {"\[UpTee]", {Infix}, "UpTee"},
	{"\[DownTee]", {Infix}, "DownTee"}, {"\[RightVector]", {Infix}, "RightVector"},
	{"\[LeftVector]", {Infix}, "LeftVector"}, {"\[LeftRightVector]", {Infix}, "LeftRightVector"},
	{"\[DownRightVector]", {Infix}, "DownRightVector"}, {"\[DownLeftVector]", {Infix}, "DownLeftVector"},
	{"\[DownLeftRightVector]", {Infix}, "DownLeftRightVector"}, {"\[RightTeeVector]", {Infix}, "RightTeeVector"},
	{"\[LeftTeeVector]", {Infix}, "LeftTeeVector"}, {"\[DownRightTeeVector]", {Infix}, "DownRightTeeVector"},
	{"\[DownLeftTeeVector]", {Infix}, "DownLeftTeeVector"}, {"\[RightVectorBar]", {Infix}, "RightVectorBar"},
	{"\[LeftVectorBar]", {Infix}, "LeftVectorBar"}, {"\[DownRightVectorBar]", {Infix}, "DownRightVectorBar"},
	{"\[DownLeftVectorBar]", {Infix}, "DownLeftVectorBar"}, {"\[Equilibrium]", {Infix}, "Equilibrium"},
	{"\[ReverseEquilibrium]", {Infix}, "ReverseEquilibrium"}, {"\[LeftUpVector]", {Infix}, "LeftUpVector"},
	{"\[LeftDownVector]", {Infix}, "LeftDownVector"}, {"\[LeftUpDownVector]", {Infix}, "LeftUpDownVector"},
	{"\[RightUpVector]", {Infix}, "RightUpVector"}, {"\[RightDownVector]", {Infix}, "RightDownVector"},
	{"\[RightUpDownVector]", {Infix}, "RightUpDownVector"}, {"\[LeftUpTeeVector]", {Infix}, "LeftUpTeeVector"},
	{"\[LeftDownTeeVector]", {Infix}, "LeftDownTeeVector"}, {"\[RightUpTeeVector]", {Infix}, "RightUpTeeVector"},
	{"\[RightDownTeeVector]", {Infix}, "RightDownTeeVector"}, {"\[LeftUpVectorBar]", {Infix}, "LeftUpVectorBar"},
	{"\[LeftDownVectorBar]", {Infix}, "LeftDownVectorBar"}, {"\[RightUpVectorBar]", {Infix}, "RightUpVectorBar"},
	{"\[RightDownVectorBar]", {Infix}, "RightDownVectorBar"}, {"\[DownLeftVectorBar]", {Infix}, "DownLeftVectorBar"},
	{"\[UpEquilibrium]", {Infix}, "UpEquilibrium"}, {"\[ReverseUpEquilibrium]", {Infix}, "ReverseUpEquilibrium"},
	{"\[RightArrow]", {Infix}, "RightArrow"}, {"\[LeftArrow]", {Infix}, "LeftArrow"},
	{"\[LeftRightArrow]", {Infix}, "LeftRightArrow"}, {"\[LongRightArrow]", {Infix}, "LongRightArrow"},
	{"\[LongLeftArrow]", {Infix}, "LongLeftArrow"}, {"\[LongLeftRightArrow]", {Infix}, "LongLeftRightArrow"},
	{"\[ShortRightArrow]", {Infix}, "ShortRightArrow"}, {"\[ShortLeftArrow]", {Infix}, "ShortLeftArrow"},
	{"\[RightTeeArrow]", {Infix}, "RightTeeArrow"}, {"\[LeftTeeArrow]", {Infix}, "LeftTeeArrow"},
	{"\[RightArrowBar]", {Infix}, "RightArrowBar"}, {"\[LeftArrowBar]", {Infix}, "LeftArrowBar"},
	{"\[DoubleRightArrow]", {Infix}, "DoubleRightArrow"}, {"\[DoubleLeftArrow]", {Infix}, "DoubleLeftArrow"},
	{"\[DoubleLeftRightArrow]", {Infix}, "DoubleLeftRightArrow"}, {"\[DoubleLongRightArrow]", {Infix}, "DoubleLongRightArrow"},
	{"\[DoubleLongLeftArrow]", {Infix}, "DoubleLongLeftArrow"}, {"\[DoubleLongLeftRightArrow]", {Infix}, "DoubleLongLeftRightArrow"},
	{"\[DownArrow]", {Infix}, "DownArrow"}, {"\[UpDownArrow]", {Infix}, "UpDownArrow"},
	{"\[UpTeeArrow]", {Infix}, "UpTeeArrow"}, {"\[DownTeeArrow]", {Infix}, "DownTeeArrow"},
	{"\[UpArrowBar]", {Infix}, "UpArrowBar"}, {"\[DownArrowBar]", {Infix}, "DownArrowBar"},
	{"\[DoubleUpArrow]", {Infix}, "DoubleUpArrow"}, {"\[DoubleDownArrow]", {Infix}, "DoubleDownArrow"},
	{"\[DoubleUpDownArrow]", {Infix}, "DoubleUpDownArrow"}, {"\[RightArrowLeftArrow]", {Infix}, "RightArrowLeftArrow"},
	{"\[LeftArrowRightArrow]", {Infix}, "LeftArrowRightArrow"}, {"\[UpArrowDownArrow]", {Infix}, "UpArrowDownArrow"},
	{"\[DownArrowUpArrow]", {Infix}, "DownArrowUpArrow"}, {"\[LowerRightArrow]", {Infix}, "LowerRightArrow"},
	{"\[LowerLeftArrow]", {Infix}, "LowerLeftArrow"}, {"\[UpperLeftArrow]", {Infix}, "UpperLeftArrow"},
	{"\[UpperRightArrow]", {Infix}, "UpperRightArrow"}, {"++", {Postfix}, "Increment"},
	{"--", {Postfix}, "Decrement"}, {"!", {Postfix}, "Factorial"},
	{"!!", {Postfix}, "Factorial2"}, {"<>", {Infix}, "StringJoin"},
	{"^", {Infix}, "Power"}, {"\[Del]", {Prefix}, "Del"},
	{"\[Square]", {Prefix}, "Square"}, {"\[SmallCircle]", {Infix}, "SmallCircle"},
	{"\[CircleDot]", {Infix}, "CircleDot"}, {"**", {Infix}, "NonCommutativeMultiply"},
	{"\[Cross]", {Infix}, "Cross"}, {".", {Infix}, "Dot"},
	{"+", {Infix, Prefix}, "Plus"}, {"\[PlusMinus]", {Infix, Prefix}, "PlusMinus"},
	{"\[MinusPlus]", {Infix, Prefix}, "MinusPlus"}, {"\[Diamond]", {Infix}, "Diamond"},
	{"\[CircleTimes]", {Infix, Prefix}, "CircleTimes"}, {"\[CenterDot]", {Infix}, "CenterDot"},
	{"*", {Infix}, "Times"}, {"\[Times]", {Infix}, "Times"},
	{"\[Star]", {Infix}, "Star"}, {"\[Coproduct]", {Infix, Prefix}, "Coproduct"},
	{"\[CirclePlus]", {Infix}, "CirclePlus"}, {"\[CircleMinus]", {Infix}, "CircleMinus"},
	{"-", {Infix, Prefix}, "Subtract"}, {"/", {Infix}, "Divide"},
	{"\[Conjugate]", {Postfix}, "Conjugate"}, {"\[Transpose]", {Postfix}, "Transpose"},
	{"\[ConjugateTranspose]", {Postfix}, "ConjugateTranspose"}, {"\[HermitianConjugate]", {Postfix}, "HermitianConjugate"},
	{"\[Backslash]", {Infix}, "Backslash"}, {"\[Intersection]", {Infix}, "Intersection"},
	{"\[Union]", {Infix}, "Union"}, {"\[UnionPlus]", {Infix}, "UnionPlus"},
	{"\[SquareIntersection]", {Infix}, "SquareIntersection"}, {"\[SquareUnion]", {Infix}, "SquareUnion"},
	{"\[Element]", {Infix}, "Element"}, {"\[NotElement]", {Infix}, "NotElement"},
	{"\[ReverseElement]", {Infix}, "ReverseElement"}, {"\[NotReverseElement]", {Infix}, "NotReverseElement"},
	{"\[Subset]", {Infix}, "Subset"}, {"\[NotSubset]", {Infix}, "NotSubset"},
	{"\[Superset]", {Infix}, "Superset"}, {"\[NotSuperset]", {Infix}, "NotSuperset"},
	{"\[SubsetEqual]", {Infix}, "SubsetEqual"}, {"\[NotSubsetEqual]", {Infix}, "NotSubsetEqual"},
	{"\[SupersetEqual]", {Infix}, "SupersetEqual"}, {"\[NotSupersetEqual]", {Infix}, "NotSupersetEqual"},
	{">=", {Infix}, "GreaterEqual"}, {"\[GreaterEqual]", {Infix}, "GreaterEqual"},
	{"\[NotGreaterEqual]", {Infix}, "NotGreaterEqual"}, {"\[GreaterSlantEqual]", {Infix}, "GreaterEqual"},
	{"\[NotGreaterSlantEqual]", {Infix}, "NotGreaterSlantEqual"}, {"\[GreaterFullEqual]", {Infix}, "GreaterFullEqual"},
	{"\[NotGreaterFullEqual]", {Infix}, "NotGreaterFullEqual"}, {"\[GreaterTilde]", {Infix}, "GreaterTilde"},
	{"\[NotGreaterTilde]", {Infix}, "NotGreaterTilde"}, {"\[GreaterGreater]", {Infix}, "GreaterGreater"},
	{"\[NotGreaterGreater]", {Infix}, "NotGreaterGreater"}, {"\[NestedGreaterGreater]", {Infix}, "NestedGreaterGreater"},
	{"\[NotNestedGreaterGreater]", {Infix}, "NotNestedGreaterGreater"}, {">", {Infix}, "Greater"},
	{"\[NotGreater]", {Infix}, "NotGreater"}, {"<=", {Infix}, "LessEqual"},
	{"\[LessEqual]", {Infix}, "LessEqual"}, {"\[NotLessEqual]", {Infix}, "NotLessEqual"},
	{"\[LessSlantEqual]", {Infix}, "LessEqual"}, {"\[NotLessSlantEqual]", {Infix}, "NotLessSlantEqual"},
	{"\[LessFullEqual]", {Infix}, "LessFullEqual"}, {"\[NotLessFullEqual]", {Infix}, "NotLessFullEqual"},
	{"\[LessTilde]", {Infix}, "LessTilde"}, {"\[NotLessTilde]", {Infix}, "NotLessTilde"},
	{"\[LessLess]", {Infix}, "LessLess"}, {"\[NotLessLess]", {Infix}, "NotLessLess"},
	{"\[NestedLessLess]", {Infix}, "NestedLessLess"}, {"\[NotNestedLessLess]", {Infix}, "NotNestedLessLess"},
	{"<", {Infix}, "Less"}, {"\[NotLess]", {Infix}, "NotLess"},
	{"\[GreaterLess]", {Infix}, "GreaterLess"}, {"\[NotGreaterLess]", {Infix}, "NotGreaterLess"},
	{"\[LessGreater]", {Infix}, "LessGreater"}, {"\[NotLessGreater]", {Infix}, "NotLessGreater"},
	{"\[GreaterEqualLess]", {Infix}, "GreaterEqualLess"}, {"\[LessEqualGreater]", {Infix}, "LessEqualGreater"},
	{"\[Succeeds]", {Infix}, "Succeeds"}, {"\[NotSucceeds]", {Infix}, "NotSucceeds"},
	{"\[SucceedsEqual]", {Infix}, "SucceedsEqual"}, {"\[NotSucceedsEqual]", {Infix}, "NotSucceedsEqual"},
	{"\[SucceedsSlantEqual]", {Infix}, "SucceedsSlantEqual"}, {"\[NotSucceedsSlantEqual]", {Infix}, "NotSucceedsSlantEqual"},
	{"\[SucceedsTilde]", {Infix}, "SucceedsTilde"}, {"\[NotSucceedsTilde]", {Infix}, "NotSucceedsTilde"},
	{"\[Precedes]", {Infix}, "Precedes"}, {"\[NotPrecedes]", {Infix}, "NotPrecedes"},
	{"\[PrecedesEqual]", {Infix}, "PrecedesEqual"}, {"\[NotPrecedesEqual]", {Infix}, "NotPrecedesEqual"},
	{"\[PrecedesSlantEqual]", {Infix}, "PrecedesSlantEqual"}, {"\[NotPrecedesSlantEqual]", {Infix}, "NotPrecedesSlantEqual"},
	{"\[PrecedesTilde]", {Infix}, "PrecedesTilde"}, {"\[NotPrecedesTilde]", {Infix}, "NotPrecedesTilde"},
	{"\[RightTriangle]", {Infix}, "RightTriangle"}, {"\[NotRightTriangle]", {Infix}, "NotRightTriangle"},
	{"\[RightTriangleEqual]", {Infix}, "RightTriangleEqual"}, {"\[NotRightTriangleEqual]", {Infix}, "NotRightTriangleEqual"},
	{"\[RightTriangleBar]", {Infix}, "RightTriangleBar"}, {"\[NotRightTriangleBar]", {Infix}, "NotRightTriangleBar"},
	{"\[LeftTriangle]", {Infix}, "LeftTriangle"}, {"\[NotLeftTriangle]", {Infix}, "NotLeftTriangle"},
	{"\[LeftTriangleEqual]", {Infix}, "LeftTriangleEqual"}, {"\[NotLeftTriangleEqual]", {Infix}, "NotLeftTriangleEqual"},
	{"\[LeftTriangleBar]", {Infix}, "LeftTriangleBar"}, {"\[NotLeftTriangleBar]", {Infix}, "NotLeftTriangleBar"},
	{"\[SquareSuperset]", {Infix}, "SquareSuperset"}, {"\[NotSquareSuperset]", {Infix}, "NotSquareSuperset"},
	{"\[SquareSupersetEqual]", {Infix}, "SquareSupersetEqual"}, {"\[NotSquareSupersetEqual]", {Infix}, "NotSquareSupersetEqual"},
	{"\[SquareSubset]", {Infix}, "SquareSubset"}, {"\[NotSquareSubset]", {Infix}, "NotSquareSubset"},
	{"\[SquareSubsetEqual]", {Infix}, "SquareSubsetEqual"}, {"\[NotSquareSubsetEqual]", {Infix}, "NotSquareSubsetEqual"},
	{"=", {Infix}, "Set"}, {":=", {Infix}, "SetDelayed"},
	{"\[Equal]", {Infix}, "Equal"}, {"==", {Infix}, "Equal"},
	{"\[LongEqual]", {Infix}, "Equal"}, {"!=", {Infix}, "Unequal"},
	{"\[NotEqual]", {Infix}, "Unequal"}, {"===", {Infix}, "SameQ"},
	{"=!=", {Infix}, "UnsameQ"}, {"\[Congruent]", {Infix}, "Congruent"},
	{"\[NotCongruent]", {Infix}, "NotCongruent"}, {"\[Tilde]", {Infix}, "Tilde"},
	{"\[NotTilde]", {Infix}, "NotTilde"}, {"\[TildeTilde]", {Infix}, "TildeTilde"},
	{"\[NotTildeTilde]", {Infix}, "NotTildeTilde"}, {"\[TildeEqual]", {Infix}, "TildeEqual"},
	{"\[NotTildeEqual]", {Infix}, "NotTildeEqual"}, {"\[TildeFullEqual]", {Infix}, "TildeFullEqual"},
	{"\[NotTildeFullEqual]", {Infix}, "NotTildeFullEqual"}, {"\[EqualTilde]", {Infix}, "EqualTilde"},
	{"\[NotEqualTilde]", {Infix}, "NotEqualTilde"}, {"\[HumpEqual]", {Infix}, "HumpEqual"},
	{"\[NotHumpEqual]", {Infix}, "NotHumpEqual"}, {"\[HumpDownHump]", {Infix}, "HumpDownHump"},
	{"\[NotHumpDownHump]", {Infix}, "NotHumpDownHump"}, {"\[DotEqual]", {Infix}, "DotEqual"},
	{"\[Proportional]", {Infix}, "Proportional"}, {"\[Proportion]", {Infix}, "Proportion"},
	{"\[Vee]", {Infix}, "Vee"}, {"\[Wedge]", {Infix}, "Wedge"},
	{"\[Or]", {Infix}, "Or"}, {"\[And]", {Infix}, "And"},
	{"\[Not]", {Prefix}, "Not"}, {"\[Xor]", {Infix}, "Xor"},
	{"\[Nand]", {Infix}, "Nand"}, {"\[Nor]", {Infix}, "Nor"},
	{"\[Implies]", {Infix}, "Implies"}, {"\[Therefore]", {Infix}, "Therefore"},
	{"\[Because]", {Infix}, "Because"}, {"\[RightTee]", {Infix}, "RightTee"},
	{"\[LeftTee]", {Infix}, "LeftTee"}, {"\[DoubleRightTee]", {Infix}, "DoubleRightTee"},
	{"\[DoubleLeftTee]", {Infix}, "DoubleLeftTee"}, {"\[SuchThat]", {Infix}, "SuchThat"}};
	
$tmaOperatorSymbols = Map[ First, $tmaOperators];
(* We must not add contexts (like "Theorema`Knowledge`" etc.) to the operator names, as it is done with quantifiers,
	because some of them (like "Plus") appear in context "Theorema`Language`". Copying each of the more than 200
	operator names 4 times (for the 4 possible contexts) seems to be a bit too inefficient. *)
$tmaOperatorNames = Map[ (Last[#] <> "$TM")&, $tmaOperators];
$tmaOperatorToName = Dispatch[ Map[ Rule[ First[#], Last[#]] &, $tmaOperators]];
$tmaNameToOperator = Dispatch[ MapThread[ Rule, {$tmaOperatorNames, $tmaOperatorSymbols}]];

(* We need this attribute, because otherwise expressions (not only operator symbols!) are evaluated when "MakeBoxes" is called. *)	
SetAttributes[ isTmaOperatorName, HoldAllComplete];
isTmaOperatorSymbol[ op_String] := MemberQ[ $tmaOperatorSymbols, op]
isTmaOperatorName[ op_Symbol] := Quiet[ Check[ MemberQ[ $tmaOperatorNames, SymbolName[ op]], False]]


(* ::Section:: *)
(* Expression categories *)

isQuantifierFormula[ e_] := MatchQ[ e, _Forall$TM|_Exists$TM]
isQuantifierFormula[ args___] := unexpected[ isQuantifierFormula, {args}]

isConnectiveFormula[ e_] := MatchQ[ e, _Not$TM|_And$TM|_Or$TM|_Implies$TM|_Iff$TM|_IffDef$TM]
isConnectiveFormula[ args___] := unexpected[ isConnectiveFormula, {args}]

isAtomicExpression[ e_] := !isQuantifierFormula[ e] && !isConnectiveFormula[ e]
isAtomicExpression[ args___] := unexpected[ isAtomicExpression, {args}]


(* ::Section:: *)
(* Set and tuple constructor *)


(*
	Expression specific parts -> Expression.m
	The default cases go here, otherwise it is not save that these are put at the end (if they have conditions,
	they could stay in front of the rules loaded in "Computation`". Keep in mind that Expression.m is loaded twice!
*)

makeSet[ x___] /; isVariableFree[ {x}] := Apply[ ToExpression[ "Set$TM"], Union[ {x}]]
makeTuple[ x___] := ToExpression[ "Tuple$TM"][x]



(* ::Section:: *)
(* MakeExpression *)


MakeExpression[RowBox[{a_, TagBox[op_, Identity, ___], b_}], fmt_] := 
	MakeExpression[RowBox[{a, op, b}], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

MakeExpression[RowBox[{ TagBox[ "(", "AutoParentheses"], expr_, TagBox[ ")", "AutoParentheses"]}], fmt_] := 
	MakeExpression[ expr, fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
	
	
(* ::Subsubsection:: *)
(* Sequence Variables *)

MakeExpression[ RowBox[{a_, "..."}], fmt_] :=
	MakeExpression[ RowBox[{"SEQ0$", "[", a, "]"}], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
	
MakeExpression[ RowBox[{a_, ".."}], fmt_] :=
	MakeExpression[ RowBox[{"SEQ1$", "[", a, "]"}], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals


(* ::Subsubsection:: *)
(* Quantifiers *)


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

MakeExpression[ RowBox[{UnderscriptBox[ SubscriptBox[ q_?isQuantifierSymbol, dom_], rng_], form_}], fmt_] :=
    subscriptedQuantifier[ Replace[ q, $tmaQuantifierToName], rng, "True", dom, form, fmt]/; $parseTheoremaExpressions

MakeExpression[ RowBox[{UnderscriptBox[ UnderscriptBox[ SubscriptBox[ q_?isQuantifierSymbol, dom_], rng_], cond_], form_}], fmt_] :=
    subscriptedQuantifier[ Replace[ q, $tmaQuantifierToName], rng, cond, dom, form, fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[{UnderoverscriptBox[ q:"\[Sum]"|"\[Product]", low:RowBox[{_, "=", _}], high_], form_}], fmt_] :=
    standardQuantifier[ Replace[ q, $tmaQuantifierToName], RowBox[{low, ",", "\[Ellipsis]", ",", high}], "True", form, fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[{UnderscriptBox[ UnderoverscriptBox[ q:"\[Sum]"|"\[Product]", low:RowBox[{_, "=", _}], high_], cond_], form_}], fmt_] :=
    standardQuantifier[ Replace[ q, $tmaQuantifierToName], RowBox[{low, ",", "\[Ellipsis]", ",", high}], cond, form, fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[{UnderoverscriptBox[ SubscriptBox[ q:"\[Sum]"|"\[Product]", dom_], low:RowBox[{_, "=", _}], high_], form_}], fmt_] :=
    subscriptedQuantifier[ Replace[ q, $tmaQuantifierToName], RowBox[{low, ",", "\[Ellipsis]", ",", high}], "True", dom, form, fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[{UnderscriptBox[ UnderoverscriptBox[ SubscriptBox[ q:"\[Sum]"|"\[Product]", dom_], low:RowBox[{_, "=", _}], high_], cond_], form_}], fmt_] :=
    subscriptedQuantifier[ Replace[ q, $tmaQuantifierToName], RowBox[{low, ",", "\[Ellipsis]", ",", high}], cond, dom, form, fmt] /; $parseTheoremaExpressions
   
MakeExpression[ RowBox[{UnderscriptBox[ "let", rng_], form_}], fmt_] :=
	(* We use the powerful toRangeBox in order to have the many variants, multiranges, etc. However, only ABBRVRNG$ makes sense in a "let",
	   but we do not consider it a syntax error to use one of the other ranges *)
     With[ {r = toRangeBox[ rng]},
		MakeExpression[ RowBox[{"QU$", "[", 
            RowBox[{ r, ",", RowBox[{ "Abbrev", "[", RowBox[{ r, ",", form}], "]"}]}], "]"}], 
        fmt]
     ] /; $parseTheoremaExpressions

(* ::Subsubsection:: *)
(* Special arithmetic *)

(* we do not want that a-b is automatically converted to a+(-b), this should only be under built-in subtract. *)

MakeExpression[ RowBox[ {a_, "-", b_, c___}], fmt_] := MakeExpression[ RowBox[ {RowBox[ {"Subtract", "[", a, ",", b, "]"}], c}], fmt] /; $parseTheoremaExpressions
MakeExpression[ RowBox[ {a_, "/", b_, c___}], fmt_] := MakeExpression[ RowBox[ {RowBox[ {"Divide", "[", a, ",", b, "]"}], c}], fmt] /; $parseTheoremaExpressions
MakeExpression[ FractionBox[ a_, b_], fmt_] := MakeExpression[ RowBox[ {"Divide", "[", a, ",", b, "]"}], fmt] /; $parseTheoremaExpressions
MakeExpression[ SqrtBox[ a_], fmt_] := MakeExpression[ RowBox[ {"Radical", "[", a, ",", 2, "]"}], fmt] /; $parseTheoremaExpressions
MakeExpression[ RadicalBox[ a_, b_], fmt_] := MakeExpression[ RowBox[ {"Radical", "[", a, ",", b, "]"}], fmt] /; $parseTheoremaExpressions

(* ::Subsubsection:: *)
(* Special connectives *)


MakeExpression[ RowBox[{left_, RowBox[{":", "\[NegativeThickSpace]\[NegativeThinSpace]", "\[DoubleLongLeftRightArrow]"}], right_}], fmt_] :=
    MakeExpression[ RowBox[{"IffDef", "[", RowBox[{left, ",", right}], "]"}], fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[{"\[Piecewise]", GridBox[ c:{{_, "\[DoubleLeftArrow]"|"\[DoubleLongLeftArrow]", _}..}, ___]}], fmt_] :=
	With[ {clauses = Riffle[ Map[ row2clause, c], ","]},
    	MakeExpression[ RowBox[{"CaseDistinction", "[", RowBox[ clauses], "]"}], fmt]
	] /; $parseTheoremaExpressions

row2clause[ {e_, "\[DoubleLeftArrow]"|"\[DoubleLongLeftArrow]", "otherwise"}] := RowBox[ {"Clause", "[", RowBox[ {"True", ",", e}], "]"}]
row2clause[ {e_, "\[DoubleLeftArrow]"|"\[DoubleLongLeftArrow]", "\[Placeholder]"}] := RowBox[ {"Clause", "[", RowBox[ {"True", ",", e}], "]"}]
row2clause[ {e_, "\[DoubleLeftArrow]"|"\[DoubleLongLeftArrow]", c_}] := RowBox[ {"Clause", "[", RowBox[ {c, ",", e}], "]"}]

MakeExpression[ RowBox[ {"\[And]", RowBox[{"\[Piecewise]", GridBox[ c:{{_}..}, ___]}]}], fmt_] :=
	With[ {clauses = Riffle[ Map[ First, c], ","]},
		MakeExpression[ RowBox[{"And", "[", RowBox[ clauses], "]"}], fmt]
	] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {"\[Or]", RowBox[{"\[Piecewise]", GridBox[ c:{{_}..}, ___]}]}], fmt_] :=
	With[ {clauses = Riffle[ Map[ First, c], ","]},
		MakeExpression[ RowBox[{"Or", "[", RowBox[ clauses], "]"}], fmt]
	] /; $parseTheoremaExpressions
	
MakeExpression[ RowBox[ {"\[DoubleLongLeftRightArrow]"|"\[DoubleLeftRightArrow]", RowBox[{"\[Piecewise]", GridBox[ c:{{_}..}, ___]}]}], fmt_] :=
	With[ {clauses = Riffle[ Map[ First, c], ","]},
		MakeExpression[ RowBox[{"Iff", "[", RowBox[ clauses], "]"}], fmt]
	] /; $parseTheoremaExpressions
	

(* ::Subsubsection:: *)
(* Indexed functions *)

MakeExpression[ RowBox[ {SubscriptBox[ "max", ord_], "[", arg_, "]"}], fmt_] :=
	With[ {g = RowBox[ {Unique["a"], ord, Unique["b"]}]},
		MakeExpression[ RowBox[ {"max", "[", arg, ",", g, "]"}], fmt]
	]/; $parseTheoremaExpressions

	
(* ::Subsubsection:: *)
(* Number domains *)

(* Important: If a limit is "Infinity", it doesn't matter whether the range is open or closed at this limit;
				"Infinity" is always excluded!
*)

isLeftIntervalBracket[ b_] := MemberQ[ {"(", "["}, b]
isRightIntervalBracket[ b_] := MemberQ[ {")", "]"}, b]
isLeftClosed[ b_] := Switch[ b, "(", "False", "[", "True"]
isRightClosed[ b_] := Switch[ b, ")", "False", "]", "True"]
posInfBox = RowBox[ {"DirectedInfinity", "[", "1", "]"}]
negInfBox = RowBox[ {"DirectedInfinity", "[", RowBox[ {"-", "1"}], "]"}]
makeDomainRangeBox[ head_String, l_, u_, leftClosed_, rightClosed_] := RowBox[ {head, "[", RowBox[ {l, ",", u, ",", leftClosed, ",", rightClosed}], "]"}]

(* ::Subsubsubsection:: *)
(* \[DoubleStruckCapitalN] *)

(* Ellipsis-subscript without interval brackets *)
MakeExpression[ SubscriptBox[ "\[DoubleStruckCapitalN]", RowBox[ {l_, ",", "\[Ellipsis]", ",", u_}]], fmt_] :=
	MakeExpression[ makeDomainRangeBox[ "IntegerRange", makeMaxBox[ l, "0"], u, "True", "True"], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

(* Ellipsis-subscript with interval brackets
	The following 3 definitions are essentially the same, we only take care of the several possibilities how
	left/right brackets are arranged withing RowBox *)
MakeExpression[ SubscriptBox[ "\[DoubleStruckCapitalN]", RowBox[ {RowBox[ {left_?isLeftIntervalBracket, RowBox[ {l_, ",", "\[Ellipsis]", ",", u_}]}], right_?isRightIntervalBracket}]], fmt_] :=
	MakeExpression[ makeDomainRangeBox[ "IntegerRange", makeMaxBox[ l, "0"], u, isLeftClosed[ left], isRightClosed[ right]], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
MakeExpression[ SubscriptBox[ "\[DoubleStruckCapitalN]", RowBox[ {left_?isLeftIntervalBracket, RowBox[ {RowBox[ {l_, ",", "\[Ellipsis]", ",", u_}], right_?isRightIntervalBracket}]}]], fmt_] :=
	MakeExpression[ makeDomainRangeBox[ "IntegerRange", makeMaxBox[ l, "0"], u, isLeftClosed[ left], isRightClosed[ right]], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
MakeExpression[ SubscriptBox[ "\[DoubleStruckCapitalN]", RowBox[ {left_?isLeftIntervalBracket, RowBox[ {l_, ",", "\[Ellipsis]", ",", u_}], right_?isRightIntervalBracket}]], fmt_] :=
	MakeExpression[ makeDomainRangeBox[ "IntegerRange", makeMaxBox[ l, "0"], u, isLeftClosed[ left], isRightClosed[ right]], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

(* Single subscript indicating where to start from *)
MakeExpression[ SubscriptBox[ "\[DoubleStruckCapitalN]", l_], fmt_] :=
	MakeExpression[ makeDomainRangeBox[ "IntegerRange", makeMaxBox[ l, "0"], posInfBox, "True", "False"], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

(* No subscript at all; Start from 1.
	This case, unfortunately, can reasonably only be handled in "freshSymbol[]" in "Session.m" *)

makeMaxBox[ a_, b_] := RowBox[ {"max", "[", RowBox[ {"{", RowBox[ {a, ",", b}], "}"}], "]"}]

(* ::Subsubsubsection:: *)
(* \[DoubleStruckCapitalZ], \[DoubleStruckCapitalQ], \[DoubleStruckCapitalR] *)

isZQR[ dom_] := MemberQ[ {"\[DoubleStruckCapitalZ]", "\[DoubleStruckCapitalQ]", "\[DoubleStruckCapitalR]"}, dom]

makeDomainRange[ "\[DoubleStruckCapitalZ]"] := "IntegerRange"
makeDomainRange[ "\[DoubleStruckCapitalQ]"] := "RationalRange"
makeDomainRange[ "\[DoubleStruckCapitalR]"] := "RealRange"

(* Ellipsis-subscript without interval brackets *)
MakeExpression[ SubscriptBox[ dom_?isZQR, RowBox[ {l_, ",", "\[Ellipsis]", ",", u_}]], fmt_] :=
	MakeExpression[ makeDomainRangeBox[ makeDomainRange[ dom], l, u, "True", "True"], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

(* Ellipsis-subscript with interval brackets
	The following definitions are essentially the same, we only take care of the several possibilities how
	left/right brackets are arranged withing RowBox *)
MakeExpression[ SubscriptBox[ dom_?isZQR, RowBox[ {RowBox[ {left_?isLeftIntervalBracket, RowBox[ {l_, ",", "\[Ellipsis]", ",", u_}]}], right_?isRightIntervalBracket}]], fmt_] :=
	MakeExpression[ makeDomainRangeBox[ makeDomainRange[ dom], l, u, isLeftClosed[ left], isRightClosed[ right]], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
MakeExpression[ SubscriptBox[ dom_?isZQR, RowBox[ {left_?isLeftIntervalBracket, RowBox[ {RowBox[ {l_, ",", "\[Ellipsis]", ",", u_}], right_?isRightIntervalBracket}]}]], fmt_] :=
	MakeExpression[ makeDomainRangeBox[ makeDomainRange[ dom], l, u, isLeftClosed[ left], isRightClosed[ right]], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
MakeExpression[ SubscriptBox[ dom_?isZQR, RowBox[ {left_?isLeftIntervalBracket, RowBox[ {l_, ",", "\[Ellipsis]", ",", u_}], right_?isRightIntervalBracket}]], fmt_] :=
	MakeExpression[ makeDomainRangeBox[ makeDomainRange[ dom], l, u, isLeftClosed[ left], isRightClosed[ right]], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

(* Single subscript indicating where to start from *)
MakeExpression[ SubscriptBox[ dom_?isZQR, l_], fmt_] :=
	MakeExpression[ makeDomainRangeBox[ makeDomainRange[ dom], l, posInfBox, "True", "False"], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

(* No subscript at all; Start from -Infinity.
	This case, unfortunately, can reasonably only be handled in "freshSymbol[]" in "Session.m" *)

(* ::Subsubsection:: *)
(* Tuple notations *)


MakeExpression[ RowBox[ {l_,"\[LeftArrow]"}], fmt_] := MakeExpression[ RowBox[{"LeftArrow", "[", l, "]"}], fmt] /; $parseTheoremaExpressions
MakeExpression[ RowBox[ {l_,"\[LeftArrowBar]"}], fmt_] := MakeExpression[ RowBox[{"LeftArrowBar", "[", l, "]"}], fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[{left_,"\[EmptyUpTriangle]", right_}], fmt_] :=
    MakeExpression[ RowBox[{"EmptyUpTriangle", "[", RowBox[{left, ",", right}], "]"}], fmt] /; $parseTheoremaExpressions


(* ::Subsection:: *)
(* operator underscript -> domain *)


(*
	The assumption is that prefix/infix/postfix operators with underscript are used for operators, which 
	translate correctly to some expression when used without the underscript.
*)
(* PREFIX *)
MakeExpression[ RowBox[ {UnderscriptBox[ "-", dom_], r_}], fmt_] :=
    Module[ {},
    	(* Special case: unary minus *)
    	(* We memorize for output, that dom has been introduced as a domain underscript *)
    	registerDomainOperator[ "-", Minus, Prefix, dom];
        MakeExpression[ RowBox[ {RowBox[ {dom, "[", "Minus", "]"}], "[", r, "]"}], fmt]
    ] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {UnderscriptBox[ op_, dom_], r_}], fmt_] :=
    Module[ {expr = MakeExpression[ RowBox[{op, r}], fmt]},
    	(* expr is the form that would result without the underscript, say f[r] *)
        With[ {aux = expr[[1, 0]]},
    		(* We memorize for output, that dom has been introduced as a domain underscript *)
    		registerDomainOperator[ op, aux, Prefix, dom];
        	(* From expr we now fetch the head, i.e. "f". We then generate dom[f][r] *)
            MakeExpression[ RowBox[ {RowBox[ {dom, "[", aux, "]"}], "[", r, "]"}], fmt]
        ]
    ] /; $parseTheoremaExpressions

(* INFIX *)
MakeExpression[ RowBox[ {l_, UnderscriptBox[ "-", dom_], r_}], fmt_] :=
    Module[ {},
    	(* Special case: subtract *)
    	(* We memorize for output, that dom has been introduced as a domain underscript *)
    	registerDomainOperator[ "-", Subtract, Infix, dom];
        MakeExpression[ RowBox[ {RowBox[ {dom, "[", "Subtract", "]"}], "[", RowBox[ {l, ",", r}], "]"}], fmt]
    ] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {l_, UnderscriptBox[ "/", dom_], r_}], fmt_] :=
    Module[ {},
    	(* Special case: divide *)
    	(* We memorize for output, that dom has been introduced as a domain underscript *)
    	registerDomainOperator[ "/", Divide, Infix, dom];
        MakeExpression[ RowBox[ {RowBox[ {dom, "[", "Divide", "]"}], "[", RowBox[ {l, ",", r}], "]"}], fmt]
    ] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {l_, UnderscriptBox[ op_, dom_], r_}], fmt_] :=
    Module[ {expr = MakeExpression[ RowBox[{l, op, r}], fmt]},
    	(* expr is the form that would result without the underscript, say f[l,r] with HoldComplete wrapped around, so expr[[1,0]] gives the desired Head, say "f".  *)
        With[ {aux = expr[[1, 0]]},
    		(* We memorize for output, that dom has been introduced as a domain underscript *)
    		registerDomainOperator[ op, aux, Infix, dom];
        	(* From expr we now fetch the head, i.e. "f", and the box form of the parameters, i.e. box form of "x,y".
        	   We then generate dom[f][x,y] *)
            MakeExpression[ RowBox[ {RowBox[ {dom, "[", aux, "]"}], "[", RowBox[ {l, ",", r}], "]"}], fmt]
        ]
    ] /; $parseTheoremaExpressions

(* POSTFIX *)
MakeExpression[ RowBox[ {l_, UnderscriptBox[ op_, dom_]}], fmt_] :=
    Module[ {expr = MakeExpression[ RowBox[{l, op}], fmt]},
    	(* expr is the form that would result without the underscript, say f[l] *)
        With[ {aux = expr[[1, 0]]},
    		(* We memorize for output, that dom has been introduced as a domain underscript *)
    		registerDomainOperator[ op, aux, Postfix, dom];
        	(* From expr we now fetch the head, i.e. "f". We then generate dom[f][r] *)
            MakeExpression[ RowBox[ {RowBox[ {dom, "[", aux, "]"}], "[", l, "]"}], fmt]
        ]
    ] /; $parseTheoremaExpressions

(* GENERAL *)
MakeExpression[ RowBox[ {UnderscriptBox[ op_, dom_], "[", p___, "]"}], fmt_] :=
	Module[ {},
    	registerDomainOperator[ dom];
        MakeExpression[ RowBox[ {RowBox[ {dom, "[", op, "]"}], "[", p, "]"}], fmt]
    ] /; $parseTheoremaExpressions

registerDomainOperator[ op_, f_, form_, dom_] :=
	Module[{},
		isUnderscriptDomain[ dom] = True;
		operatorSymbol[ f, form] = op;
	]
registerDomainOperator[ dom_] :=
	Module[{},
		isUnderscriptDomain[ dom] = True;
	]
registerDomainOperator[ args___] := unexpected[ registerDomainOperator, {args}]


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

MakeExpression[ UnderscriptBox[ "let", rng_], fmt_] := 
	(* We the powerful toRangeBox in order to have the many variants, multiranges, etc. However, only ABBRVRNG$ makes sense in a "let",
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

SetAttributes[ subscriptedQuantifier, HoldRest]
subscriptedQuantifier[ name_, rng_, cond_, sub_, expr_, fmt_] :=
    With[ {r = toRangeBox[ rng]},
        MakeExpression[ RowBox[{"QU$", "[", 
            RowBox[{ r, ",", RowBox[{ name, "[", RowBox[{ r, ",", cond, ",", sub, ",", expr}], "]"}]}],
             "]"}], fmt]
    ]
subscriptedQuantifier[ args___] := unexpected[ subscriptedQuantifier, {args}]
    
SetAttributes[ standardGlobalQuantifier, HoldRest]
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
	
makeRangeSequence[ RowBox[{p_, "[", v:RowBox[{_, ".."|"..."}], "]"}]] :=
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


(* ::Subsubsection:: *)
(* Operators *)


MakeExpression[ RowBox[ {h_, "[", RowBox[ {op_String?isTmaOperatorSymbol}], "]"}], fmt_] :=
	MakeExpression[ RowBox[ {h, "[", RowBox[ {Replace[ op, $tmaOperatorToName]}], "]"}], fmt] /; ($parseTheoremaExpressions || $parseTheoremaGlobals)
MakeExpression[ RowBox[ {h_, "[", RowBox[ {pre___, ld_?isLeftDelimiter, op_String?isTmaOperatorSymbol}], "]"}], fmt_] :=
	MakeExpression[ RowBox[ {h, "[", RowBox[ {pre, ld, Replace[ op, $tmaOperatorToName]}], "]"}], fmt] /; ($parseTheoremaExpressions || $parseTheoremaGlobals)
MakeExpression[ RowBox[ {h_, "[", RowBox[ {op_String?isTmaOperatorSymbol, rd_?isRightDelimiter, post___}], "]"}], fmt_] :=
	MakeExpression[ RowBox[ {h, "[", RowBox[ {Replace[ op, $tmaOperatorToName], rd, post}], "]"}], fmt] /; ($parseTheoremaExpressions || $parseTheoremaGlobals)
MakeExpression[ RowBox[ {h_, "[", RowBox[ {pre___, ld_?isLeftDelimiter, op_String?isTmaOperatorSymbol, rd_?isRightDelimiter, post___}], "]"}], fmt_] :=
	MakeExpression[ RowBox[ {h, "[", RowBox[ {pre, ld, Replace[ op, $tmaOperatorToName], rd, post}], "]"}], fmt] /; ($parseTheoremaExpressions || $parseTheoremaGlobals)

MakeExpression[ RowBox[ {op_String?isTmaOperatorSymbol}], fmt_] :=
	MakeExpression[ RowBox[ {Replace[ op, $tmaOperatorToName]}], fmt] /; ($parseTheoremaExpressions || $parseTheoremaGlobals)
MakeExpression[ RowBox[ {pre___, ld_?isLeftDelimiter, op_String?isTmaOperatorSymbol}], fmt_] :=
	MakeExpression[ RowBox[ {pre, ld, Replace[ op, $tmaOperatorToName]}], fmt] /; ($parseTheoremaExpressions || $parseTheoremaGlobals)
MakeExpression[ RowBox[ {op_String?isTmaOperatorSymbol, rd_?isRightDelimiter, post___}], fmt_] :=
	MakeExpression[ RowBox[ {Replace[ op, $tmaOperatorToName], rd, post}], fmt] /; ($parseTheoremaExpressions || $parseTheoremaGlobals)
MakeExpression[ RowBox[ {pre___, ld_?isLeftDelimiter, op_String?isTmaOperatorSymbol, rd_?isRightDelimiter, post___}], fmt_] :=
	MakeExpression[ RowBox[ {pre, ld, Replace[ op, $tmaOperatorToName], rd, post}], fmt] /; ($parseTheoremaExpressions || $parseTheoremaGlobals)
	
MakeExpression[op_String?isTmaOperatorSymbol, fmt_] := MakeExpression[Replace[op, $tmaOperatorToName], fmt] /; ($parseTheoremaExpressions || $parseTheoremaGlobals)
 
isLeftDelimiter[ s_String] :=
	MemberQ[ {"[", "(", "{", "\[LeftAngleBracket]", "\[LeftBracketingBar]", "\[LeftFloor]", "\[LeftCeiling]", "\[LeftDoubleBracket]", "\[LeftDoubleBracketingBar]", ",", ";"}, s]
isRightDelimiter[ s_String] :=
	MemberQ[ {"[", "]", ")", "}", "\[RightAngleBracket]", "\[RightBracketingBar]", "\[RightFloor]", "\[RightCeiling]", "\[RightDoubleBracket]", "\[RightDoubleBracketingBar]", ",", ";"}, s]


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

MakeBoxes[ (q_?isQuantifierName)[ rng_, True, sub_, form_], TheoremaForm] := 
	RowBox[ {UnderscriptBox[ SubscriptBox[ Replace[ q, $tmaNameToQuantifier], MakeBoxes[ sub, TheoremaForm]], makeRangeBox[ rng, TheoremaForm]],
		MakeBoxes[ form, TheoremaForm]}
	]

MakeBoxes[ (q_?isQuantifierName)[ rng_, cond_, sub_, form_], TheoremaForm] := 
	RowBox[ {UnderscriptBox[ UnderscriptBox[ SubscriptBox[ Replace[ q, $tmaNameToQuantifier], MakeBoxes[ sub, TheoremaForm]], makeRangeBox[ rng, TheoremaForm]],
		MakeBoxes[ cond, TheoremaForm]], MakeBoxes[ form, TheoremaForm]}
	]

MakeBoxes[ (op_?isNonStandardOperatorName)[ arg___], TheoremaForm] :=
    With[ {b = Replace[ op, $tmaNonStandardOperatorToBuiltin]},
        MakeBoxes[ b[ arg], TheoremaForm]
    ]

(*
	Parenthesizing of expressions is an issue that may need more attention in an improved implementation.
	Current solution: 
	1) Basically, we let Mma do the formatting including setting parentheses.
	2) We parenthesize expressions with "AutoParenthesies" like in input, except for 
			expressions that format as f[...] and
			expressions starting with a "("
	3) We do not parenthesize arithmetic expressions.
	4) On demand, more exceptions can be implemented at this point.
*)
MakeBoxes[ (op_?isStandardOperatorName)[ arg__], TheoremaForm] :=
    With[ {b = tmaToInputOperator[ op]},
    	(* Special cases, because otherwise And uses && and Or uses || *)
    	Switch[ b,
    		And,
    		tmaInfixBox[ {arg}, "\[And]"],
    		Or,
    		tmaInfixBox[ {arg}, "\[Or]"],
    		Not,
    		RowBox[{ "\[Not]", parenthesize[ arg]}],
    		Plus|Times|Power,
    		MakeBoxes[ b[ arg], TheoremaForm],
    		_,
    		parenthesize[ b[ arg]]
    	]
    ]

parenthesize[ b_[ arg___]] :=
    Module[ {res = MakeBoxes[ b[ arg], TheoremaForm]},
        If[ MatchQ[ res, RowBox[ {ToString[ b], "[", ___}]|RowBox[ {"(", ___, ")"}]],
            res,
            RowBox[ {TagBox[ "(", "AutoParentheses"], res, TagBox[ ")", "AutoParentheses"]}]
        ]
    ]
parenthesize[ e_] := MakeBoxes[ e, TheoremaForm]
parenthesize[ args___] := unexpected[ parenthesize, {args}]
    
MakeBoxes[ s_?isTmaOperatorName, TheoremaForm] := Replace[ SymbolName[ s], $tmaNameToOperator]
    
MakeBoxes[ s_Symbol, TheoremaForm] := 
	(* We have to use "Unevaluated" here, because "I" is a symbol, but evaluates to "Complex[0, 1]" *)
	Module[ {n = SymbolName[ Unevaluated[ s]]},
		If[ StringLength[ n] > 3 && StringTake[ n, -3] === "$TM",
			StringDrop[ n, -3],
			n
		]
	]
	


(* ::Subsection:: *)
(* Domain underscripts *)


MakeBoxes[ (dom_?(isUnderscriptDomain[ MakeBoxes[ #, TheoremaForm]]&))[ op_][ a_], TheoremaForm] :=
	Module[ {opSymPre = operatorSymbol[ ToExpression[ MakeBoxes[ op, TheoremaForm]], Prefix],
		opSymPost = operatorSymbol[ ToExpression[ MakeBoxes[ op, TheoremaForm]], Postfix]},
		Which[
			StringQ[ opSymPre],
			RowBox[ {UnderscriptBox[ opSymPre, MakeBoxes[ dom, TheoremaForm]], MakeBoxes[ a, TheoremaForm]}],
			StringQ[ opSymPost],
			RowBox[ {MakeBoxes[ a, TheoremaForm], UnderscriptBox[ opSymPost, MakeBoxes[ dom, TheoremaForm]]}],
			True,
			MakeBoxes[ Underscript[ op, dom][ a], TheoremaForm]
		]
	]
	
MakeBoxes[ (dom_?(isUnderscriptDomain[ MakeBoxes[ #, TheoremaForm]]&))[ op_][ a_, b_], TheoremaForm] :=
	Module[ {opSym = operatorSymbol[ ToExpression[ MakeBoxes[ op, TheoremaForm]], Infix]},
		Which[
			StringQ[ opSym],
			tmaInfixBox[ {a, b}, UnderscriptBox[ opSym, MakeBoxes[ dom, TheoremaForm]]],
			True,
			MakeBoxes[ Underscript[ op, dom][ a, b], TheoremaForm]
		]
	]
	
MakeBoxes[ (dom_?(isUnderscriptDomain[ MakeBoxes[ #, TheoremaForm]]&))[ op_][ a___], TheoremaForm] :=
	MakeBoxes[ Underscript[ op, dom][ a], TheoremaForm]
	
tmaInfixBox[ args_List, op_] := RowBox[ Riffle[ Map[ MakeBoxes[ #, TheoremaForm]&, args], op]]
tmaInfixBox[ args___] := unexpected[ tmaInfixBox, {args}]

initParser[];

End[];
EndPackage[];

