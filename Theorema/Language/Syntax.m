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

BeginPackage["Theorema`Language`Syntax`"];

Needs["Theorema`Common`"]

Begin["`Private`"]

theoremaDisplay[ expr_] := DisplayForm[ theoremaBoxes[ expr]]
theoremaDisplay[ args___] := unexpected[ theoremaDisplay, {args}]

theoremaBoxes[ expr_] := stripOutermostParen[ ToBoxes[ expr, TheoremaForm]]
theoremaBoxes[ args___] := unexpected[ theoremaBoxes, {args}]

(* The ToBoxes sometimes produces parentheses also around the entire expression. This is the place to remove them before display *)
stripOutermostParen[ FormBox[ RowBox[ {TagBox["(", "AutoParentheses"], e_, TagBox[")", "AutoParentheses"]}], TheoremaForm]] := FormBox[ e, TheoremaForm]
stripOutermostParen[ FormBox[ RowBox[ {TagBox["(", "AutoParentheses"], e1_, e2__, TagBox[")", "AutoParentheses"]}], TheoremaForm]] := FormBox[ RowBox[ {e1, e2}], TheoremaForm]
stripOutermostParen[ e_] := e
stripOutermostParen[ args___] := unexpected[ stripOutermostParen, {args}]


(* In order to add a new special bracket, just add the corresponding item to the list below and provide a definition for 'MessageName' and 'translate'.
	ATTENTION! In contrast to user-defined quantifiers and variable-ranges, this is *not* possible after Theorema has been started! *)
(* Each special bracket is characterized by 6 strings, namely
	- an ID, referred to in 'translate',
	- a string depicting the brackets, used in tool-tips in the GUI,
	- the left/opening character,
	- the right/closing character,
	- the name of the bracket, which becomes the head of the internal representation of a bracketted expression, and
	- an input alias.
*)
specialBrackets =
	{
		{"\[VerticalEllipsis]\[VerticalEllipsis]", "\[VerticalEllipsis] \[VerticalEllipsis]", "\[VerticalEllipsis]", "\[VerticalEllipsis]", "SEQ$", "seq"},
		{"()", "( )", "\:fd3e", "\:fd3f", "parenthesized", "()"},
		{"(())", "(( ))", "\:2e28", "\:2e29", "doubleParenthesized", "(())"},
		{"(|)", "\:2987 \:2988", "\:2987", "\:2988", "barParenthesized", "(|)"},
		{"[]", "[ ]", "\:e114", "\:e115", "squareBracketted", "[]"},
		{"[[]]", "[[ ]]", "\:27e6", "\:27e7", "doubleSquareBracketted", "[[]]"},
		{"[|]", "\:27ec \:27ed", "\:27ec", "\:27ed", "barSlantBracketted", "[|]"},
		{"{}", "{ }", "\:e117", "\:e118", "braced", "{}"},
		{"{{}}", "{{ }}", "\:2983", "\:2984", "doubleBraced", "{{}}"},
		{"<>", "\[LeftAngleBracket] \[RightAngleBracket]", "\:27e8", "\:27e9", "angleBracketted", "<>"},
		{"<<>>", "\[LeftAngleBracket]\[LeftAngleBracket] \[RightAngleBracket]\[RightAngleBracket]", "\:27ea", "\:27eb", "doubleAngleBracketted", "<<>>"},
		{"<|>", "\:2989 \:298a", "\:2989", "\:298a", "barAngleBracketted", "<|>"},
		{"<.>", "\:2991 \:2992", "\:2991", "\:2992", "dotAngleBracketted", "<.>"},
		{"<c>", "\:29fc \:29fd", "\:29fc", "\:29fd", "curveAngleBracketted", "<c>"}
	};

SetAttributes[ isMathematicalConstant, HoldAll];
isMathematicalConstant[ Indeterminate|True|False|I|Pi|E|Infinity|DirectedInfinity|Complex|Rational|Degree|EulerGamma|GoldenRatio|Catalan|Khinchin|Glaisher] := True
isMathematicalConstant[ _] := False


(* ::Section:: *)
(* Conversion Theorema <-> Mathematica *)

(* This section must come *before* "Expressions.m" is loaded since some symbols in that file (e.g. 'Part$TM') are
	moved to "Theorema`Language`"-context here. *)

(* "$symbolTranslator" translates Mma symbols to Tma symbols corresponding to them in a 1-1 way.
	This, for instance, is not the case for "Wedge", since "Wedge" should only be turned into "And$TM" BUT NOT VICE VERSA! *)
$symbolTranslator = {"SetDelayed" -> "EqualDef", "Inequality" -> "OperatorChain", "Max" -> "max", "Min" -> "min"};

(* Every symbol in "System`" context is registered in the two "Theorema`Language`" contexts,
	and two dispatch tables for fast conversion between Theorema and Mathematica are generated. *)
{Theorema`MmaToTma, Theorema`TmaToMma, Theorema`TmaCompToMma} =
	Transpose[
		DeleteCases[
			Map[
				(* We add the same exceptions as in "freshSymbol", and treat them separately below.
					Otherwise, some rules would appear multiple times. *)
				Switch[ #,
					"DoubleRightArrow"|"DoubleLongRightArrow"|"DoubleLeftRightArrow"|"DoubleLongLeftRightArrow"|
					"Set"|"Wedge"|"Vee"|"List"|"AngleBracket"|"Complement",
					Null,
					_,
					With[ {n = ToExpression[ #, InputForm, Hold], tm = Replace[ #, $symbolTranslator] <> "$TM"},
						If[ isMathematicalConstant@@n,
							Null,
							{HoldPattern@@n :> ToExpression[ tm], (* With "ToExpression" the symbol automatically goes to the right context. "HoldPattern" is needed because otherwise some symbols, e.g. "$Context", would immediately evaluate. *)
							 RuleDelayed@@Prepend[ n, ToExpression[ "Theorema`Language`" <> tm]],
							 RuleDelayed@@Prepend[ n, ToExpression[ "Theorema`Computation`Language`" <> tm]]}
						]
					]
				]&,
				Names[ "System`*"]
			],
		Null]
	];
	
(* The dispatch tables "MmaToTma" and "Tma(Comp)ToMma" allow for a neat integration of Mathematica functions into
	Theorema sessions. They translate Mathematica expressions to their Theorema counterparts, and vice versa.
	Of course, not all Theorema expressions have Mathematica counterparts;
	For instance, Mathematica has no built-in concept of integer/rational intervals. *)
Theorema`MmaToTma = Dispatch[
			Join[ Theorema`MmaToTma,
				{HoldPattern[ DoubleRightArrow]|HoldPattern[ DoubleLongRightArrow] :> ToExpression[ "Implies$TM"],
				HoldPattern[ DoubleLeftRightArrow]|HoldPattern[ DoubleLongLeftRightArrow]|HoldPattern[ Equivalent] :> ToExpression[ "Iff$TM"],
				HoldPattern[ Set] :> ToExpression[ "Equal$TM"],
				HoldPattern[ Wedge] :> ToExpression[ "And$TM"],
				HoldPattern[ Vee] :> ToExpression[ "Or$TM"],
				HoldPattern[ Complement] :> ToExpression[ "Backslash$TM"],
				HoldPattern[ List]|HoldPattern[ AngleBracket] :> ToExpression[ "Tuple$TM"] (* We turn "List" into "Tuple", because that's actually what a Mathematica list is. *)}
			]
		   ];
Theorema`TmaToMma = Dispatch[
			Join[ Theorema`TmaToMma,
				{Theorema`Language`Iff$TM :> Equivalent,
				Theorema`Language`IffDef$TM :> Equivalent,
				Theorema`Language`Set$TM :> List,
				Theorema`Language`Tuple$TM :> List,
				Theorema`Language`Backslash$TM :> Complement,
				Theorema`Language`Radical$TM[ x_, y_] :> Power[ x, 1/y]}
				(* "Theorema`Language`AngleBracket$TM", "Theorema`Language`Equivalent$TM" etc. are not translated,
					because they should not appear in Theorema expressions anyway ... *)
			]
		   ];
Theorema`TmaCompToMma = Dispatch[
			Join[ Theorema`TmaCompToMma,
				{Theorema`Computation`Language`Iff$TM :> Equivalent,
				Theorema`Computation`Language`IffDef$TM :> Equivalent,
				Theorema`Computation`Language`Set$TM :> List,
				Theorema`Computation`Language`Tuple$TM :> List,
				Theorema`Computation`Language`Backslash$TM :> Complement,
				Theorema`Computation`Language`Radical$TM[ x_, y_] :> Power[ x, 1/y]}
			]
		   ];


(* ::Section:: *)
(* "Expressions.m" *)

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

$tmaQuantifierNames = {};	(* Contains the names of all registered quantifiers as *strings*, without parameters (e.g. "Forall", "Exists", ...). *)
$tmaQuantifierToName = {};
$tmaNameToQuantifier = {};

(* 'isQuantifier[ expr]' gives True iff 'expr' represents the head (including parameters) of a registered quantifier.
	'isQuantifier' works in both "Theorema`" and "Theorema`Computation`" context.
	This is the default definition; 'registerQuantifier' adds other definitions. *)
isQuantifier[ _] := False

(* The following function registers a new quantifier.
	In 'registerRange[ name, inputRules, outputRules]'
	- 'name' is a string representing the name of the quantifier, e.g. "Forall".
	- 'inputRules' is a list of rules of the form 'box :> {params, subscript, cond, multi, ranges}', where
		> 'box' is a box(-pattern),
		> 'params' is either 'Null' (default) or a list of parameters that shall be added to the name of the quantifier when constructing the quantified expression,
		> 'subscript' is either 'None', "Annotated" (default) or "DomainOperation", where 'None' means that the quantifier may not be input with subscripts,
			"Annotated" means that subscripts are turned into annotations, and "DomainOperation" means that subscripts are interpreted as domains (resulting in 'DomainOperation'),
		> 'cond' is a Boolean value indicating whether the quantifier is allowed to have an additional condition (default is 'True'),
		> 'multi' is a Boolean value indicating whether the quantifier may bind several variables at once (default is 'True'), and
		> 'ranges' is a pattern expression specifying the names (strings!) of the variable-ranges that are allowed to appear under the quantifier (default is '_'),
			e.g. for "TupleOf" it is "STEPRNG$".
	- 'outputRules' is a list of rules of the form 'params :> box', where
		> 'params' is either 'Null' (default) or a list of patterns corresponding to the parameters of the quantifier (as in 'inputRules'), and
		> 'box' is the box-expression that shall be constructed when pretty-printing 'name' or 'name[ params]', respectively.
*)
registerQuantifier[ name_String, box:Except[ _Rule|_RuleDelayed|{(_Rule|_RuleDelayed)...}], rest___] :=
	registerQuantifier[ name, box -> Null, rest]
registerQuantifier[ name_String, rule:(_Rule|_RuleDelayed), rest___] :=
	registerQuantifier[ name, {rule}, rest]
registerQuantifier[ name_String, input:{(Rule|RuleDelayed)[ box_, _], ___}] :=
	registerQuantifier[ name, input, Null -> box]
registerQuantifier[ name_String, input_List, box:Except[ _Rule|_RuleDelayed|{(_Rule|_RuleDelayed)...}]] :=
	registerQuantifier[ name, input, Null -> box]
registerQuantifier[ name_String, input_List, rule:(_Rule|_RuleDelayed)] :=
	registerQuantifier[ name, input, {rule}]
registerQuantifier[ name_String, input_List, output_List] :=
	If[ !MemberQ[ $tmaQuantifierNames, name],
		AppendTo[ $tmaQuantifierNames, name];
		$tmaQuantifierToName =
			Join[ $tmaQuantifierToName,
				Cases[ input, (Rule|RuleDelayed)[ l_, r_] :> (l :> getQuantifierSpecification[ name, r])]
			];
		With[ {
					sym1 = Block[ {$ContextPath = Join[ {"Theorema`Language`"}, If[ ListQ[ $TheoremaArchives], $TheoremaArchives, {}], $ContextPath], $Context = "Theorema`Knowledge`"},
							ToExpression[ name <> "$TM"]
						],
					sym2 = Block[ {$ContextPath = Join[ {"Theorema`Computation`Language`"}, If[ ListQ[ $TheoremaArchives], $TheoremaArchives, {}], $ContextPath], $Context = "Theorema`Computation`Knowledge`"},
							ToExpression[ name <> "$TM"]
						]
				},
			$tmaNameToQuantifier = Join[ $tmaNameToQuantifier,
					Join @@
					DeleteCases[
						Replace[ output,
							{
								(Rule|RuleDelayed)[ Null, box_] :>
									(
										isQuantifier[ sym1] = True;
										isQuantifier[ sym2] = True;
										{sym1 :> box, sym2 :> box}
									),
								(Rule|RuleDelayed)[ params_List, box_] :>
									With[ {expr1 = sym1 @@ params, expr2 = sym2 @@ params},
										isQuantifier[ expr1] = True;
										isQuantifier[ expr2] = True;
										{expr1 :> box, expr2 :> box}
									],
								_ -> $Failed
							},
							{1}
						],
						$Failed
					]
				]
		];
	]
registerQuantifier[ args___] := unexpected[ registerQuantifier, {args}]

getQuantifierSpecification[ name_, Null] :=
	getQuantifierSpecification[ name, {"Annotated", True, True, Blank[]}]
getQuantifierSpecification[ name_, {Null, sub_, cond_, multi_, ranges_}] :=
	getQuantifierSpecification[ name, {sub, cond, multi, ranges}]
getQuantifierSpecification[ name_, {params_List, sub_, cond_, multi_, ranges_}] :=
	getQuantifierSpecification[ RowBox[ {name, "[", RowBox[ Riffle[ params, ","]], "]"}], {sub, cond, multi, ranges}]
getQuantifierSpecification[ name_, {sub_, cond_, multi_, ranges_}] :=
	{name, sub, cond, multi, ranges}
getQuantifierSpecification[ args___] := unexpected[ getQuantifierSpecification, {args}]

(* To register a new quantifier, just add a call to 'registerQuantifier' below. *)
registerQuantifier[ "Forall", "\[ForAll]"]
registerQuantifier[ "Exists", "\[Exists]"]
registerQuantifier[ "NotExists", "\[NotExists]"]
registerQuantifier[ "ExistsUnique", RowBox[ {"\[Exists]", "!"}], RowBox[ {"\[Exists]", "\[NegativeThickSpace]", "\[NegativeThinSpace]", "!"}]]
registerQuantifier[ "IntersectionOf", "\[Intersection]"]
registerQuantifier[ "UnionOf", "\[Union]"]
registerQuantifier[ "SumOf", "\[Sum]" -> {"DomainOperation", True, True, _}]
registerQuantifier[ "ProductOf", "\[Product]" -> {"DomainOperation", True, True, _}]
registerQuantifier[ "IntegralOf", "\[Integral]"]
registerQuantifier[ "Such", {"\[CurlyEpsilon]" -> Null, "such" -> Null}]
registerQuantifier[ "SuchUnique", "the"]
registerQuantifier[ "MinimumOf", "min"]
registerQuantifier[ "MaximumOf", "max"]
registerQuantifier[ "ArgMin", "argmin"]
registerQuantifier[ "ArgMax", "argmax"]
registerQuantifier[ "TheArgMin", "theargmin"]
registerQuantifier[ "TheArgMax", "theargmax"]
registerQuantifier[ "Lambda", "\[Lambda]"]
registerQuantifier[ "Abbrev", "let" -> {None, False, True, "ABBRVRNG$"}]
registerQuantifier[ "SetOf", {"{", "}"} -> {None, True, True, _}]
registerQuantifier[ "TupleOf", {"\[LeftAngleBracket]", "\[RightAngleBracket]"} -> {None, True, False, "STEPRNG$"}]
registerQuantifier[ "SequenceOf",
	{TagBox[ "\[VerticalEllipsis]", ___], TagBox[ "\[VerticalEllipsis]", ___]} -> {None, True, False, "STEPRNG$"},
	{TagBox[ "\[VerticalEllipsis]", Identity, SyntaxForm -> "("], TagBox[ "\[VerticalEllipsis]", Identity, SyntaxForm -> ")"]}
]

(* We keep the distinction between built-in- and user-ranges,
	because built-in ranges provide much more powerful parsing rules for multiple variables. *)
$tmaUserRangeNames = {};	(* Contains the names of all user-defined variable ranges as *strings* (e.g. "LIMRNG$", ...). *)
$tmaBoxToUserRange = {};
$tmaUserRangeToBox = {};
$tmaUserRangeToCondition = {};

(* 'isVariableRange[ rng]' gives True iff 'rng' is a variable range, either built-in or user-defined.
	'isVariableRange' works in both "Theorema`" and "Theorema`Computation`" context.
	This is the default definition; 'registerRange' adds other definitions. *)
isVariableRange[ rng_] :=
	MemberQ[
		{
			Theorema`Language`SIMPRNG$, Theorema`Computation`Language`SIMPRNG$,
			Theorema`Language`PREDRNG$, Theorema`Computation`Language`PREDRNG$,
			Theorema`Language`SETRNG$, Theorema`Computation`Language`SETRNG$,
			Theorema`Language`STEPRNG$, Theorema`Computation`Language`STEPRNG$,
			Theorema`Language`ABBRVRNG$, Theorema`Computation`Language`ABBRVRNG$,
			Theorema`Language`DOMEXTRNG$, Theorema`Computation`Language`DOMEXTRNG$
		},
		rng
	]

(* The following function registers a new user-defined variable-range.
	In 'registerRange[ name, inputRules, outputRules, conds]'
	- 'name' is a string representing the name of the range, e.g. "LIMRNG$". Note that such names typically end with "$", but "$" is not added automatically!
	- 'inputRules' is a list of rules of the form 'box :> params', where
		> 'box' is a box(-pattern) where precisely once the string "$var" must appear, representing the bound variable, and
		> 'params' is a list of additional arguments the range depends upon and that may also appear (as named patterns) in 'box',
	- 'outputRules' is a list of rules of the form 'args :> box', where
		> 'args' is a list of patterns corresponding to all arguments of the range; in contrast to 'params' in 'inputRules', this also includes the bound variable!
		> 'box' is the box-expression that shall be constructed when pretty-printing the range with arguments 'args'.
			Calls to 'MakeBoxes' that do not specify the format (e.g. 'TheoremaForm') are automatically replaced by calls specifying the "right" format.
	- 'conds' is a list of rules of the form 'args :> cond', where
		> 'args' has exactly the same meaning as in 'outputRules', and
		> 'cond' is a list of Theorema expressions (in "Theorema`" context) representing the conditions on the bound variable that can be extracted from the range,
			or '$Failed' if no conditions can be extracted from the range (this is the default value; think of "limit ranges").
*)
registerRange[ _String?(MemberQ[ $tmaUserRangeNames, #]&), ___] :=
	Null
registerRange[ name_String, input:(_Rule|_RuleDelayed), rest___] :=
	registerRange[ name, {input}, rest]
registerRange[ name_String, input_List, output:(_Rule|_RuleDelayed), rest___] :=
	registerRange[ name, input, {output}, rest]
registerRange[ name_String, input_List, output_List] :=
	registerRange[ name, input, output, {}]
registerRange[ name_String, input_List, output_List, cond:(_Rule|_RuleDelayed)] :=
	registerRange[ name, input, output, {cond}]
registerRange[ name_String, input_List, output_List, cond_List] :=
	(
		AppendTo[ $tmaUserRangeNames, name];
		$tmaBoxToUserRange = Join[ $tmaBoxToUserRange,
				Cases[ input,
						(h:(Rule|RuleDelayed))[ box_, expr_] :>
							With[ {p = Position[ HoldComplete[ box], "$var"]},
								h @@ Join[
										ReplacePart[ HoldComplete[ box], First[ p] -> Pattern[ $var, BlankSequence[]]],
										HoldComplete[ {name, {$var}, expr}]
									] /; Length[ p] === 1
							]
				]
			];
		With[ {
					sym1 = Block[ {$ContextPath = Join[ {"Theorema`Language`"}, If[ ListQ[ $TheoremaArchives], $TheoremaArchives, {}], $ContextPath], $Context = "Theorema`Knowledge`"},
							ToExpression[ name]
						],
					sym2 = Block[ {$ContextPath = Join[ {"Theorema`Computation`Language`"}, If[ ListQ[ $TheoremaArchives], $TheoremaArchives, {}], $ContextPath], $Context = "Theorema`Computation`Knowledge`"},
							ToExpression[ name]
						]
				},
			isVariableRange[ sym1] = True;
			isVariableRange[ sym2] = True;
			$tmaUserRangeToBox = Join[ $tmaUserRangeToBox,
					Join @@ Cases[ output,
									(Rule|RuleDelayed)[ expr_List, box_] :>
										With[ {newBox = HoldComplete[ box] /. HoldPattern[ MakeBoxes[ b_]] :> MakeBoxes[ b, $fmt]},
											{RuleDelayed @@ Prepend[ newBox, {sym1 @@ expr, $fmt_}], RuleDelayed @@ Prepend[ newBox, {sym2 @@ expr, $fmt_}]}
										]
							]
				];
			$tmaUserRangeToCondition = Join[ $tmaUserRangeToCondition,
					Cases[ cond, (Rule|RuleDelayed)[ expr_List, c_] :> (sym1 @@ expr :> c)]
				]
		];
	)
registerRange[ args___] := unexpected[ registerRange, {args}]
	
(*
The following code would add a new limit-range:

registerRange[
	"LIMRNG$",
	{
		RowBox[ {"$var", "\[Rule]", lim_}] :> {lim, 0},
		RowBox[ {"$var", "\[UpperRightArrow]", lim_}] :> {lim, 1},	(*approaching the limit from below*)
		RowBox[ {"$var", "\[LowerRightArrow]", lim_}] :> {lim, -1}	(*approaching the limit from above*)
	},
	{
		{x_, lim_, 0} :> RowBox[ {MakeBoxes[ x], "\[Rule]", MakeBoxes[ lim]}],
		{x_, lim_, 1} :> RowBox[ {MakeBoxes[ x], "\[UpperRightArrow]", MakeBoxes[ lim]}],
		{x_, lim_, -1} :> RowBox[ {MakeBoxes[ x], "\[LowerRightArrow]", MakeBoxes[ lim]}]
	}
]
*)

(* $tmaNonStandardOperators is defined in Expression.m *)
$tmaNonStandardOperatorNames = First /@ $tmaNonStandardOperators;
$tmaNonStandardOperatorToBuiltin = Dispatch[ Apply[ Rule, $tmaNonStandardOperators, {1}]];

isNonStandardOperatorName[ f_] := MemberQ[ $tmaNonStandardOperatorNames, f]
isNonStandardOperatorName[ args___] := unexpected[ isNonStandardOperatorName, {args}]

isStandardOperatorName[ f_Symbol] :=
    With[ {n = SymbolName[ f]},
        StringLength[ n] > 3 && StringTake[ n, -3] === "$TM"
    ]
isStandardOperatorName[ f_] := False
isStandardOperatorName[ args___] := unexpected[ isStandardOperatorName, {args}]

tmaToInputOperator[ op_Symbol] :=
    With[ {n = SymbolName[ op]},
        If[ StringTake[ n, -3] == "$TM",
        	ToExpression[ StringDrop[ n, -3]],
        (*else*)
            ToExpression[ n]
        ]
    ]
tmaToInputOperator[ args___] := unexpected[ tmaToInputOperator, {args}]

SetAttributes[ removeVar, HoldAllComplete];
removeVar[ (h:(Theorema`Language`SEQ0$|Theorema`Language`SEQ1$|Theorema`Computation`Language`SEQ0$|Theorema`Computation`Language`SEQ1$))[ op_Symbol]] :=
	ReplacePart[ HoldComplete@@{removeVar[ op]}, {1, 0} -> h]
removeVar[ op_Symbol] :=
	With[ {n = SymbolName[ Unevaluated[ op]]},
		Block[ {$Context = "Theorema`Knowledge`", $ContextPath = Prepend[ $ContextPath, "Theorema`Language`"]},
			(* Names of variables shall stay in Theorema` context!
				Otherwise, 'x$TM' would go to Global`-context. *)
			ToExpression[ removeVar[ n], InputForm, HoldComplete]
		]
	]
removeVar[ op_String] :=
	If[ StringLength[ op] > 4 && StringTake[ op, 4] === "VAR$",
		StringDrop[ op, 4],
		op
	]

With[ {spec = Alternatives @@ specialBrackets[[All, 3]],
		std = Join[
					{"[", "(", "{", "\[LeftAngleBracket]", "\[LeftBracketingBar]",
					"\[LeftFloor]", "\[LeftCeiling]", "\[LeftDoubleBracket]",
					"\[LeftDoubleBracketingBar]", TagBox[ "(", "AutoParentheses"], ",", ";"},
					If[ $VersionNumber >= 10.0, {"\:f113"}, {}]	(* left association character *)
				]},
	getLeftDelimiter[ TagBox[ box:spec, ___]] :=
		box;
	getLeftDelimiter[ TagBox[ box_, _Theorema`Language`TAG$|_Theorema`Computation`Language`TAG$, ___]] :=
		getLeftDelimiter[ box];
	getLeftDelimiter[ box_] :=
		If[ MemberQ[ std, box],
			box,
		(*else*)
			$Failed
		]
]
With[ {spec = Alternatives @@ specialBrackets[[All, 4]],
		std = Join[
					{"[", "]", ")", "}", "\[RightAngleBracket]", "\[RightBracketingBar]",
					"\[RightFloor]", "\[RightCeiling]", "\[RightDoubleBracket]",
					"\[RightDoubleBracketingBar]", TagBox[ ")", "AutoParentheses"], ",", ";"},
					If[ $VersionNumber >= 10.0, {"\:f114"}, {}]	(* right association character *)
				]},
	getRightDelimiter[ TagBox[ box:spec, ___]] :=
		box;
	getRightDelimiter[ TagBox[ box_, _Theorema`Language`TAG$|_Theorema`Computation`Language`TAG$, ___]] :=
		getRightDelimiter[ box];
	getRightDelimiter[ box_] :=
		If[ MemberQ[ std, box],
			box,
		(*else*)
			$Failed
		]
]

isLeftDelimiter[ box_] := (getLeftDelimiter[ box] =!= $Failed)
isRightDelimiter[ box_] := (getRightDelimiter[ box] =!= $Failed)


(* In the following list:
	- The first element of each item is the symbol of the operator; could be "".
	- The second element is a list of possible syntax of the operator according to Mathematica; used
		for pretty-printing ONLY.
	- The third element is the full name of the operator, as it should be parsed; it should
		always be the name of a Mathematica-built-in symbol, since otherwise symbols might appear
		in the wrong context (-> renaming the built-in name to another name, e.g. "SetDelayed" to
		"EqualDef", happens only in 'freshSymbol').
		Also note that the third element MUST be different from the first element!
	- The (optional) fourth argument is an alternative full name of the operator,
		e.g. "Iff" for "DoubleLeftRightArrow"; this ONLY affects pretty-printing and replaces the
		obsolete '$tmaNonStandardOperators'.
		If a fourth element is present, the first element MUST be different from ""! *)
$tmaOperators = {
	{"", {}, "min"}, {"", {}, "max"},	(*needed for parsing 'min_Greater' as 'Annotated[ min, SubScript[ Greater]]' rather than 'Subscript[ min, Greater]'*)
	{"@", {Infix}, "Componentwise"}, {"/@", {Infix}, "Map"}, {"//@", {Infix}, "MapAll"},
	{">>", {Infix}, "Put"}, {">>>", {Infix}, "PutAppend"}, {"<<", {Prefix}, "Get"},
	{"@@", {Infix}, "Apply"}, {";;", {Infix}, "Span"},
	{"\[Rule]", {Infix}, "Rule"}, {"\[RuleDelayed]", {Infix}, "RuleDelayed"},
	{"\[UndirectedEdge]", {Infix}, "UndirectedEdge"}, {"\[DirectedEdge]", {Infix}, "DirectedEdge"},
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
	{"\[DoubleLeftRightArrow]", {Infix}, "DoubleLeftRightArrow", "Iff"}, {"\[DoubleLongRightArrow]", {Infix}, "DoubleLongRightArrow"},
	{"\[DoubleLongLeftArrow]", {Infix}, "DoubleLongLeftArrow"}, {"\[DoubleLongLeftRightArrow]", {Infix}, "DoubleLongLeftRightArrow"},
	{"\[DownArrow]", {Infix}, "DownArrow"}, {"\[UpArrow]", {Infix}, "UpArrow"}, {"\[UpDownArrow]", {Infix}, "UpDownArrow"},
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
	{"\[GreaterEqual]", {Infix}, "GreaterEqual"}, {">=", {Infix}, "GreaterEqual"},
	{"\[NotGreaterEqual]", {Infix}, "NotGreaterEqual"}, {"\[GreaterSlantEqual]", {Infix}, "GreaterEqual"},
	{"\[NotGreaterSlantEqual]", {Infix}, "NotGreaterSlantEqual"}, {"\[GreaterFullEqual]", {Infix}, "GreaterFullEqual"},
	{"\[NotGreaterFullEqual]", {Infix}, "NotGreaterFullEqual"}, {"\[GreaterTilde]", {Infix}, "GreaterTilde"},
	{"\[NotGreaterTilde]", {Infix}, "NotGreaterTilde"}, {"\[GreaterGreater]", {Infix}, "GreaterGreater"},
	{"\[NotGreaterGreater]", {Infix}, "NotGreaterGreater"}, {"\[NestedGreaterGreater]", {Infix}, "NestedGreaterGreater"},
	{"\[NotNestedGreaterGreater]", {Infix}, "NotNestedGreaterGreater"}, {">", {Infix}, "Greater"},
	{"\[NotGreater]", {Infix}, "NotGreater"}, {"\[LessEqual]", {Infix}, "LessEqual"},
	{"<=", {Infix}, "LessEqual"}, {"\[NotLessEqual]", {Infix}, "NotLessEqual"},
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
	{"=", {Infix}, "Set"}, {":=", {Infix}, "SetDelayed", "EqualDef"},
	{"\[Equal]", {Infix}, "Equal"}, {"==", {Infix}, "Equal"},
	{"\[LongEqual]", {Infix}, "Equal"}, {"\[NotEqual]", {Infix}, "Unequal"},
	{"!=", {Infix}, "Unequal"}, {"===", {Infix}, "SameQ"},
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
	{"\[DoubleLeftTee]", {Infix}, "DoubleLeftTee"}, {"\[SuchThat]", {Infix}, "SuchThat"},
	{"\[Distributed]", {Infix}, "Distributed"}, {"\[Conditioned]", {Infix}, "Conditioned"},
	{"\[Cup]", {Infix}, "Cup"}, {"\[Cap]", {Infix}, "Cap"},
	{"\[CupCap]", {Infix}, "CupCap"}, {"\[NotCupCap]", {Infix}, "NotCupCap"},
	{"\:22ff", {Infix}, "elemTuple"}, {"\:22c8", {Infix}, "joinTuples"},
	{"\:293a", {Infix}, "appendElem"}, {"\:293b", {Infix}, "prependElem"}};
	
(* The following (alphabetically sorted) list contains the names of all symbols that are interpreted as binary relations
	in Theorema (-> chains of relations). Of course, all symbols may also be annotated and/or domain-underscripted.
	The names have to be exactly as in '$tmaOperatorSymbols'. *)
$tmaBinaryRelations =
	{
		"Element", "Equal",
		"Greater", "GreaterEqual",
		"Less", "LessEqual",
		"NotElement", "NotGreater", "NotGreaterEqual", "NotLess", "NotLessEqual", "NotSubset", "NotSubsetEqual", "NotSuperset", "NotSupersetEqual", "NotReverseElement",
		"ReverseElement",
		"Subset", "SubsetEqual", "Superset", "SupersetEqual",
		"Unequal"
	};
	
$tmaOperatorSymbols = Map[ First, $tmaOperators];
(* We must not add contexts (like "Theorema`Language`" etc.) to the operator names, as it is done with quantifiers,
	because copying each of the more than 200 operator names twice (for the two possible contexts) seems to be a bit too inefficient. *)
$tmaOperatorToName = Dispatch[ Map[ Rule[ First[ #], #[[3]]] &, $tmaOperators]];
$tmaNameToOperator =
	Replace[
		$tmaOperators,
		{
			{"", _, name_String} :> (name <> "$TM" -> name),
			{sym_, _, name_String} :> (name <> "$TM" -> sym),
			{sym_, _, name1_String, name2_String} :> Sequence[ name1 <> "$TM" -> sym, name2 <> "$TM" -> sym]
		},
		{1}
	];
$tmaOperatorNames = First /@ $tmaNameToOperator;
$tmaNameToOperator = Dispatch[ $tmaNameToOperator];

(* We need this attribute, because otherwise expressions (not only operator symbols!) are evaluated when "MakeBoxes" is called. *)
SetAttributes[ isTmaOperatorName, HoldAllComplete];
isTmaOperatorName[ op_Symbol] := Quiet[ Check[ isTmaOperatorString[ SymbolName[ op], True], False]]

isTmaOperatorString[ op_String, True] := isTmaOperatorString[ removeVar[ op], False]
isTmaOperatorString[ op_String, False] := MemberQ[ $tmaOperatorNames, op]

(* "getTmaOperatorName" returns the string form (without suffix "$TM" and prefix "$VAR") of the Theorema operator name 'op',
	even if it occurs inside nested "TAG$"-,"Annotated$TM"-, "DomainOperation$TM"- or "VAR$"-expressions.
	If 'op' is no Theorema operator name, $Failed is returned. *)
SetAttributes[ getTmaOperatorName, HoldAllComplete];
getTmaOperatorName[ op_Symbol] := Quiet[ Check[ getTmaOperatorNameFromString[ SymbolName[ op]], $Failed]]
getTmaOperatorName[ (Theorema`Language`VAR$|Theorema`Computation`Language`VAR$)[ op_Symbol]] :=
	Quiet[ Check[ getTmaOperatorNameFromString[ removeVar[ SymbolName[ op]]], $Failed]]
getTmaOperatorName[ (Theorema`Language`FIX$|Theorema`Computation`Language`FIX$)[ op_Symbol, 0]] :=
	Quiet[ Check[ getTmaOperatorNameFromString[ removeVar[ SymbolName[ op]]], $Failed]]
getTmaOperatorName[ (Theorema`Language`TAG$|Theorema`Computation`Language`TAG$)[ op_, ___]] := getTmaOperatorName[ op]
getTmaOperatorName[ (Theorema`Language`Annotated$TM|Theorema`Computation`Language`Annotated$TM)[ op_, __]] := getTmaOperatorName[ op]
getTmaOperatorName[ (Theorema`Language`DomainOperation$TM|Theorema`Computation`Language`DomainOperation$TM)[ _, op_]] := getTmaOperatorName[ op]
getTmaOperatorName[ _] := $Failed

getTmaOperatorNameFromString[ op_String] := If[ MemberQ[ $tmaOperatorNames, op], StringDrop[ op, -3], $Failed]

isTmaOperatorSymbol[ op_String] := MemberQ[ $tmaOperatorSymbols, op]
isTmaOperatorBox[ (OverscriptBox|SubscriptBox)[ op_, __], fullName_:False] := isTmaOperatorBox[ op, fullName]
isTmaOperatorBox[ (UnderscriptBox|SuperscriptBox)[ op_, _], fullName_:False] := isTmaOperatorBox[ op, fullName]
isTmaOperatorBox[ (UnderoverscriptBox|SubsuperscriptBox)[ op_, _, _], fullName_:False] := isTmaOperatorBox[ op, fullName]
(* In the following definition, if 'fullName' is 'True', the second alternative ensures that "Plus_0"
	is also transformed into "Annotated[Plus, SubScript[0]]", not only "+_0". *)
isTmaOperatorBox[ op_String, fullName_:False] := isTmaOperatorSymbol[ op] || (fullName && MemberQ[ $tmaOperatorNames, op <> "$TM"])
isTmaOperatorBox[ ___] := False

isTmaRelationBox[ (OverscriptBox|SubscriptBox)[ op_, __]] := isTmaRelationBox[ op]
isTmaRelationBox[ (UnderscriptBox|SuperscriptBox)[ op_, _]] := isTmaRelationBox[ op]
isTmaRelationBox[ (UnderoverscriptBox|SubsuperscriptBox)[ op_, _, _]] := isTmaRelationBox[ op]
isTmaRelationBox[ op_String] := MemberQ[ $tmaBinaryRelations, Replace[ op, $tmaOperatorToName]]
isTmaRelationBox[ ___] := False

getTmaOperatorForms[ op_Symbol] := getTmaOperatorForms[ StringDrop[ SymbolName[ op], -3]]
getTmaOperatorForms[ op_String] := First[ Cases[ $tmaOperators, {_, forms_, ___, op} -> forms]]


(* ::Section:: *)
(* Quoted Expressions *)

MakeExpression[ RowBox[ {"\[OpenCurlyQuote]", expr_, "\[CloseCurlyQuote]"}], fmt_] :=
	Block[ {$parseTheoremaQuoted = False},
	With[ {out = makeTmaExpressionFromBoxes[ expr, removeRedundantBoxes, Identity]},
		If[ MatchQ[ out, _Hold],
			HoldComplete @@ out,
		(*else*)
			HoldComplete[ $Failed]
		]
	]] /; $parseTheoremaQuoted

(* ::Section:: *)
(* MakeExpression *)


MakeExpression[ RowBox[ {a_?isLeftDelimiter, TagBox[ op_, Identity, ___], b_?isRightDelimiter}], fmt_] := 
	MakeExpression[ RowBox[ {a, RowBox[ {op}], b}], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
MakeExpression[RowBox[{a:Except[ _?isLeftDelimiter], TagBox[op_, Identity, ___], b_?isRightDelimiter}], fmt_] := 
	MakeExpression[RowBox[{RowBox[{a, op}], b}], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
MakeExpression[RowBox[{a_?isLeftDelimiter, TagBox[op_, Identity, ___], b:Except[ _?isRightDelimiter]}], fmt_] := 
	MakeExpression[RowBox[{a, RowBox[{op, b}]}], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
MakeExpression[RowBox[{a:Except[ _?isLeftDelimiter], TagBox[op_, Identity, ___], b:Except[ _?isRightDelimiter]}], fmt_] := 
	MakeExpression[RowBox[{a, op, b}], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
MakeExpression[RowBox[{TagBox[op_, Identity, ___], b:Except[ _?isRightDelimiter]}], fmt_] := 
	MakeExpression[RowBox[{op, b}], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
MakeExpression[RowBox[{a:Except[ _?isLeftDelimiter], TagBox[op_, Identity, ___]}], fmt_] := 
	MakeExpression[RowBox[{a, op}], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

MakeExpression[RowBox[{ TagBox[ "(", "AutoParentheses"], expr_, TagBox[ ")", "AutoParentheses"]}], fmt_] := 
	MakeExpression[ expr, fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
	
	
(* ::Subsubsection:: *)
(* Sequence Expressions *)

MakeExpression[ RowBox[{a_, "..."}], fmt_] :=
	MakeExpression[ RowBox[{"SEQ0$", "[", a, "]"}], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
	
MakeExpression[ RowBox[{a_, ".."}], fmt_] :=
	MakeExpression[ RowBox[{"SEQ1$", "[", a, "]"}], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals


(* ::Subsubsection:: *)
(* Quantifiers *)


MakeExpression[ RowBox[ {UnderscriptBox[ q_, rng_], form_}], fmt_] :=
	With[ {qu = constructQuantifier[ Replace[ q, $tmaQuantifierToName], rng, form, fmt]},
		qu /; qu =!= $Failed
	] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {UnderscriptBox[ UnderscriptBox[ q_, rng_], cond_], form_}], fmt_] :=
	With[ {qu = constructQuantifier[ Replace[ q, $tmaQuantifierToName], rng, form, cond, fmt]},
		qu /; qu =!= $Failed
	] /; $parseTheoremaExpressions
	
MakeExpression[ RowBox[ {left_, RowBox[ {form_, UnderscriptBox[ "|"|":", rng_]}], right_}], fmt_] :=
	With[ {qu = constructQuantifier[ Replace[ {left, right}, $tmaQuantifierToName], rng, form, fmt]},
		qu /; qu =!= $Failed
	] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {left_, RowBox[ {form_, UnderscriptBox[ "|"|":", rng_], cond_}], right_}], fmt_] :=
    With[ {qu = constructQuantifier[ Replace[ {left, right}, $tmaQuantifierToName], rng, form, cond, fmt]},
		qu /; qu =!= $Failed
	] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {left_, RowBox[ {form_, UnderscriptBox[ UnderscriptBox[ "|"|":", rng_], cond_]}], right_}], fmt_] :=
    With[ {qu = constructQuantifier[ Replace[ {left, right}, $tmaQuantifierToName], rng, form, cond, fmt]},
		qu /; qu =!= $Failed
	] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {left_, RowBox[ {rng_, "|"|":", cond_}], right_}], fmt_] :=
	With[ {qu = constructQuantifier[ Replace[ {left, right}, $tmaQuantifierToName], rng, Null, cond, fmt]},
		qu /; qu =!= $Failed
	] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {UnderscriptBox[ SubscriptBox[ q_, sub_], rng_], form_}], fmt_] :=
	With[ {qu = constructQuantifier[ Replace[ q, $tmaQuantifierToName], rng, form, Null, sub, fmt]},
		qu /; qu =!= $Failed
	] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {UnderscriptBox[ UnderscriptBox[ SubscriptBox[ q_, sub_], rng_], cond_], form_}], fmt_] :=
    With[ {qu = constructQuantifier[ Replace[ q, $tmaQuantifierToName], rng, form, cond, sub, fmt]},
		qu /; qu =!= $Failed
	] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {UnderoverscriptBox[ q_, low:RowBox[ {_, "=", _}], high_], form_}], fmt_] :=
    With[ {qu = constructQuantifier[ Replace[ q, $tmaQuantifierToName], RowBox[ {low, ",", "\[Ellipsis]", ",", high}], form, fmt]},
		qu /; qu =!= $Failed
	] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {UnderscriptBox[ UnderoverscriptBox[ q_, low:RowBox[ {_, "=", _}], high_], cond_], form_}], fmt_] :=
    With[ {qu = constructQuantifier[ Replace[ q, $tmaQuantifierToName], RowBox[ {low, ",", "\[Ellipsis]", ",", high}], form, cond, fmt]},
		qu /; qu =!= $Failed
	] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {UnderoverscriptBox[ SubscriptBox[ q_, sub_], low:RowBox[ {_, "=", _}], high_], form_}], fmt_] :=
    With[ {qu = constructQuantifier[ Replace[ q, $tmaQuantifierToName], RowBox[ {low, ",", "\[Ellipsis]", ",", high}], form, Null, sub, fmt]},
		qu /; qu =!= $Failed
	] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {UnderscriptBox[ UnderoverscriptBox[ SubscriptBox[ q_, sub_], low:RowBox[ {_, "=", _}], high_], cond_], form_}], fmt_] :=
    With[ {qu = constructQuantifier[ Replace[ q, $tmaQuantifierToName], RowBox[ {low, ",", "\[Ellipsis]", ",", high}], form, cond, sub, fmt]},
		qu /; qu =!= $Failed
	] /; $parseTheoremaExpressions


(* ::Subsubsection:: *)
(* Special arithmetic *)

(* we do not want that a-b is automatically converted to a+(-b), this should only be under built-in subtract. *)

MakeExpression[ RowBox[ {"-", "\[Infinity]"|"Infinity", c___}], fmt_] :=
	MakeExpression[ RowBox[ {RowBox[ {"DirectedInfinity", "[", "-1", "]"}], c}], fmt] /;
		$parseTheoremaExpressions	(* "-Infinity" should not be converted into "Minus[DirectedInfinity[1]]" *)
MakeExpression[ RowBox[ {"-", a_, c___}], fmt_] :=
	MakeExpression[ RowBox[ {RowBox[ {"Minus", "[", a, "]"}], c}], fmt] /;
		($parseTheoremaExpressions &&
		!NumberQ[ quietToAtom[ a]])		(* amaletzk: We don't want to convert negative numbers into "Minus[...]". *)
MakeExpression[ RowBox[ {a_, "-", b_, c___}], fmt_] := MakeExpression[ RowBox[ {RowBox[ {"Subtract", "[", a, ",", b, "]"}], c}], fmt] /; $parseTheoremaExpressions
MakeExpression[ RowBox[ {a_, "/", b_, c___}], fmt_] := MakeExpression[ RowBox[ {RowBox[ {"Divide", "[", a, ",", b, "]"}], c}], fmt] /; $parseTheoremaExpressions
MakeExpression[ FractionBox[ a_, b_], fmt_] := MakeExpression[ RowBox[ {"Divide", "[", a, ",", b, "]"}], fmt] /; $parseTheoremaExpressions
MakeExpression[ SqrtBox[ a_], fmt_] := MakeExpression[ RowBox[ {"Radical", "[", a, ",", 2, "]"}], fmt] /; $parseTheoremaExpressions
MakeExpression[ RadicalBox[ a_, b_], fmt_] := MakeExpression[ RowBox[ {"Radical", "[", a, ",", b, "]"}], fmt] /; $parseTheoremaExpressions

(* ::Subsubsection:: *)
(* Special connectives *)


MakeExpression[ RowBox[{left_, RowBox[{":", "\[NegativeThickSpace]\[NegativeThinSpace]", "\[DoubleLongLeftRightArrow]"}], right_}], fmt_] :=
    MakeExpression[ RowBox[{"IffDef", "[", RowBox[{left, ",", right}], "]"}], fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[{P_, "@", right_}], fmt_] :=
    MakeExpression[ RowBox[{"Componentwise", "[", RowBox[{P, ",", right}], "]"}], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

MakeExpression[ RowBox[{"\[Piecewise]", GridBox[ c:{({_, "\[DoubleLeftArrow]"|"\[DoubleLongLeftArrow]", _}|{RowBox[ {_, "\[DoubleLeftArrow]"|"\[DoubleLongLeftArrow]", _}]})..}, ___]}], fmt_] :=
	With[ {clauses = Riffle[ Map[ row2clause, c], ","]},
    	MakeExpression[ RowBox[{"Piecewise", "[", RowBox[ {"Tuple", "[", RowBox[ clauses], "]"}], "]"}], fmt]
	] /; $parseTheoremaExpressions

row2clause[ {RowBox[ l_]}] := row2clause[ l]
row2clause[ {e_, "\[DoubleLeftArrow]"|"\[DoubleLongLeftArrow]", "otherwise"}] := RowBox[ {"Tuple", "[", RowBox[ {e, ",", "True"}], "]"}]
row2clause[ {e_, "\[DoubleLeftArrow]"|"\[DoubleLongLeftArrow]", "\[Placeholder]"}] := RowBox[ {"Tuple", "[", RowBox[ {e, ",", "True"}], "]"}]
row2clause[ {e_, "\[DoubleLeftArrow]"|"\[DoubleLongLeftArrow]", c_}] := RowBox[ {"Tuple", "[", RowBox[ {e, ",", c}], "]"}]

(* Use "collectColumn" instead of "First" to treat nested GridBoxes correctly.
	Reason: If one enters a new row to a GridBox by hitting "Ctrl+Enter", it might be that the new row
	is in fact not added to the outermost GridBox, but rather a new GridBox is created. Still, it looks as if
	the row was added to the outermost GridBox, so finding the error would be complicated (for the user).
	However, I think there is no need to do this also with "Piecewise", because there 3 columns are required
	anyway, and adding a new row either REALLY adds a new row to the outermost GridBox, or, if not, it is easy to see
	that something went wrong. *)
MakeExpression[ RowBox[ {"\[And]", RowBox[{"\[Piecewise]", GridBox[ c:{{_}..}, ___]}]}], fmt_] :=
	With[ {clauses = Riffle[ Map[ collectColumn, c], ","]},
		MakeExpression[ RowBox[{"And", "[", RowBox[ clauses], "]"}], fmt]
	] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {"\[Or]", RowBox[{"\[Piecewise]", GridBox[ c:{{_}..}, ___]}]}], fmt_] :=
	With[ {clauses = Riffle[ Map[ collectColumn, c], ","]},
		MakeExpression[ RowBox[{"Or", "[", RowBox[ clauses], "]"}], fmt]
	] /; $parseTheoremaExpressions
	
MakeExpression[ RowBox[ {"\[DoubleLongLeftRightArrow]"|"\[DoubleLeftRightArrow]", RowBox[{"\[Piecewise]", GridBox[ c:{{_}..}, ___]}]}], fmt_] :=
	With[ {clauses = Riffle[ Map[ collectColumn, c], ","]},
		MakeExpression[ RowBox[{"Iff", "[", RowBox[ clauses], "]"}], fmt]
	] /; $parseTheoremaExpressions
	
collectColumn[ {GridBox[ l:{{_}..}, ___]}] := Apply[ Sequence, Map[ collectColumn, l]]
collectColumn[ {x_}] := x
	

(* ::Subsubsection:: *)
(* Indexed functions *)

(* amaletzk: Just leave subscripted functions as they are, such that, e.g., "min_<[A]" is transformed
	into "Subscript[min, <][A]", because this also works if functions are given without arguments. *)
(* MakeExpression[ RowBox[ {SubscriptBox[ f:("max"|"min"), ord_], "[", arg_, "]"}], fmt_] :=
	MakeExpression[ RowBox[ {f, "[", arg, ",", ord, "]"}], fmt] /; $parseTheoremaExpressions *)
	
	
(* ::Subsubsection:: *)
(* Chains of relations *)


MakeExpression[ RowBox[ l:{_, PatternSequence[ _?isTmaRelationBox, _]..}], fmt_] :=
	Module[ {ops, args},
		ops = Take[ l, {2, -1, 2}];
		If[ Length[ DeleteDuplicates[ ops]] === 1,
			args = Take[ l, {1, -1, 2}];
			MakeExpression[ RowBox[ {First[ops], "[", RowBox[ Riffle[ args, ","]], "]"}], fmt],
			
			MakeExpression[ RowBox[ {"OperatorChain", "[", RowBox[ Riffle[ l, ","]], "]"}], fmt]
		]
	] /; $parseTheoremaExpressions || $parseTheoremaGlobals
	
(*
MakeExpression[ RowBox[ l:{_, PatternSequence[ _?isTmaRelationBox, _]..}], fmt_] :=
	Module[ {ops, args},
		{args, ops} = flattenRelations[ l, {}, {}];
		If[ Length[ DeleteDuplicates[ ops]] === 1,
			MakeExpression[ RowBox[ {First[ops], "[", RowBox[ Riffle[ args, ","]], "]"}], fmt],
			MakeExpression[ RowBox[ {"OperatorChain", "[", RowBox[ Riffle[ Riffle[ args, ops], ","]], "]"}], fmt]
		]
	]
	
flattenRelations[ {RowBox[ l:{_, PatternSequence[ _?isTmaRelationBox, _]..}], rest__}, args_List, ops_List] :=
	flattenRelations[ Join[ l, {rest}], args, ops]
flattenRelations[ {a_, op_, rest__}, {args___}, {ops___}] :=
	flattenRelations[ {rest}, {args, a}, {ops, op}]
flattenRelations[ {RowBox[ l:{_, PatternSequence[ _?isTmaRelationBox, _]..}]}, args_List, ops_List] :=
	flattenRelations[ l, args, ops]
flattenRelations[ {a_}, {args___}, ops_List] :=
	{{args, a}, ops}
*)

	
(* ::Subsubsection:: *)
(* Number domains *)

(* Important: If a limit is "Infinity", it doesn't matter whether the interval is open or closed at this limit;
				"Infinity" is always excluded!
*)

isLeftIntervalBracket[ b_] := MemberQ[ {"(", "["}, b]
isRightIntervalBracket[ b_] := MemberQ[ {")", "]"}, b]
isLeftClosed[ b_] := Switch[ b, "(", "False", "[", "True"]
isRightClosed[ b_] := Switch[ b, ")", "False", "]", "True"]
posInfBox = RowBox[ {"DirectedInfinity", "[", "1", "]"}]
negInfBox = RowBox[ {"DirectedInfinity", "[", RowBox[ {"-", "1"}], "]"}]
makeDomainIntervalBox[ head_String, l_, u_, leftClosed_, rightClosed_] := RowBox[ {head, "[", RowBox[ {l, ",", u, ",", leftClosed, ",", rightClosed}], "]"}]

quietToAtom[ s_] :=
	Block[ {$parseTheoremaExpressions = False, $parseTheoremaGlobals = False},
		Module[ {out = Quiet[ Check[ ToExpression[ s, StandardForm, Hold], $Failed]]},
			If[ out =!= $Failed && out === Apply[ Hold, {ReleaseHold[ out]}],
				out = ReleaseHold[ out];
				If[ !AtomQ[ out], out = $Failed],
				out = $Failed
			];
			out
		]
	]

(* ::Subsubsubsection:: *)
(* \[DoubleStruckCapitalN] *)

(* Ellipsis-subscript without interval brackets *)
MakeExpression[ SubscriptBox[ "\[DoubleStruckCapitalN]", RowBox[ {l_, ",", "\[Ellipsis]", ",", u_}]], fmt_] :=
	MakeExpression[ makeDomainIntervalBox[ "IntegerInterval", makeMaxBox[ l, "0"], u, "True", "True"], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

(* Ellipsis-subscript with interval brackets
	The following 3 definitions are essentially the same, we only take care of the several possibilities how
	left/right brackets are arranged withing RowBox *)
MakeExpression[ SubscriptBox[ "\[DoubleStruckCapitalN]", RowBox[ {RowBox[ {left_?isLeftIntervalBracket, RowBox[ {l_, ",", "\[Ellipsis]", ",", u_}]}], right_?isRightIntervalBracket}]], fmt_] :=
	MakeExpression[ makeDomainIntervalBox[ "IntegerInterval", makeMaxBox[ l, "0"], u, isLeftClosed[ left], isRightClosed[ right]], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
MakeExpression[ SubscriptBox[ "\[DoubleStruckCapitalN]", RowBox[ {left_?isLeftIntervalBracket, RowBox[ {RowBox[ {l_, ",", "\[Ellipsis]", ",", u_}], right_?isRightIntervalBracket}]}]], fmt_] :=
	MakeExpression[ makeDomainIntervalBox[ "IntegerInterval", makeMaxBox[ l, "0"], u, isLeftClosed[ left], isRightClosed[ right]], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
MakeExpression[ SubscriptBox[ "\[DoubleStruckCapitalN]", RowBox[ {left_?isLeftIntervalBracket, RowBox[ {l_, ",", "\[Ellipsis]", ",", u_}], right_?isRightIntervalBracket}]], fmt_] :=
	MakeExpression[ makeDomainIntervalBox[ "IntegerInterval", makeMaxBox[ l, "0"], u, isLeftClosed[ left], isRightClosed[ right]], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

(* Single subscript indicating where to start from *)
MakeExpression[ SubscriptBox[ "\[DoubleStruckCapitalN]", l_], fmt_] :=
	MakeExpression[ makeDomainIntervalBox[ "IntegerInterval", makeMaxBox[ l, "0"], posInfBox, "True", "False"], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

(* No subscript at all; Start from 1.
	This case, unfortunately, can reasonably only be handled in "freshSymbol[]" in "Session.m" *)

makeMaxBox[ a_, b_] :=
	Module[ {aex = quietToAtom[ a], bex = quietToAtom[ b]},
		Which[ TrueQ[ Quiet[ Check[ aex >= bex, False]]],
			a,
			TrueQ[ Quiet[ Check[ bex >= aex, False]]],
			b,
			True,
			RowBox[ {"max", "[", RowBox[ {"{", RowBox[ {a, ",", b}], "}"}], "]"}]
		]
	]

(* ::Subsubsubsection:: *)
(* \[DoubleStruckCapitalZ], \[DoubleStruckCapitalQ], \[DoubleStruckCapitalR] *)

isZQR[ dom_] := MemberQ[ {"\[DoubleStruckCapitalZ]", "\[DoubleStruckCapitalQ]", "\[DoubleStruckCapitalR]"}, dom]

makeDomainInterval[ "\[DoubleStruckCapitalZ]"] := "IntegerInterval"
makeDomainInterval[ "\[DoubleStruckCapitalQ]"] := "RationalInterval"
makeDomainInterval[ "\[DoubleStruckCapitalR]"] := "RealInterval"

(* Ellipsis-subscript without interval brackets *)
MakeExpression[ SubscriptBox[ dom_?isZQR, RowBox[ {l_, ",", "\[Ellipsis]", ",", u_}]], fmt_] :=
	MakeExpression[ makeDomainIntervalBox[ makeDomainInterval[ dom], l, u, "True", "True"], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

(* Ellipsis-subscript with interval brackets
	The following definitions are essentially the same, we only take care of the several possibilities how
	left/right brackets are arranged withing RowBox *)
MakeExpression[ SubscriptBox[ dom_?isZQR, RowBox[ {RowBox[ {left_?isLeftIntervalBracket, RowBox[ {l_, ",", "\[Ellipsis]", ",", u_}]}], right_?isRightIntervalBracket}]], fmt_] :=
	MakeExpression[ makeDomainIntervalBox[ makeDomainInterval[ dom], l, u, isLeftClosed[ left], isRightClosed[ right]], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
MakeExpression[ SubscriptBox[ dom_?isZQR, RowBox[ {left_?isLeftIntervalBracket, RowBox[ {RowBox[ {l_, ",", "\[Ellipsis]", ",", u_}], right_?isRightIntervalBracket}]}]], fmt_] :=
	MakeExpression[ makeDomainIntervalBox[ makeDomainInterval[ dom], l, u, isLeftClosed[ left], isRightClosed[ right]], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
MakeExpression[ SubscriptBox[ dom_?isZQR, RowBox[ {left_?isLeftIntervalBracket, RowBox[ {l_, ",", "\[Ellipsis]", ",", u_}], right_?isRightIntervalBracket}]], fmt_] :=
	MakeExpression[ makeDomainIntervalBox[ makeDomainInterval[ dom], l, u, isLeftClosed[ left], isRightClosed[ right]], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

(* Single subscript indicating where to start from *)
MakeExpression[ SubscriptBox[ "\[DoubleStruckCapitalZ]", l_], fmt_] :=
	Module[ {lex = quietToAtom[ l]},
		If[ TrueQ[ Negative[ lex]],
			MakeExpression[ makeDomainIntervalBox[ "IntegerInterval", l, posInfBox, "True", "False"], fmt],
			(*else*)
			MakeExpression[ RowBox[ {"IntegerQuotientRing", "[", l, "]"}], fmt]
		]
	] /; $parseTheoremaExpressions || $parseTheoremaGlobals
MakeExpression[ SubsuperscriptBox[ "\[DoubleStruckCapitalZ]", m_, "\[PlusMinus]"], fmt_] :=
	MakeExpression[ RowBox[ {"IntegerQuotientRingPM", "[", m, "]"}], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals
MakeExpression[ SubscriptBox[ dom:("\[DoubleStruckCapitalQ]"|"\[DoubleStruckCapitalR]"), l_], fmt_] :=
	MakeExpression[ makeDomainIntervalBox[ makeDomainInterval[ dom], l, posInfBox, "True", "False"], fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

(* No subscript at all; Start from -Infinity.
	This case, unfortunately, can reasonably only be handled in "freshSymbol[]" in "Session.m" *)
	
(* ::Subsubsubsection:: *)
(* \[DoubleStruckCapitalC] *)

MakeExpression[ SubscriptBox[ "\[DoubleStruckCapitalC]", "P"], fmt_] :=
	MakeExpression[ "\[DoubleStruckCapitalC]P", fmt] /; $parseTheoremaExpressions || $parseTheoremaGlobals

(* ::Subsubsection:: *)
(* Tuple notations *)


MakeExpression[ SubscriptBox[ t_, RowBox[ {l_, "\[RightArrow]"|"\[Rule]", r_}]], fmt_] :=
	MakeExpression[ RowBox[ {"Insert", "[", RowBox[ {t, ",", l, ",", r}], "]"}], fmt] /; $parseTheoremaExpressions

MakeExpression[ SubscriptBox[ t_, RowBox[ {l_, "\[LeftArrow]"}]], fmt_] :=
	MakeExpression[ RowBox[ {"DeleteAt", "[", RowBox[ {t, ",", l}], "]"}], fmt] /; $parseTheoremaExpressions

MakeExpression[ SubscriptBox[ t_, RowBox[ {l_, "\[LeftArrowBar]"}]], fmt_] :=
	MakeExpression[ RowBox[ {"Delete", "[", RowBox[ {t, ",", l}], "]"}], fmt] /; $parseTheoremaExpressions
MakeExpression[ SubscriptBox[ t_, RowBox[ {RowBox[ {l1_, "\[LeftArrowBar]"}], l2:(PatternSequence[ ",", RowBox[ {_,"\[LeftArrowBar]"}]]...)}]], fmt_] :=
	MakeExpression[ RowBox[ {"Delete", "[", RowBox[ Join[ {t, ",", l1}, Replace[ {l2}, RowBox[ {x_, _}] :> x, {1}]]], "]"}], fmt] /; $parseTheoremaExpressions

MakeExpression[ SubscriptBox[ t_, RowBox[ {l_, "\[LeftArrow]", r_}]], fmt_] :=
	MakeExpression[ RowBox[ {"ReplacePart", "[", RowBox[ {t, ",", RowBox[ {"Tuple", "[", RowBox[ {l, ",", r}], "]"}]}], "]"}], fmt] /; $parseTheoremaExpressions
MakeExpression[ SubscriptBox[ t_, RowBox[ {RowBox[ {l1_, "\[LeftArrow]", r1_}], l2:(PatternSequence[ ",", RowBox[ {_, "\[LeftArrow]", _}]]...)}]], fmt_] :=
	MakeExpression[ RowBox[ {"ReplacePart", "[", RowBox[ Join[ {t, ",", RowBox[ {"Tuple", "[", RowBox[ {l1, ",", r1}], "]"}]},
		Replace[ {l2}, RowBox[ {x_, _, y_}] :> RowBox[ {"Tuple", "[", RowBox[ {x, ",", y}], "]"}], {1}]]], "]"}], fmt] /; $parseTheoremaExpressions
					
MakeExpression[ SubscriptBox[ t_, RowBox[ {l_, "\[LeftArrowBar]", r_}]], fmt_] :=
	MakeExpression[ RowBox[ {"Replace", "[", RowBox[ {t, ",", RowBox[ {"Tuple", "[", RowBox[ {l, ",", r}], "]"}]}], "]"}], fmt] /; $parseTheoremaExpressions
MakeExpression[ SubscriptBox[ t_, RowBox[ {RowBox[ {l1_, "\[LeftArrowBar]", r1_}], l2:(PatternSequence[ ",", RowBox[ {_, "\[LeftArrowBar]", _}]]...)}]], fmt_] :=
	MakeExpression[ RowBox[ {"Replace", "[", RowBox[ Join[ {t, ",", RowBox[ {"Tuple", "[", RowBox[ {l1, ",", r1}], "]"}]},
		Replace[ {l2}, RowBox[ {x_, _, y_}] :> RowBox[ {"Tuple", "[", RowBox[ {x, ",", y}], "]"}], {1}]]], "]"}], fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[{left_,"\[EmptyUpTriangle]", right_}], fmt_] :=
    MakeExpression[ RowBox[{"EmptyUpTriangle", "[", RowBox[{left, ",", right}], "]"}], fmt] /; $parseTheoremaExpressions

(* Use unicode characters for certain operations *)
(* amaletzk: Operator symbols do not have to be put inside TagBoxes here, because at the beginning of this file
	there are some rules that automatically remove all TagBoxes from symbols that occur at operator positions. *)
MakeExpression[ RowBox[ {l_, "\:293a", r_}], fmt_] := MakeExpression[ RowBox[ {"appendElem", "[", RowBox[{ l, ",", r}], "]"}], fmt] /; $parseTheoremaExpressions
(* The order of arguments must be exactly as in input, for otherwise we get incorrect output *)
MakeExpression[ RowBox[ {l_, "\:293b", r_}], fmt_] := MakeExpression[ RowBox[ {"prependElem", "[", RowBox[{ l, ",", r}], "]"}], fmt] /; $parseTheoremaExpressions
MakeExpression[ RowBox[ {l_, "\:22c8", r_}], fmt_] := MakeExpression[ RowBox[ {"joinTuples", "[", RowBox[{ l, ",", r}], "]"}], fmt] /; $parseTheoremaExpressions
MakeExpression[ RowBox[ {l_, "\:22ff", r_}], fmt_] := MakeExpression[ RowBox[ {"elemTuple", "[", RowBox[{ l, ",", r}], "]"}], fmt] /; $parseTheoremaExpressions


(* ::Subsubsection:: *)
(* Bracketted expressions *)

MakeExpression[ RowBox[ {"{", x___, "}"}], fmt_] :=
    MakeExpression[ RowBox[ {"Theorema`Common`makeSet", "[", x, "]"}], fmt] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {"\[LeftAngleBracket]", x___, "\[RightAngleBracket]"}], fmt_] :=
    MakeExpression[ RowBox[ {"Tuple", "[", x, "]"}], fmt] /; $parseTheoremaExpressions
	
(* Bracketting symbols do not occur at operator positions, therefore TagBoxes have to be used here. *)
Scan[
	With[ {left = #[[3]], right = #[[4]], name = #[[5]]},
		MakeExpression[ RowBox[ {TagBox[ left, ___], x___, TagBox[ right, ___]}], fmt_] :=
			(MakeExpression[ RowBox[ {name, "[", x, "]"}], fmt] /; $parseTheoremaExpressions)
	]&,
	specialBrackets
]

(* ::Subsection:: *)
(* operator underscript -> domain *)


(*
	The assumption is that prefix/infix/postfix operators with underscript are used for operators, which 
	translate correctly to some expression when used without the underscript.
*)

(* DELIMITERS *)
MakeExpression[ RowBox[ {UnderscriptBox[ op_, dom_], r_?isRightDelimiter}], fmt_] :=
    Module[ {},
        MakeExpression[ RowBox[ {makeDomainOperation[ dom, op], r}], fmt]
    ] /; $parseTheoremaExpressions
    
MakeExpression[ RowBox[ {l_?isLeftDelimiter, UnderscriptBox[ op_, dom_]}], fmt_] :=
    Module[ {},
        MakeExpression[ RowBox[ {l, makeDomainOperation[ dom, op]}], fmt]
    ] /; $parseTheoremaExpressions
    
MakeExpression[ RowBox[ {l_?isLeftDelimiter, UnderscriptBox[ op_, dom_], r_?isRightDelimiter}], fmt_] :=
    Module[ {},
        MakeExpression[ RowBox[ {l, makeDomainOperation[ dom, op], r}], fmt]
    ] /; $parseTheoremaExpressions
    
MakeExpression[ RowBox[ {l_?isLeftDelimiter, u_UnderscriptBox, r_}], fmt_] :=
    Module[ {},
        MakeExpression[ RowBox[ {l, RowBox[ {u, r}]}], fmt]
    ] /; $parseTheoremaExpressions
    
MakeExpression[ RowBox[ {l_, u_UnderscriptBox, r_?isRightDelimiter}], fmt_] :=
    Module[ {},
        MakeExpression[ RowBox[ {RowBox[ {l, u}], r}], fmt]
    ] /; $parseTheoremaExpressions

(* PREFIX *)
MakeExpression[ RowBox[ {UnderscriptBox[ "-", dom_], r_}], fmt_] :=
    Module[ {},
        MakeExpression[ RowBox[ {makeDomainOperation[ dom, "Minus"], "[", r, "]"}], fmt]
    ] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {UnderscriptBox[ op_, dom_], r_}], fmt_] :=
	makeDomainOperation[ MakeExpression[ dom, fmt], MakeExpression[ RowBox[{op, r}], fmt], Expression] /; $parseTheoremaExpressions

(* INFIX *)
MakeExpression[ RowBox[ {l_, rest:(PatternSequence[ UnderscriptBox[ "-", dom_], _]..)}], fmt_] :=
    Module[ {args = Prepend[ Take[ {rest}, {2, -1, 2}], l]},
        MakeExpression[ RowBox[ {makeDomainOperation[ dom, "Subtract"], "[", RowBox[ Riffle[ args, ","]], "]"}], fmt]
    ] /; $parseTheoremaExpressions

MakeExpression[ RowBox[ {l_, rest:(PatternSequence[ UnderscriptBox[ "/", dom_], _]..)}], fmt_] :=
    Module[ {args = Prepend[ Take[ {rest}, {2, -1, 2}], l]},
        MakeExpression[ RowBox[ {makeDomainOperation[ dom, "Divide"], "[", RowBox[ Riffle[ args, ","]], "]"}], fmt]
    ] /; $parseTheoremaExpressions
    
(* We have to consider the case where the operator symbol is a built-in relation separately, for otherwise
	we could get 'OperatorChain' as the head.
	Example: RowBox[{RowBox[{"a", ">", "b"}], UnderscriptBox["<", "D"], "c"}]
*)
MakeExpression[ RowBox[ {l_, rest:(PatternSequence[ UnderscriptBox[ op_?isTmaRelationBox, dom_], _]..)}], fmt_] :=
    Module[ {args = Prepend[ Take[ {rest}, {2, -1, 2}], l]},
        MakeExpression[ RowBox[ {makeDomainOperation[ dom, op], "[", RowBox[ Riffle[ args, ","]], "]"}], fmt]
    ] /; $parseTheoremaExpressions
    
MakeExpression[ RowBox[ {l_, UnderscriptBox[ op_, dom_], r_}], fmt_] :=
	makeDomainOperation[ MakeExpression[ dom, fmt], MakeExpression[ RowBox[{l, op, r}], fmt], Expression] /; $parseTheoremaExpressions
	
MakeExpression[ RowBox[ {l_, UnderscriptBox[ op_, dom_], r_, rest:(PatternSequence[ UnderscriptBox[ op_, dom_], _]..)}], fmt_] :=
    Module[ {args = Join[ {l, r}, Take[ {rest}, {2, -1, 2}]], expr, f},
    	expr = MakeExpression[ RowBox[ {l, op, r}], fmt];
    	(*
    	expr is the form that would result without the underscript, say f[l,r] with HoldComplete wrapped around, so expr[[1,0]] gives the desired Head, say "f".
    	It is important that we only consider the first two arguments, for otherwise we could get 'OperatorChain' as the head ALTHOUGH THE EXPRESSION IS NO CHAIN OF OPERATORS (see example above).
    	*)
    	f = Extract[ expr, {1, 0}, HoldComplete];
    	(* expr now becomes the "original" expression without domain underscript, and without unwanted OperatorChains. *)
    	expr = FlattenAt[ ReplacePart[ MakeExpression[ RowBox[ {"List", "[", RowBox[ Riffle[ args, ","]], "]"}], fmt], {1, 0} -> f], {1, 0}];
    	makeDomainOperation[ MakeExpression[ dom, fmt], expr, Expression]
    ] /; $parseTheoremaExpressions

(* POSTFIX *)
MakeExpression[ RowBox[ {l_, UnderscriptBox[ op_, dom_]}], fmt_] :=
	makeDomainOperation[ MakeExpression[ dom, fmt], MakeExpression[ RowBox[{l, op}], fmt], Expression] /; $parseTheoremaExpressions

(* GENERAL *)
MakeExpression[ RowBox[ {UnderscriptBox[ op_, dom_], RowBox[ {"[", p___, "]"}]}], fmt_] :=
	Module[ {},
        MakeExpression[ RowBox[ {makeDomainOperation[ dom, op], "[", p, "]"}], fmt]
    ] /; $parseTheoremaExpressions
MakeExpression[ RowBox[ {UnderscriptBox[ op_, dom_], "[", p___, "]"}], fmt_] :=
	Module[ {},
        MakeExpression[ RowBox[ {makeDomainOperation[ dom, op], "[", p, "]"}], fmt]
    ] /; $parseTheoremaExpressions

(* 'makeDomainOperation[ dom, op]' returns the box representation of 'DomainOperation[ dom, op]'. *)
makeDomainOperation[ dom_, op_] := RowBox[ {"DomainOperation", "[", RowBox[ {dom, ",", op}], "]"}]
(* 'makeDomainOperation[ dom, expr, Expression]' turns 'expr' into a domain-expression, by replacing its head 'f' by 'DomainOperation[ dom, f]'.
	'h' is supposed to be 'HoldComplete' or a related symbol. It is ensured that no unwanted evaluation takes place. *)
(*
makeDomainOperation[ dom:(h_[ _]), expr:(h_[ c:((s_Symbol)[ _, _, __])]), Expression] :=
	Module[ {l, p, f},
		(
			p = Table[ {1, 2*i}, {i, l/2}];
			f = Extract[ expr, p, h];
			If[ Length[ DeleteDuplicates[ f]] === 1,
				f = Join[ dom, First[ f]];
				ReplacePart[ ReplacePart[ Delete[ expr, p], {1, 0} -> f], {1, 0, 0} -> ToExpression[ "DomainOperation$TM"]],
     
				f = MapThread[ (#1 -> Join[ dom, #2])&, {p, f}];
				p = Map[ Append[ #, 0]&, p];
				ReplacePart[ ReplacePart[ expr, f], p -> ToExpression[ "DomainOperation$TM"]]
			]
		) /; (EvenQ[ l = Length[ c] - 1] && MemberQ[ {"OperatorChain", "OperatorChain$TM"}, SymbolName[ Unevaluated[ s]]])
	]
*)
makeDomainOperation[ dom:(h_[ _]), expr:(h_[ _[ ___]]), Expression] :=
	With[ {f = Join[ dom, Extract[ expr, {1, 0}, h]]},
		ReplacePart[ ReplacePart[ expr, {1, 0} -> f], {1, 0, 0} -> ToExpression[ "DomainOperation$TM"]]
	]
makeDomainOperation[ _, expr_, Expression] := expr


(* ::Subsection:: *)
(* Global Declarations *)


MakeExpression[ RowBox[ {a_, TagBox[ "\[DoubleLongRightArrow]", Identity, ___]}], fmt_] :=
	MakeExpression[ RowBox[ {a, "\[DoubleLongRightArrow]"}], fmt] /; $parseTheoremaGlobals

MakeExpression[ UnderscriptBox[ "\[ForAll]", rng_], fmt_] :=
    Block[ {$parseTheoremaExpressions = True},
    	standardGlobalQuantifier[ "globalForall", rng, "True", fmt]
    ] /; $parseTheoremaGlobals
    
MakeExpression[ UnderscriptBox[ UnderscriptBox[ "\[ForAll]", rng_], cond_], fmt_] :=
    Block[ {$parseTheoremaExpressions = True},
	    standardGlobalQuantifier[ "globalForall", rng, cond, fmt]
    ] /; $parseTheoremaGlobals

MakeExpression[ RowBox[ {UnderscriptBox[ "\[ForAll]", rng_], decl_}], fmt_] :=
	MakeExpression[ RowBox[ {UnderscriptBox[ UnderscriptBox[ "\[ForAll]", rng], "True"], decl}], fmt] /; $parseTheoremaGlobals

MakeExpression[ RowBox[ {UnderscriptBox[ UnderscriptBox[ "\[ForAll]", rng_], cond_], decl_}], fmt_] :=
	With[ {a = MakeExpression[ UnderscriptBox[ UnderscriptBox[ "\[ForAll]", rng], cond], fmt], d = MakeExpression[ decl, fmt]},
	    If[ MatchQ[ a, HoldComplete[ _[ r_, _[ r_, _]]]],
	    	Delete[ Insert[ a, d, {1, 2, 3}], {1, 2, 3, 0}],
	    (*else*)
	    	MakeExpression[ "nE", fmt]
	    ]
	] /; $parseTheoremaGlobals

MakeExpression[ RowBox[ {cond_, "\[Implies]"|"\[DoubleLongRightArrow]"|"\[DoubleRightArrow]"}], fmt_] :=
    Block[ {$parseTheoremaExpressions = True},
		MakeExpression[ RowBox[ {"globalImplies", "[", cond, "]"}], fmt]
    ] /; $parseTheoremaGlobals

MakeExpression[ RowBox[ {lhs_, ":=", UnderscriptBox[ "\[CapitalDelta]", rng_]}], fmt_] :=
	(* We use 'toDomSpecRangeBox', because of the special 'DOMEXTRNG$'-ranges. *)
	With[ {r = toDomSpecRangeBox[ rng]},
		MakeExpression[ RowBox[ {"domainConstruct", "[", RowBox[ {lhs, ",", RowBox[ {"QU$", "[", RowBox[ {r, ",", r}], "]"}]}], "]"}], fmt]
	] /; $parseTheoremaGlobals

toDomSpecRangeBox[ RowBox[ {v_, "\[Superset]", d_}]] := RowBox[ {"RNG$", "[", RowBox[ {"DOMEXTRNG$", "[", RowBox[ {v, ",", d}], "]"}], "]"}]
toDomSpecRangeBox[ v_String] := toRangeBox[ v]
toDomSpecRangeBox[ args___] := unexpected[ toDomSpecRangeBox, {args}]

MakeExpression[ UnderscriptBox[ "let", rng_], fmt_] :=
	(* We use the powerful 'makeRangeList' in order to have the many variants, multiranges, etc.
		However, only ABBRVRNG$ makes sense in a "let", and this we check below. *)
	With[ {s = makeRangeList[ rng]},
		If[ MatchQ[ s, {RowBox[ {"ABBRVRNG$", "[", _, "]"}]...}],
			With[ {r = toRangeBox[ s]},
				Block[ {$parseTheoremaExpressions = True},
					MakeExpression[
						RowBox[ {"QU$", "[", RowBox[ {r, ",", RowBox[ {"globalAbbrev", "[", r, "]"}]}], "]"}],
						fmt
					]
				]
			],
		(*else*)
			notification[ translate[ "invalidQuRange"], DisplayForm[ "Abbrev"], DisplayForm[ rng]];
			MakeExpression[ "nE", fmt]
		]
	] /; $parseTheoremaGlobals


(* ::Subsection:: *)
(* Auxiliary parsing functions *)


(* QU$ is an auxiliary tag introduced in quantifier MakeExpressions, which should be eliminated during expression parsing
	in markVariables. Any remaining QU$ actually indicates an error, and it will evaluate through this definition and
	throw an exception. *)
QU$[ args___] := unexpected[ QU$, {args}]

SetAttributes[ constructQuantifier, HoldRest]
constructQuantifier[ spec_, rng_, form_, fmt_] :=
	constructQuantifier[ spec, rng, form, Null, Null, fmt]
constructQuantifier[ spec_, rng_, form_, cond_, fmt_] :=
	constructQuantifier[ spec, rng, form, cond, Null, fmt]
constructQuantifier[ {name_, s_, c_, multi_, ranges_}, rng_, form_, cond_, sub_, fmt_] :=
	With[ {newCond = If[ cond === Null,
						If[ TrueQ[ c], {"True", ","}, {}],
						If[ TrueQ[ c], {cond, ","}, $Failed]
					]
			},
		If[ ListQ[newCond],
			With[ {newName = If[ sub === Null,
								name,
								Switch[ s,
									"Annotated",
									makeAnnotation[ SubscriptBox, name, sub],
									"DomainOperation",
									makeDomainOperation[ sub, name],
									_,
									$Failed
								]
							]
					},
				If[ newName =!= $Failed,
					With[ {r = makeRangeList[ rng]},
						If[ TrueQ[ multi] || Length[ r] === 1,
							If[ MatchQ[ r, {RowBox[ {ranges, "[", _, "]"}]...}],
								With[ {
											rb = toRangeBox[ r],
											newForm = If[ form === Null, getSingleRangeVar[ r], form]
										},
									If[ newForm =!= $Failed,
										With[ {expr = Join[ {rb, ","}, newCond, {newForm}]},
											MakeExpression[
												RowBox[ {"QU$", "[", RowBox[ {rb, ",", RowBox[ {newName, "[", RowBox[ expr], "]"}]}], "]"}],
												fmt
											]
										],
									(*else*)
										MakeExpression[ "nE", fmt]
									]
								],
							(*else*)
								notification[ translate[ "invalidQuRange"], DisplayForm[ name], DisplayForm[ rng]];
								MakeExpression[ "nE", fmt]
							],
						(*else*)
							notification[ translate[ "invalidQuVarNum"], DisplayForm[ name]];
							MakeExpression[ "nE", fmt]
						]
					],
				(*else*)
					notification[ translate[ "invalidQuSubscript"], DisplayForm[ name]];
					MakeExpression[ "nE", fmt]
				]
			],
		(*else*)
			notification[ translate[ "invalidQuCondition"], DisplayForm[ name]];
			MakeExpression[ "nE", fmt]
		]
	]
constructQuantifier[ ___] :=
	$Failed
    
SetAttributes[ standardGlobalQuantifier, HoldRest]
standardGlobalQuantifier[ name_, rng_, cond_, fmt_] :=
    With[ {r = toRangeBox[ rng]},
        MakeExpression[
        	RowBox[ {"QU$", "[", RowBox[ {r, ",", RowBox[ {name, "[", RowBox[ {r, ",", cond}], "]"}]}], "]"}],
        	fmt
        ]
    ]
standardGlobalQuantifier[ args___] := unexpected[ standardGlobalQuantifier, {args}]



(* ::Subsubsection:: *)
(* Ranges *)


toRangeBox[ {}] :=
	RowBox[ {"RNG$", "[", "]"}]
toRangeBox[ {r_}] :=
	RowBox[ {"RNG$", "[", r, "]"}]
toRangeBox[ r_List] :=
    RowBox[ {"RNG$", "[", RowBox[ Riffle[ r, ","]], "]"}]
toRangeBox[ s_] :=
	toRangeBox[ makeRangeList[ s]]
toRangeBox[ args___] := unexpected[ toRangeBox, {args}]

makeRangeList[ b_] :=
	With[ {r = makeUserRange[ Replace[ b, $tmaBoxToUserRange]]},
		r /; r =!= $Failed
	]

makeRangeList[ RowBox[ {v_, "\[Element]", s_}]] :=
	{makeSingleSetRange[ v, s]}

makeRangeList[ RowBox[ {x___, y_, ",", RowBox[ {v_, "\[Element]", s_}]}]] :=
    Append[ makeRangeList[ RowBox[ {x, RowBox[ {y, "\[Element]", s}]}]], makeSingleSetRange[ v, s]]

makeRangeList[ RowBox[ {p_, RowBox[ {"[", x__, "]"}]}]] :=
	makeRangeList[ RowBox[ {p, "[", x, "]"}]]
		
makeRangeList[ RowBox[ {p_, "[", RowBox[ {x__, ",", v_}], "]"}]] :=
	Append[ makeRangeList[ RowBox[ {p, "[", RowBox[ {x}], "]"}]], makeSinglePredRange[ v, p]]

makeRangeList[ RowBox[ {p_, "[", RowBox[ {v_}], "]"}]] :=
	{makeSinglePredRange[ v, p]}
	
makeRangeList[ RowBox[ {p_, "[", v:RowBox[ {_, ".."|"..."}], "]"}]] :=
	{makeSinglePredRange[ v, p]}

makeRangeList[ RowBox[ {p_, "[", v_String, "]"}]] :=
	{makeSinglePredRange[ v, p]}

makeRangeList[ RowBox[ {RowBox[ {v_, "=", lower_}], ",", "\[Ellipsis]", ",", upper_}]] :=
    {makeSingleStepRange[ v, lower, upper, "1"]}

makeRangeList[ RowBox[ {x___, y_, ",", RowBox[ {v_, "=", lower_}], ",", "\[Ellipsis]", ",", upper_}]] :=
    Append[ makeRangeList[ RowBox[ {x, RowBox[ {y, "=", lower}], ",", "\[Ellipsis]", ",", upper}]],
    	makeSingleStepRange[ v, lower, upper, "1"]]

makeRangeList[ RowBox[ {RowBox[ {v_, "=", lower_}], ",", OverscriptBox[ "\[Ellipsis]", step_], ",", upper_}]] :=
    {makeSingleStepRange[ v, lower, upper, step]}

makeRangeList[ RowBox[ {x___, y_, ",", RowBox[ {v_, "=", lower_}], ",", OverscriptBox[ "\[Ellipsis]", step_], ",", upper_}]] :=
    Append[ makeRangeList[ RowBox[ {x, RowBox[ {y, "=", lower}], ",", OverscriptBox[ "\[Ellipsis]", step], ",", upper}]],
    	makeSingleStepRange[ v, lower, upper, step]]

makeRangeList[ RowBox[ {a_, "=", e_}]] :=
	{makeSingleAbbrevRange[ a, e]}

makeRangeList[ RowBox[ {s_, ",", r__}]] :=
    Join[ makeRangeList[ s], makeRangeList[ RowBox[ {r}]]]

makeRangeList[ RowBox[ {s_}]] :=
    makeRangeList[ s]

makeRangeList[ GridBox[ r_List]] := Join @@ Map[ makeRangeList, Flatten[ r]]

makeRangeList[ s_] :=
    {RowBox[ {"SIMPRNG$", "[", s, "]"}]}
    
makeRangeList[ args___] := unexpected[ makeRangeList, {args}]

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

makeUserRange[ {name_, vars:{_, PatternSequence[ ",", _]...}, args_List}] :=
	Join @@ Map[ makeUserRange[ {name, #, args}]&, Part[ vars, 2 * Range[ (Length[ vars] + 1) / 2] - 1]]
makeUserRange[ {name_, RowBox[ list:{_, PatternSequence[ ",", _]...}], args_List}] :=
	makeUserRange[ {name, list, args}]
makeUserRange[ {name_, var_, {}}] :=
	{RowBox[ {name, "[", var, "]"}]}
makeUserRange[ {name_, var_, args_List}] :=
	{RowBox[ {name, "[", RowBox[ Riffle[ Prepend[ args, var], ","]], "]"}]}
makeUserRange[ ___] := $Failed

getSingleRangeVar[ {r_}] :=
	getSingleRangeVar[ r]
getSingleRangeVar[ RowBox[ {_String, "[", v:RowBox[ {_, ".."|"..."}], "]"}]] :=
	v
getSingleRangeVar[ RowBox[ {r_String, "[", RowBox[ {v_}], "]"}]] :=
	getSingleRangeVar[ RowBox[ {r, "[", v, "]"}]]
getSingleRangeVar[ RowBox[ {r_String, "[", RowBox[ {v_, ",", __}], "]"}]] :=
	getSingleRangeVar[ RowBox[ {r, "[", v, "]"}]]
getSingleRangeVar[ RowBox[ {_String, "[", v_, "]"}]] :=
	v
getSingleRangeVar[ _] :=
	$Failed
getSingleRangeVar[ args___] := unexpected[ getSingleRangeVar, {args}]


(* ::Subsubsection:: *)
(* Operators *)

(* The definitions in this subsubsection turn "+" into "Plus", if it appears without arguments; This also
	happens in case of sub/super/over -scripted symbols (like "+_0"). *)

(* Underscript is treated differently than the others, because it is assumed to be a domain underscript;
	See Section 'Under-, Over-, Sub-, Superscripts', subsection 'no arguments of domain underscript'. *)
MakeExpression[ (h:(OverscriptBox|SubscriptBox|SuperscriptBox))[ op_?((isTmaOperatorBox[ #, True])&), sc_], fmt_] :=
	MakeExpression[ makeAnnotation[ h, op, sc], fmt] /; ($parseTheoremaExpressions || $parseTheoremaGlobals)
MakeExpression[ (h:(UnderoverscriptBox|SubsuperscriptBox))[ op_?((isTmaOperatorBox[ #, True])&), sc1_, sc2_], fmt_] :=
	MakeExpression[ makeAnnotation[ h, op, sc1, sc2], fmt] /; ($parseTheoremaExpressions || $parseTheoremaGlobals)

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

SetAttributes[ makeAnnotation, HoldAllComplete];
makeAnnotation[ h_, f_, sc_] := RowBox[ {"Annotated", "[", RowBox[ {f, ",", RowBox[ {scriptBoxToString[ h], "[", sc, "]"}]}], "]"}]
makeAnnotation[ h_, f_, sc1_, sc2_] :=
	Module[ {h1, h2},
		{h1, h2} = scriptBoxToString[ h];
		RowBox[ {"Annotated", "[", RowBox[ {f, ",", RowBox[ {h1, "[", sc1, "]"}], ",", RowBox[ {h2, "[", sc2, "]"}]}], "]"}]
	]

(* 'makeAnnotationE' should not have any attributes. *)
makeAnnotationE[ expr:(h_[ _[ ___]]), sc:(h_[ _])] :=
	With[ {f = Join[ Extract[ expr, {1, 0}, h], sc]},
		ReplacePart[ ReplacePart[ expr, {1, 0} -> f], {1, 0, 0} -> ToExpression[ "Annotated$TM"]]
	]
makeAnnotationE[ expr:(h_[ _[ ___]]), sc1:(h_[ _]), sc2:(h_[ _])] :=
	With[ {f = Join[ Extract[ expr, {1, 0}, h], sc1, sc2]},
		ReplacePart[ ReplacePart[ expr, {1, 0} -> f], {1, 0, 0} -> ToExpression[ "Annotated$TM"]]
	]
makeAnnotationE[ expr_, __] := expr

(* Remark: We do NOT use "Subscript" below, but "SubScript" (upper-case "S"!), since "Subscript" already
	has some meaning in Theorema (accessing parts of tuples). Same for other script boxes. *)
scriptBoxToString[ OverscriptBox] = "OverScript"
scriptBoxToString[ SubscriptBox] = "SubScript"
scriptBoxToString[ SuperscriptBox] = "SuperScript"
scriptBoxToString[ UnderoverscriptBox] = {"UnderScript", "OverScript"}
scriptBoxToString[ SubsuperscriptBox] = {"SubScript", "SuperScript"}
scriptBoxToString[ _] = "List"

(* ::Subsection:: *)
(* Under-, Over-, Sub-, Superscripts *)

(* The definitions in this subsection handle sub/super/over -scripted operator symbols (like "+_0") if they
	appear WITH arguments. The case when they appear without arguments is treated above. *)
	
(* ::Subsubsection:: *)
(* Prefix *)

(* The scripts could be sequences of expressions, hence we need a head ("SubScript" etc.) around them for being parsed correctly. *)
MakeExpression[ RowBox[ {(h:(OverscriptBox|SubscriptBox|SuperscriptBox))[ op_?isTmaOperatorBox, sc_], r_}], fmt_] :=
	makeAnnotationE[ MakeExpression[ RowBox[ {op, r}], fmt], MakeExpression[ RowBox[ {scriptBoxToString[ h], "[", sc, "]"}], fmt]] /; $parseTheoremaExpressions
MakeExpression[ RowBox[ {(h:(UnderoverscriptBox|SubsuperscriptBox))[ op_?isTmaOperatorBox, sc1_, sc2_], r_}], fmt_] :=
	Module[ {h1, h2},
		{h1, h2} = scriptBoxToString[ h];
		makeAnnotationE[ MakeExpression[ RowBox[ {op, r}], fmt], MakeExpression[ RowBox[ {h1, "[", sc1, "]"}], fmt], MakeExpression[ RowBox[ {h2, "[", sc2, "]"}], fmt]]
	] /; $parseTheoremaExpressions
	
(* ::Subsubsection:: *)
(* Postfix *)

MakeExpression[ RowBox[ {l_, (h:(OverscriptBox|SubscriptBox|SuperscriptBox))[ op_?isTmaOperatorBox, sc_]}], fmt_] :=
	makeAnnotationE[ MakeExpression[ RowBox[ {l, op}], fmt], MakeExpression[ RowBox[ {scriptBoxToString[ h], "[", sc, "]"}], fmt]] /; $parseTheoremaExpressions
MakeExpression[ RowBox[ {l_, (h:(UnderoverscriptBox|SubsuperscriptBox))[ op_?isTmaOperatorBox, sc1_, sc2_]}], fmt_] :=
	Module[ {h1, h2},
		{h1, h2} = scriptBoxToString[ h];
		makeAnnotationE[ MakeExpression[ RowBox[ {l, op}], fmt], MakeExpression[ RowBox[ {h1, "[", sc1, "]"}], fmt], MakeExpression[ RowBox[ {h2, "[", sc2, "]"}], fmt]]
	] /; $parseTheoremaExpressions
	
(* ::Subsubsection:: *)
(* Infix *)
	
(* We need the first two rules here to deal with the special case if the operator is a built-in relation,
	for the same reason as with domain underscripts.
*)
MakeExpression[ RowBox[ {l_, rest:(PatternSequence[ (h:(OverscriptBox|SubscriptBox|SuperscriptBox))[ op_?isTmaRelationBox, sc_], _]..)}], fmt_] :=
	Module[ {args = Prepend[ Take[ {rest}, {2, -1, 2}], l]},
		MakeExpression[ RowBox[ {makeAnnotation[ h, op, sc], "[", RowBox[ Riffle[ args, ","]], "]"}], fmt]
	] /; $parseTheoremaExpressions
MakeExpression[ RowBox[ {l_, rest:(PatternSequence[ (h:(UnderoverscriptBox|SubsuperscriptBox))[ op_?isTmaRelationBox, sc1_, sc2_], _]..)}], fmt_] :=
	Module[ {args = Prepend[ Take[ {rest}, {2, -1, 2}], l]},
		MakeExpression[ RowBox[ {makeAnnotation[ h, op, sc1, sc2], "[", RowBox[ Riffle[ args, ","]], "]"}], fmt]
	] /; $parseTheoremaExpressions
	
MakeExpression[ RowBox[ {l_, (h:(OverscriptBox|SubscriptBox|SuperscriptBox))[ op_?isTmaOperatorBox, sc_], r_}], fmt_] :=
	makeAnnotationE[ MakeExpression[ RowBox[ {l, op, r}], fmt], MakeExpression[ RowBox[ {scriptBoxToString[ h], "[", sc, "]"}], fmt]] /; $parseTheoremaExpressions
MakeExpression[ RowBox[ {l_, operator:((h:(OverscriptBox|SubscriptBox|SuperscriptBox))[ op_?isTmaOperatorBox, sc_]), r_, rest:(PatternSequence[ operator_, _]..)}], fmt_] :=
	Module[ {args = Join[ {l, r}, Take[ {rest}, {2, -1, 2}]], expr, f},
    	expr = MakeExpression[ RowBox[ {l, op, r}], fmt];
    	(* It is important that we only consider the first two arguments, for otherwise we could get 'OperatorChain' as the head ALTHOUGH THE EXPRESSION IS NO CHAIN OF OPERATORS. *)
    	f = Extract[ expr, {1, 0}, HoldComplete];
    	(* expr now becomes the "original" expression without annotation, and without unwanted OperatorChains. *)
    	expr = FlattenAt[ ReplacePart[ MakeExpression[ RowBox[ {"List", "[", RowBox[ Riffle[ args, ","]], "]"}], fmt], {1, 0} -> f], {1, 0}];
    	makeAnnotationE[ expr, MakeExpression[ RowBox[ {scriptBoxToString[ h], "[", sc, "]"}], fmt]]
    ] /; $parseTheoremaExpressions
MakeExpression[ RowBox[ {l_, (h:(UnderoverscriptBox|SubsuperscriptBox))[ op_?isTmaOperatorBox, sc1_, sc2_], r_}], fmt_] :=
	Module[ {h1, h2},
		{h1, h2} = scriptBoxToString[ h];
		makeAnnotationE[ MakeExpression[ RowBox[ {l, op, r}], fmt], MakeExpression[ RowBox[ {h1, "[", sc1, "]"}], fmt], MakeExpression[ RowBox[ {h2, "[", sc2, "]"}], fmt]]
	] /; $parseTheoremaExpressions
MakeExpression[ RowBox[ {l_, operator:((h:(UnderoverscriptBox|SubsuperscriptBox))[ op_?isTmaOperatorBox, sc1_, sc2_]), r_, rest:(PatternSequence[ operator_, _]..)}], fmt_] :=
	Module[ {args = Join[ {l, r}, Take[ {rest}, {2, -1, 2}]], expr, f, h1, h2},
    	expr = MakeExpression[ RowBox[ {l, op, r}], fmt];
    	(* It is important that we only consider the first two arguments, for otherwise we could get 'OperatorChain' as the head ALTHOUGH THE EXPRESSION IS NO CHAIN OF OPERATORS. *)
    	f = Extract[ expr, {1, 0}, HoldComplete];
    	(* expr now becomes the "original" expression without annotation, and without unwanted OperatorChains. *)
    	expr = FlattenAt[ ReplacePart[ MakeExpression[ RowBox[ {"List", "[", RowBox[ Riffle[ args, ","]], "]"}], fmt], {1, 0} -> f], {1, 0}];
    	{h1, h2} = scriptBoxToString[ h];
    	makeAnnotationE[ expr, MakeExpression[ RowBox[ {h1, "[", sc1, "]"}], fmt], MakeExpression[ RowBox[ {h2, "[", sc2, "]"}], fmt]]
    ] /; $parseTheoremaExpressions
	
(* ::Subsubsection:: *)
(* Chains of operators *)

(* The following definition handles chains of operators (at least two operators),
	where at least one is no plain symbol (i.e. has some sort of annotation and/or domain underscript) *)
MakeExpression[ RowBox[ l:{_?((!(isLeftDelimiter[ #] || isRightDelimiter[ #]))&),
						pre:(PatternSequence[ _?isTmaOperatorBox,
							_?((!(isLeftDelimiter[ #] || isRightDelimiter[ #]))&)]...),
						op:Except[ _String] /; isTmaOperatorBox[ op],
						post:(PatternSequence[ _?((!(isLeftDelimiter[ #] || isRightDelimiter[ #]))&),
							_?isTmaOperatorBox]...),
						_?((!(isLeftDelimiter[ #] || isRightDelimiter[ #]))&)}], fmt_] :=
	Module[ {},
		MakeExpression[ RowBox[ {"OperatorChain", "[", RowBox[ Riffle[ l, ","]], "]"}], fmt]
	] /; ($parseTheoremaExpressions && Length[ l] > 3)
	
(* ::Subsubsection:: *)
(* No arguments of domain underscript *)

(* This definition must come after the quantifier definitions. *)
MakeExpression[ UnderscriptBox[ op_, dom_], fmt_] :=
	Module[ {},
		MakeExpression[ makeDomainOperation[ dom, op], fmt]
	] /; ($parseTheoremaExpressions || $parseTheoremaGlobals)
	

(* ::Section:: *)
(* MakeBoxes *)

SetAttributes[makeTmaBoxes, HoldAllComplete];
makeTmaBoxes[ b_] := MakeBoxes[ b, TheoremaForm]
	
(* DomainOperation$TM- and Annotated$TM-quantifiers are treated in "Expression.m" *)

(*
MakeBoxes[ (op_?isNonStandardOperatorName)[ arg___], TheoremaForm] :=
	With[ {b = Replace[ op, $tmaNonStandardOperatorToBuiltin]},
		MakeBoxes[ b[ arg], TheoremaForm]
	]
MakeBoxes[ (h:(Theorema`Language`TAG$|Theorema`Computation`Language`TAG$))[ op_?isNonStandardOperatorName, t_][ arg___], TheoremaForm] :=
	With[ {b = Replace[ op, $tmaNonStandardOperatorToBuiltin]},
		MakeBoxes[ h[ b, t][ arg], TheoremaForm]
	]
*)

If[ $VersionNumber >= 10.0,
	With[ {sym = Theorema`Language`Association$TM|Theorema`Computation`Language`Association$TM,
			left = "\:f113", right = "\:f114"},
		MakeBoxes[ sym[ e___], TheoremaForm] :=
			RowBox[
				{left, tmaInfixBox[ HoldComplete[ e], ","], right}
			];
		MakeBoxes[ (h:(Theorema`Language`TAG$|Theorema`Computation`Language`TAG$))[ sym, t_][ e___], TheoremaForm] :=
			RowBox[
				{
					tmaTagBox[ Left, left, t, h],
					tmaInfixBox[ HoldComplete[ e], ","],
					tmaTagBox[ Right, right, t, h]
				}
			]
	]
]

(*
	Parenthesizing of expressions is an issue that may need more attention in an improved implementation.
	Current solution: 
	1) Basically, we let Mma do the formatting including setting parentheses.
	2) We parenthesize expressions with "AutoParenthesies" like in input, except for 
			expressions that format as f[...] and
			expressions starting with a "("
	3) We do not parenthesize arithmetic expressions, subscripts, bracketing bar, etc.
	4) On demand, more exceptions can be implemented at this point.
*)
MakeBoxes[ (op_?isStandardOperatorName)[ arg__], TheoremaForm] :=
	(* Testing 'isStandardOperatorName' rules out, for instance, 'TAG$'. *)
	With[ {b = tmaToInputOperator[ op]},
    	(* Special cases, because otherwise And uses && and Or uses || *)
    	Switch[ b,
    		And,
    		tmaInfixBox[ HoldComplete[ arg], "\[And]", parenthesize],
    		Or,
    		tmaInfixBox[ HoldComplete[ arg], "\[Or]", parenthesize],
    		Not,
    		If[ MatchQ[ HoldComplete[ arg], HoldComplete[ _]],	(* 'arg' could consist of more than one element *)
    			RowBox[ {"\[Not]", parenthesize[ arg]}],
    		(*else*)
    			RowBox[ {"Not", "[", tmaInfixBox[ HoldComplete[ arg], ","], "]"}]
    		],
    		Plus,
    		RowBox[ makeSummands[ HoldComplete[ arg], True]],
    		Subtract,
    		RowBox[ makeSummands[ HoldComplete[ arg], False]],
    		Times|Divide|Power|Subscript|Slot,	(* If we put "Divide" here, we get a nice-looking FractionBox. *)
    		MakeBoxes[ b[ arg], TheoremaForm],
    		D,
    		RowBox[ {"D", "[", tmaInfixBox[ HoldComplete[ arg], ","], "]"}],	(* Otherwise the output is completely wrong. *)
    		_,
    		If[ isTmaOperatorName[ op],
    			(* This if-branch treats the case where 'op' is a Theorema operator occuring with non-empty argument list. *)
    			With[ {sym = Replace[ SymbolName[ op], $tmaNameToOperator], form = getTmaOperatorForms[ op]},
	    			If[ MatchQ[ HoldComplete[ arg], HoldComplete[ _]],
	    				Which[
							MemberQ[ form, Prefix],
							RowBox[ {sym, MakeBoxes[ arg, TheoremaForm]}],
							MemberQ[ form, Postfix],
							RowBox[ {MakeBoxes[ arg, TheoremaForm], sym}],
							form === {},
							RowBox[ {sym, "[", MakeBoxes[ arg, TheoremaForm], "]"}],
							True,
							RowBox[ {RowBox[ {TagBox[ "(", "AutoParentheses"], sym, TagBox[ ")", "AutoParentheses"]}], "[", MakeBoxes[ arg, TheoremaForm], "]"}]
						],
					(*else*)
						If[ MemberQ[ form, Infix],
							tmaInfixBox[ HoldComplete[ arg], sym, parenthesize],
						(*else*)
							RowBox[ {RowBox[ {TagBox[ "(", "AutoParentheses"], sym, TagBox[ ")", "AutoParentheses"]}], "[", tmaInfixBox[ HoldComplete[ arg], ","], "]"}]
						]
	    			]
    			],
    		(*else*)
    			parenthesize[ b[ arg]]
    		]
    	]
    ]
MakeBoxes[ (h:(Theorema`Language`TAG$|Theorema`Computation`Language`TAG$))[ op_Symbol, t_][ arg__], TheoremaForm] :=
	With[ {b = tmaToInputOperator[ op]},
    	(* Special cases, because otherwise And uses && and Or uses || *)
    	Switch[ b,
    		And,
    		tmaInfixBox[ HoldComplete[ arg], tmaTagBox[ Infix, "\[And]", t, h], parenthesize],
    		Or,
    		tmaInfixBox[ HoldComplete[ arg], tmaTagBox[ Infix, "\[Or]", t, h], parenthesize],
    		Not,
    		If[ MatchQ[ HoldComplete[ arg], HoldComplete[ _]],
    			RowBox[ {tmaTagBox[ Prefix, "\[Not]", t, h], parenthesize[ arg]}],
    		(*else*)
    			RowBox[ {tmaTagBox[ None, "Not", t, h], "[", tmaInfixBox[ HoldComplete[ arg], ","], "]"}]
    		],
    		D,
    		RowBox[ {tmaTagBox[ None, "D", t, h], "[", tmaInfixBox[ HoldComplete[ arg], ","], "]"}],
    		_,
    		If[ isTmaOperatorName[ op],
    			(* This if-branch treats the case where 'op' is a Theorema operator occuring with non-empty argument list. *)
    			With[ {sym = Replace[ SymbolName[ op], $tmaNameToOperator], form = getTmaOperatorForms[ op]},
	    			Switch[ HoldComplete[ arg],
	    				HoldComplete[ _],
	    				Which[
							MemberQ[ form, Prefix],
							RowBox[ {tmaTagBox[ Prefix, sym, t, h], MakeBoxes[ arg, TheoremaForm]}],
						(*else*)
							MemberQ[ form, Postfix],
							RowBox[ {MakeBoxes[ arg, TheoremaForm], tmaTagBox[ Postfix, sym, t, h]}],
						(*else*)
							form === {},
							RowBox[ {tmaTagBox[ None, sym, t, h], "[", MakeBoxes[ arg, TheoremaForm], "]"}],
						(*else*)
							True,
							RowBox[ {RowBox[ {TagBox[ "(", "AutoParentheses"], tmaTagBox[ None, sym, t, h], TagBox[ ")", "AutoParentheses"]}], "[", MakeBoxes[ arg, TheoremaForm], "]"}]
						],
						
						_,
						If[ MemberQ[ form, Infix],
							tmaInfixBox[ HoldComplete[ arg], tmaTagBox[ Infix, sym, t, h], parenthesize],
						(*else*)
							RowBox[ {RowBox[ {TagBox[ "(", "AutoParentheses"], tmaTagBox[ None, sym, t, h], TagBox[ ")", "AutoParentheses"]}], "[", tmaInfixBox[ HoldComplete[ arg], ","], "]"}]
						]
	    			]
    			],
    		(*else*)
    			RowBox[ {tmaTagBox[ None, b, t, h], "[", tmaInfixBox[ HoldComplete[ arg], ","], "]"}]
    		]
    	]
    ]
	
makeSummands[ arg:HoldComplete[ a_], True] /; !isIndividual[ arg] :=
	{"Plus", "[", MakeBoxes[ a, TheoremaForm], "]"}
makeSummands[ HoldComplete[ a_, rest___], positive_] :=
	makeSummands[ HoldComplete[ rest], {MakeBoxes[ a, TheoremaForm]}, If[ TrueQ[ positive], {"+", "-"}, {"-", "+"}]]
makeSummands[ HoldComplete[ a_?isNegative, rest___], {summands__}, symbols:{_, sym_String}] :=
	Module[ {a0, p},
		{a0, p} = neg[ a];
		a0 = makeTmaBoxes@@a0;
		Switch[ p,
			True,
			a0 = RowBox[ {"(", a0, ")"}],
			Invisible,
			a0 = RowBox[ {TagBox[ "(", "AutoParentheses"], a0, TagBox[ ")", "AutoParentheses"]}]
		];
		makeSummands[ HoldComplete[ rest], {summands, sym, a0}, symbols]
	]
makeSummands[ HoldComplete[ a_, rest___], {summands__}, symbols:{sym_String, _}] :=
	Module[ {a0 = MakeBoxes[ a, TheoremaForm]},
		If[ sym === "-",
			Switch[ Head[ a],
				Theorema`Language`Plus$TM|Theorema`Computation`Language`Plus$TM|Theorema`Language`Subtract$TM|Theorema`Computation`Language`Subtract$TM,
				a0 = RowBox[ {"(", a0, ")"}],
				Complex,
				a0 = RowBox[ {TagBox[ "(", "AutoParentheses"], a0, TagBox[ ")", "AutoParentheses"]}]
			]
		];
		makeSummands[ HoldComplete[ rest], {summands, sym, a0}, symbols]
	]
makeSummands[ HoldComplete[ ], summands_List, _List] := summands

SetAttributes[ isNegative, HoldAllComplete];
isNegative[ Complex[ 0, (_Integer|_Rational|_Real)?Negative]] := True
isNegative[ Complex[ (_Integer|_Rational|_Real)?Negative, _Integer|_Rational|_Real]] := True
isNegative[ (Theorema`Language`Minus$TM|Theorema`Computation`Language`Minus$TM)[ _]] := True
isNegative[ (Theorema`Language`Times$TM|Theorema`Computation`Language`Times$TM)[ _?isNegative, ___]] := True
isNegative[ a:(_Integer|_Rational|_Real)] := Negative[ a]
isNegative[ _] := False

SetAttributes[ neg, HoldAllComplete];
neg[ Complex[ 0, b:(_Integer|_Rational|_Real)]] :=
	With[ {b0 = -b},
		{HoldComplete[ b0*I], False}
	]
neg[ Complex[ a:(_Integer|_Rational|_Real), b:(_Integer|_Rational|_Real)]] :=
	With[ {out = Complex[ -a, -b]},
		{HoldComplete[ out], True}
	]
neg[ Theorema`Language`Minus$TM[ a:((_[ _])|((Theorema`Language`Times$TM|Theorema`Computation`Language`Times$TM)[ _?isNegative, __]))]] :=
	{HoldComplete[ a], Invisible}
neg[ Theorema`Language`Minus$TM[ a:(h_[ _, __])]] :=
	{HoldComplete[ a], !MemberQ[ {Theorema`Language`Times$TM, Theorema`Computation`Language`Times$TM, Theorema`Language`Power$TM, Theorema`Computation`Language`Power$TM}, h]}
neg[ Theorema`Language`Minus$TM[ a_]] := {HoldComplete[ a], False}
neg[ Theorema`Computation`Language`Minus$TM[ a_]] := neg[ Theorema`Language`Minus$TM[ a]]
neg[ (Theorema`Language`Times$TM|Theorema`Computation`Language`Times$TM)[ -1, a_]] := neg[ Theorema`Language`Minus$TM[ a]]
neg[ (h:(Theorema`Language`Times$TM|Theorema`Computation`Language`Times$TM))[ -1, a__]] := {HoldComplete[ h[ a]], False}
neg[ (h:(Theorema`Language`Times$TM|Theorema`Computation`Language`Times$TM))[ a_, b__]] :=
	With[ {a0 = Join[ First[ neg[ a]], HoldComplete[ b]]},
		{ReplacePart[ HoldComplete[ a0], {1, 0} -> h], False}
	]
neg[ a_] := With[ {a0 = -a}, {HoldComplete[ a0], False}]


(* 'parenthesize' formats the given expression and additionally puts the result inside parentheses, if necessary. *)
SetAttributes[ parenthesize, HoldAllComplete]
parenthesize[ expr_] :=
	With[ {box = MakeBoxes[ expr, TheoremaForm]},
    With[ {box0 = NestWhile[ First, box, MatchQ[ #, TagBox[ _, _Theorema`Language`TAG$|_Theorema`Language`TAG$, ___]]&]},
        If[ MatchQ[ box0, RowBox[ {__}]] &&
        		!MatchQ[ box0,
        			RowBox[ {_, _?(MemberQ[ {"[", "\[LeftDoubleBracket]"}, getLeftDelimiter[ #]] &), ___, _?(MemberQ[ {"]", "\[RightDoubleBracket]"}, getRightDelimiter[ #]] &)}]|
        				RowBox[ {_?isLeftDelimiter, ___, _?isRightDelimiter}]
        		],
            RowBox[ {TagBox[ "(", "AutoParentheses"], box, TagBox[ ")", "AutoParentheses"]}],
        (*else*)
        	box
        ]
    ]]
parenthesize[ args___] := unexpected[ parenthesize, {args}]

(* The following definitions turn "Plus" into "+" if it occurs without arguments or with an empty
	argument list. The case when it occurs with a non-empty argument list is treated above, in the
	definition with "isStandardOperatorSymbol". Annotated operators as well as domain operators
	are treated in 'Expressions.m'. *)
MakeBoxes[ s_?isTmaOperatorName, TheoremaForm] := Replace[ SymbolName[ s], $tmaNameToOperator]
MakeBoxes[ (s_?isTmaOperatorName)[], TheoremaForm] :=
	With[ {sym = Replace[ SymbolName[ s], $tmaNameToOperator]},
		If[ getTmaOperatorForms[ s] === {},
			RowBox[ {sym, "[", "]"}],
		(*else*)
			RowBox[ {RowBox[ {TagBox[ "(", "AutoParentheses"], sym, TagBox[ ")", "AutoParentheses"]}], "[", "]"}]
		]
	]
MakeBoxes[ (h:(Theorema`Language`TAG$|Theorema`Computation`Language`TAG$))[ s_?isTmaOperatorName, t_][], TheoremaForm] :=
	With[ {box = tmaTagBox[ None, Replace[ SymbolName[ s], $tmaNameToOperator], t, h]},
		If[ getTmaOperatorForms[ s] === {},
			RowBox[ {box, "[", "]"}],
		(*else*)
			RowBox[ {RowBox[ {TagBox[ "(", "AutoParentheses"], box, TagBox[ ")", "AutoParentheses"]}], "[", "]"}]
		]
	]
    
MakeBoxes[ s_Symbol, TheoremaForm] := 
	(* We have to use "Unevaluated" here, because "I" is a symbol, but evaluates to "Complex[0, 1]" *)
	Module[ {n = SymbolName[ Unevaluated[ s]], l},
		l = StringLength[ n];
		If[ l > 3 && StringTake[ n, -3] === "$TM",
			If[ l > 7 && StringTake[ n, 4] === "VAR$", (* Prefix "VAR$" is only dropped in presence of suffix "$TM" *)
				StringTake[ n, {5, l - 3}],
				StringDrop[ n, -3]
			],
			n
		]
	]

MakeBoxes[ (h:(Theorema`Language`TAG$|Theorema`Computation`Language`TAG$))[ expr_, t_], TheoremaForm] :=
	tmaTagBox[ None, MakeBoxes[ expr, TheoremaForm], t, h]

tmaInfixBox[ HoldComplete[], ",", ___] :=
	Sequence[]
tmaInfixBox[ HoldComplete[ a_], __] :=
	MakeBoxes[ a, TheoremaForm]
tmaInfixBox[ args_HoldComplete, op_] :=
	tmaInfixBox[ args, op, makeTmaBoxes]
tmaInfixBox[ args_HoldComplete, op_, f_] :=
	RowBox[ Riffle[ List @@ (f /@ args), op]]
tmaInfixBox[ args___] := unexpected[ tmaInfixBox, {args}]

(* We cannot simply write 'TAG$[ tag]', since 'TAG$' must be in the right context! *)
tmaTagBox[ syntax:(Infix|Prefix|Postfix), box_, tag_, h_] := tmaTagBox[ syntax, box, tag, h, box]
tmaTagBox[ Infix, box_, tag_, h_, op_String] := TagBox[ box, h[ tag], SyntaxForm -> "x" <> op <> "y"]
tmaTagBox[ Prefix, box_, tag_, h_, op_String] := TagBox[ box, h[ tag], SyntaxForm -> op <> "x"]
tmaTagBox[ Postfix, box_, tag_, h_, op_String] := TagBox[ box, h[ tag], SyntaxForm -> "x" <> op]
tmaTagBox[ Left, box_, tag_, h_, ___] := TagBox[ box, h[ tag], SyntaxForm -> "("]
tmaTagBox[ Right, box_, tag_, h_, ___] := TagBox[ box, h[ tag], SyntaxForm -> ")"]
tmaTagBox[ _, box_, tag_, h_, ___] := TagBox[ box, h[ tag]]

initParser[];

End[];
EndPackage[];

