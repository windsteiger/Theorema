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

BeginPackage["Theorema`Computation`Language`"]

Needs[ "Theorema`Common`"]

(*
   Load the same symbols like in Theorema`Language` so that all language constructs will be
   available in Computation context as well *)
Map[ Get, FileNames[ "*.m", FileNameJoin[{$TheoremaDirectory, "Theorema", "Language", "LanguageData"}]]];

Begin[ "`Private`"]

cleanupComputation[ ] :=
	Module[{},
		Clear[ "Theorema`Computation`Knowledge`*"]
	]
cleanupComputation[ args___] := unexpected[ cleanupComputation, {args}]

kbSelectCompute[_] := False;

buiActive[ f_String] :=
	Switch[ $computationContext,
		"prove",
		buiActProve[ f], 
		"compute",
		buiActComputation[ f],
		"solve",
		buiActSolve[ f]
	]
buiActive[ args___] := unexpected[ buiActive, {args}]

setComputationContext[ c_String] :=
    Module[ {},
        $computationContext = c;
    ]
setComputationContext[ args___] := unexpected[ setComputationContext, {args}]


(* ::Section:: *)
(* Logical Abbreviations *)

(* 'getOperatorPosition' returns the position of the main operator in an annotated/domain operator. *)
getOperatorPosition[ DomainOperation$TM[ _, op_], {pos___}] := getOperatorPosition[ op, {pos, 2}]
getOperatorPosition[ Annotated$TM[ op_, __], {pos___}] := getOperatorPosition[ op, {pos, 1}]
getOperatorPosition[ op_Symbol, pos_List] := pos
getOperatorPosition[ _] := $Failed

(* 'getOperator' retrieves the main operator from an annotated/domain operator. *)
getOperator[ expr_] :=
	Module[ {p = getOperatorPosition[ expr, {}]},
		Switch[ p,
			{},
			expr,
			{__Integer},
			Extract[ expr, p],
			_,
			$Failed
		]
	]
	
(* 'setOperator' sets the main operator of an annotated/domain operator. *)
setOperator[ op_, new_] :=
	Module[ {pos = getOperatorPosition[ op, {}]},
		Switch[ pos,
			{},
			new,
			{__Integer},
			ReplacePart[ op, pos :> new],
			_,
			op
		]
	]

isPosRelation[ "Equal"|Equal$TM] := buiActive["Equal"]
isPosRelation[ "Less"|Less$TM] := buiActive["Less"]
isPosRelation[ "LessEqual"|LessEqual$TM] := buiActive["LessEqual"]
isPosRelation[ "Greater"|Greater$TM] := buiActive["Greater"]
isPosRelation[ "GreaterEqual"|GreaterEqual$TM] := buiActive["GreaterEqual"]
isPosRelation[ "Subset"|Subset$TM] := buiActive["Subset"]
isPosRelation[ "SubsetEqual"|SubsetEqual$TM] := buiActive["SubsetEqual"]
isPosRelation[ "Superset"|Superset$TM] := buiActive["Superset"]
isPosRelation[ "SupersetEqual"|SupersetEqual$TM] := buiActive["SupersetEqual"]
isPosRelation[ "Element"|"ReverseElement"|Element$TM|ReverseElement$TM] := buiActive["IsElement"]
isPosRelation[ _] := False

isNegRelation[ "Unequal"|Unequal$TM] := buiActive["Equal"]
isNegRelation[ "NotLess"|NotLess$TM] := buiActive["Less"]
isNegRelation[ "NotLessEqual"|NotLessEqual$TM] := buiActive["LessEqual"]
isNegRelation[ "NotGreater"|NotGreater$TM] := buiActive["Greater"]
isNegRelation[ "NotGreaterEqual"|NotGreaterEqual$TM] := buiActive["GreaterEqual"]
isNegRelation[ "NotSubset"|NotSubset$TM] := buiActive["Subset"]
isNegRelation[ "NotSubsetEqual"|NotSubsetEqual$TM] := buiActive["SubsetEqual"]
isNegRelation[ "NotSuperset"|NotSuperset$TM] := buiActive["Superset"]
isNegRelation[ "NotSupersetEqual"|NotSupersetEqual$TM] := buiActive["SupersetEqual"]
isNegRelation[ "NotElement"|"NotReverseElement"|NotElement$TM|NotReverseElement$TM] := buiActive["IsElement"]
isNegRelation[ _] := False

negateRelation[ Unequal$TM] := Equal$TM
negateRelation[ Equal$TM] := Unequal$TM
negateRelation[ op_Symbol] :=
	Module[ {name = SymbolName[ op]},
		If[ StringLength[ name] > 3 && StringTake[ name, 3] === "Not",
			ToExpression[ StringDrop[ name, 3]],
			ToExpression[ StringJoin[ "Not", name]]
		]
	]
	
Equal$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isPosRelation["Equal"] :=
	Flatten[ And$TM @@ MapThread[ Hold[ Equal$TM[ #1, #2]]&, {{a, b}, {b, c}}], 1, Hold]

(*Unequal$TM[ a_, b_] /; a=!=b := Module[ {u = Union[ {a, b}]}, Apply[ Unequal$TM, u] /; u =!= {a, b}]*)
Unequal$TM[ a_?isIndividual] /; isNegRelation["Unequal"] :=
	Not$TM[ Equal$TM[ a]]
Unequal$TM[ a_?isIndividual, b_?isIndividual] /; isNegRelation["Unequal"] :=
	Not$TM[ Equal$TM[ a, b]]
Unequal$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isNegRelation["Unequal"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ Not$TM[ Equal$TM[ #1, #2]]]&, {{a, b}, {b, c}}]], 1, Hold]

Less$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isPosRelation["Less"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ Less$TM[ #1, #2]]&, {{a, b}, {b, c}}]], 1, Hold]
NotLess$TM[ a_?isIndividual] /; isNegRelation["NotLess"] :=
	Not$TM[ Less$TM[ a]]
NotLess$TM[ a_?isIndividual, b_?isIndividual] /; isNegRelation["NotLess"] :=
	Not$TM[ Less$TM[ a, b]]
NotLess$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isNegRelation["NotLess"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ Not$TM[ Less$TM[ #1, #2]]]&, {{a, b}, {b, c}}]], 1, Hold]

LessEqual$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isPosRelation["LessEqual"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ LessEqual$TM[ #1, #2]]&, {{a, b}, {b, c}}]], 1, Hold]
NotLessEqual$TM[ a_?isIndividual] /; isNegRelation["NotLessEqual"] :=
	Not$TM[ LessEqual$TM[ a]]
NotLessEqual$TM[ a_?isIndividual, b_?isIndividual] /; isNegRelation["NotLessEqual"] :=
	Not$TM[ LessEqual$TM[ a, b]]
NotLessEqual$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isNegRelation["NotLessEqual"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ Not$TM[ LessEqual$TM[ #1, #2]]]&, {{a, b}, {b, c}}]], 1, Hold]

Greater$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isPosRelation["Greater"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ Greater$TM[ #1, #2]]&, {{a, b}, {b, c}}]], 1, Hold]
NotGreater$TM[ a_?isIndividual] /; isNegRelation["NotGreater"] :=
	Not$TM[ Greater$TM[ a]]
NotGreater$TM[ a_?isIndividual, b_?isIndividual] /; isNegRelation["NotGreater"] :=
	Not$TM[ Greater$TM[ a, b]]
NotGreater$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isNegRelation["NotGreater"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ Not$TM[ Greater$TM[ #1, #2]]]&, {{a, b}, {b, c}}]], 1, Hold]

GreaterEqual$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isPosRelation["GreaterEqual"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ GreaterEqual$TM[ #1, #2]]&, {{a, b}, {b, c}}]], 1, Hold]
NotGreaterEqual$TM[ a_?isIndividual] /; isNegRelation["NotGreaterEqual"] :=
	Not$TM[ GreaterEqual$TM[ a]]
NotGreaterEqual$TM[ a_?isIndividual, b_?isIndividual] /; isNegRelation["NotGreaterEqual"] :=
	Not$TM[ GreaterEqual$TM[ a, b]]
NotGreaterEqual$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isNegRelation["NotGreaterEqual"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ Not$TM[ GreaterEqual$TM[ #1, #2]]]&, {{a, b}, {b, c}}]], 1, Hold]

Subset$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isPosRelation["Subset"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ Subset$TM[ #1, #2]]&, {{a, b}, {b, c}}]], 1, Hold]
NotSubset$TM[ a_?isIndividual] /; isNegRelation["NotSubset"] :=
	Not$TM[ Subset$TM[ a]]
NotSubset$TM[ a_?isIndividual, b_?isIndividual] /; isNegRelation["NotSubset"] :=
	Not$TM[ Subset$TM[ a, b]]
NotSubset$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isNegRelation["NotSubset"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ Not$TM[ Subset$TM[ #1, #2]]]&, {{a, b}, {b, c}}]], 1, Hold]

SubsetEqual$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isPosRelation["SubsetEqual"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ SubsetEqual$TM[ #1, #2]]&, {{a, b}, {b, c}}]], 1, Hold]
NotSubsetEqual$TM[ a_?isIndividual] /; isNegRelation["NotSubsetEqual"] :=
	Not$TM[ SubsetEqual$TM[ a]]
NotSubsetEqual$TM[ a_?isIndividual, b_?isIndividual] /; isNegRelation["NotSubsetEqual"] :=
	Not$TM[ SubsetEqual$TM[ a, b]]
NotSubsetEqual$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isNegRelation["NotSubsetEqual"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ Not$TM[ SubsetEqual$TM[ #1, #2]]]&, {{a, b}, {b, c}}]], 1, Hold]

Superset$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isPosRelation["Superset"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ Superset$TM[ #1, #2]]&, {{a, b}, {b, c}}]], 1, Hold]
NotSuperset$TM[ a_?isIndividual] /; isNegRelation["NotSuperset"] :=
	Not$TM[ Superset$TM[ a]]
NotSuperset$TM[ a_?isIndividual, b_?isIndividual] /; isNegRelation["NotSuperset"] :=
	Not$TM[ Superset$TM[ a, b]]
NotSuperset$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isNegRelation["NotSuperset"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ Not$TM[ Superset$TM[ #1, #2]]]&, {{a, b}, {b, c}}]], 1, Hold]

SupersetEqual$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isPosRelation["SupersetEqual"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ SupersetEqual$TM[ #1, #2]]&, {{a, b}, {b, c}}]], 1, Hold]
NotSupersetEqual$TM[ a_?isIndividual] /; isNegRelation["NotSupersetEqual"] :=
	Not$TM[ SupersetEqual$TM[ a]]
NotSupersetEqual$TM[ a_?isIndividual, b_?isIndividual] /; isNegRelation["NotSupersetEqual"] :=
	Not$TM[ SupersetEqual$TM[ a, b]]
NotSupersetEqual$TM[ a_?isIndividual, b_?isIndividual, c__?isIndividual] /; isNegRelation["NotSupersetEqual"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ Not$TM[ SupersetEqual$TM[ #1, #2]]]&, {{a, b}, {b, c}}]], 1, Hold]
	
Element$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isPosRelation["Element"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ Element$TM[ #1, #2]]&, {{a, b}, {b, c}}]], 1, Hold]
NotElement$TM[ a_?isIndividual] /; isNegRelation["NotElement"] :=
	Not$TM[ Element$TM[ a]]
NotElement$TM[ a_?isIndividual, b_?isIndividual] /; isNegRelation["NotElement"] :=
	Not$TM[ Element$TM[ a, b]]
NotElement$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isNegRelation["NotElement"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ Not$TM[ Element$TM[ #1, #2]]]&, {{a, b}, {b, c}}]], 1, Hold]

ReverseElement$TM[ a_?isIndividual, b_?isIndividual] /; isPosRelation["ReverseElement"] :=
	Element$TM[ b, a]
ReverseElement$TM[ a_?isIndividual, b_?isIndividual, c__?isIndividual] /; isPosRelation["ReverseElement"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ Element$TM[ #2, #1]]&, {{a, b}, {b, c}}]], 1, Hold]
NotReverseElement$TM[ a_?isIndividual] /; isNegRelation["NotReverseElement"] :=
	Not$TM[ Element$TM[ a]]
NotReverseElement$TM[ a_?isIndividual, b_?isIndividual] /; isNegRelation["NotReverseElement"] :=
	Not$TM[ Element$TM[ b, a]]
NotReverseElement$TM[ a_?isIndividual, b__?isIndividual, c_?isIndividual] /; isNegRelation["NotReverseElement"] :=
	Flatten[ Apply[ And$TM, MapThread[ Hold[ Not$TM[ Element$TM[ #2, #1]]]&, {{a, b}, {b, c}}]], 1, Hold]

DomainOperation$TM[ dom_, op_][ a_?isIndividual, b_?isIndividual] /; And[ getOperator[ op] === ReverseElement$TM, isPosRelation[ "ReverseElement"]] :=
	DomainOperation$TM[ dom, setOperator[ op, Element$TM]][ b, a]
DomainOperation$TM[ dom_, op_][ a_?isIndividual] :=
	Module[ {rel},
		Not$TM[ DomainOperation$TM[ dom, setOperator[ op, negateRelation[ rel]]][ a]] /; And[ (rel = getOperator[ op]) =!= $Failed, isNegRelation[ rel]]
	]
DomainOperation$TM[ dom_, op_][ a_?isIndividual, b_?isIndividual] :=
	Module[ {rel},
		Not$TM[ DomainOperation$TM[ dom, setOperator[ op, negateRelation[ rel]]][ a, b]] /; And[ (rel = getOperator[ op]) =!= $Failed, isNegRelation[ rel]]
	]
DomainOperation$TM[ dom_, op_][ a_?isIndividual, b__, c_?isIndividual] :=
	Module[ {rel, p},
		If[ p,
			Flatten[ Apply[ And$TM, MapThread[ Hold[ DomainOperation$TM[ dom, op][ #1, #2]]&, {{a, b}, {b, c}}]], 1, Hold],
			Flatten[ Apply[ And$TM, MapThread[ Hold[ Not$TM[ DomainOperation$TM[ dom, setOperator[ op, negateRelation[ rel]]][ #1, #2]]]&, {{a, b}, {b, c}}]], 1, Hold]
		] /; And[ (rel = getOperator[ op]) =!= $Failed, ((p = isPosRelation[ rel]) || isNegRelation[ rel]) && MatchQ[ {b}, {__?isIndividual}]]
	]

Annotated$TM[ op_, ann___][ a_?isIndividual, b_?isIndividual] /; And[ getOperator[ op] === ReverseElement$TM, isPosRelation[ "ReverseElement"]] :=
	Annotated$TM[ setOperator[ op, Element$TM], ann][ b, a]
Annotated$TM[ op_, ann___][ a_?isIndividual] :=
	Module[ {rel},
		Not$TM[ Annotated$TM[ setOperator[ op, negateRelation[ rel]], ann][ a]] /; And[ (rel = getOperator[ op]) =!= $Failed, isNegRelation[ rel]]
	]
Annotated$TM[ op_, ann___][ a_?isIndividual, b_?isIndividual] :=
	Module[ {rel},
		Not$TM[ Annotated$TM[ setOperator[ op, negateRelation[ rel]], ann][ a, b]] /; And[ (rel = getOperator[ op]) =!= $Failed, isNegRelation[ rel]]
	]
Annotated$TM[ op_, ann___][ a_?isIndividual, b__, c_?isIndividual] :=
	Module[ {rel, p},
		If[ p,
			Flatten[ Apply[ And$TM, MapThread[ Hold[ Annotated$TM[ op, ann][ #1, #2]]&, {{a, b}, {b, c}}]], 1, Hold],
			Flatten[ Apply[ And$TM, MapThread[ Hold[ Not$TM[ Annotated$TM[ setOperator[ op, negateRelation[ rel]], ann][ #1, #2]]]&, {{a, b}, {b, c}}]], 1, Hold]
		] /; And[ (rel = getOperator[ op]) =!= $Failed, ((p = isPosRelation[ rel]) || isNegRelation[ rel]) && MatchQ[ {b}, {__?isIndividual}]]
	]
	
OperatorChain$TM[ a1_?isIndividual, op_, a2_, rest___] :=
	Module[ {res},
		And$TM @@ res /;
			And[
				Mod[ Length[ Hold[ rest]], 2] === 0,
				(res = chainToConjunction[ {a1, op, a2, rest}, Hold[]]) =!= $Failed
			]
	]
	
chainToConjunction[ {a1_, op_, a2_, rest___}, Hold[ accumulator___]] :=
	If[ isIndividual[ a2],
		With[ {o = getOperator[ op]},
			If[ isPosRelation[ o] || isNegRelation[ o],
				chainToConjunction[ {a2, rest}, Hold[ accumulator, op[ a1, a2]]],
			(*else*)
				$Failed
			]
		],
	(*else*)
		$Failed
	]
chainToConjunction[ _List, acc_] := acc

DoubleLeftArrow$TM[ a_?isIndividual, b_?isIndividual] := Implies$TM[ b, a]
DoubleLeftArrow$TM[ a_?isIndividual, b___?isIndividual] := Fold[ Implies$TM[ #2, #1]&, a, {b}]

SetAttributes[ NotExists$TM, HoldRest];
NotExists$TM[ r_RNG$, cond_, form_] := Not$TM[ Exists$TM[ r, cond, form]]
	

(* ::Section:: *)
(* Arithmetic *)

tmaAtomQ[ x:VAR$[ _]] := isIndividual[ x]
tmaAtomQ[ x:FIX$[ _, _Integer]] := isIndividual[ x]
tmaAtomQ[ x:META$[ _, _Integer, _List]] := isIndividual[ x]
tmaAtomQ[ _DirectedInfinity] := True
tmaAtomQ[ a_] := AtomQ[ a]

mathematicalConstantQ[ True|False|Infinity|Indeterminate|I|Pi|E|Degree|EulerGamma|GoldenRatio|Catalan|Khinchin|Glaisher] := True
mathematicalConstantQ[ _] := False

(* "buiActiveArithmetic" extends "buiActive" such that the activation of "Subtract" and "Divide" can also
	be determined in one stroke. *)
buiActiveArithmetic["Subtract"] := buiActive["Plus"] && buiActive["Minus"]
buiActiveArithmetic["Divide"] := buiActive["Times"] && (buiActive["MultInverse"] || buiActive["Power"])
buiActiveArithmetic[s_String] := buiActive[s]

(* "buiActivePower" determines whether "Power" is activated for the given exponent. *)
buiActivePower[-1] := buiActive["MultInverse"] || buiActive["Power"]
buiActivePower[_] := buiActive["Power"]

(* 'filterIndividuals[ list, id, ann]' partitions 'list' into two sublists 'a' and 'b', where
	'a' contains the individuals in 'list' and 'b' the rest. Moreover, all elements in 'list'
	that match 'id' are removed, and if at least one element matches 'ann' both 'a' and 'b'
	are set to the empty list ('ann' plays the role of an "annihilator", such as 0 for 'Times').
	Returns the triple '{a, b, simp}', where 'simp' is a boolean value indicating whether
	'Length[ a] + Length[ b] < Length[ list]'. *)
filterIndividuals[ h_[ ___, ann_, ___], _, ann_] :=
	{h[ ann], h[], True}
filterIndividuals[ list_, id_, _] :=
	With[ {l = DeleteCases[ list, id]},
		With[ {p = Position[ HoldComplete /@ l, _?isIndividual, {1}, Heads -> False]},
			{Part[ l, First /@ p], Delete[ l, p], l =!= list}
		]
	]
	
(* 'applyFlexOperation' applies flexible-arity operations, such as Plus, Times, Subtract, And, Or, ... that would give wrong results if
	called on one non-individual argument. E.g. "Plus[ x...]" would give "x...", which is wrong. *)
(* This version is used for associative-commutative operators, like 'Plus', 'Times', etc. *)
applyFlexOperation[ args_Hold, orig_, op_, id_, ann_] :=
	Module[ {ind, seq, simp},
		{ind, seq, simp} = filterIndividuals[ args, id, ann];
		If[ ind === Hold[],
			Which[
				seq === Hold[],
				id,
			(*else*)
				simp,
				orig @@ seq,
			(*else*)
				True,
				$Failed
			],
		(*else*)
			With[ {r = op @@ ind},
				Which[
					Head[ r] === op,
					With[ {rh = Hold @@ r},
						If[ ind === rh,
							If[ simp,
								orig @@ Join[ ind, seq],
							(*else*)
								$Failed
							],
						(*else*)
							If[ seq === Hold[],
								r,
							(*else*)
								orig @@ Join[ rh, seq]
							]
						]
					],
				(*else*)
					seq === Hold[],
					r,
				(*else*)
					True,
					Switch[ r,
					(*case*)
						ann,
						ann,
					(*case*)
						id,
						orig @@ seq,
					(*case*)
						_,
						If[ Hold[ r] =!= ind || simp,
							orig @@ Prepend[ seq, r],
						(*else*)
							$Failed
						]
					]
				]
			]
		]
	]
(* This version is used for 'Subtract' and 'Divide', which are not associative and commutative. *)
applyFlexOperation[ init_, args_Hold, orig_, outer_, inner_, id_, ann_] :=
	Module[ {ind, seq, simp},
		{ind, seq, simp} = filterIndividuals[ args, id, ann];
		If[ ind === Hold[],
			If[ seq === Hold[],
				init,
			(*else*)
				If[ simp,
					orig @@ Prepend[ seq, init],
				(*else*)
					$Failed
				]
			],
		(*else*)
			If[ seq === Hold[],
				With[ {a = Hold @@ Prepend[ Replace[ ind, inner, {1}], init]},
					With[ {res = outer @@ a},
						If[ Head[ res] === outer && a === Hold @@ res,
							$Failed,
						(*else*)
							res
						]
					]
				],
			(*else*)
				orig @@ Prepend[ seq, orig @@ Prepend[ ind, init]]
			]
		]
	]

Equal$TM[ a_?isIndividual, a_] /; buiActive["Equal"] := True
Set$TM /: Equal$TM[ _Integer|_Rational|_Real|_Complex|_DirectedInfinity, _Set$TM] /; buiActive["Equal"] || buiActive["SetEqual"] := False
Tuple$TM /: Equal$TM[ _Integer|_Rational|_Real|_Complex|_DirectedInfinity, _Tuple$TM] /; buiActive["Equal"] || buiActive["TupleEqual"] := False
Equal$TM[ _?mathematicalConstantQ, _Integer|_Rational|_Real|_Complex|_DirectedInfinity] /; buiActive["Equal"] := False
Set$TM /: Equal$TM[ _?mathematicalConstantQ, _Set$TM] /; buiActive["Equal"] || buiActive["SetEqual"] := False
Tuple$TM /: Equal$TM[ _?mathematicalConstantQ, _Tuple$TM] /; buiActive["Equal"] || buiActive["TupleEqual"] := False
Equal$TM[ _Integer|_Rational|_Real|_Complex|_DirectedInfinity, (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___]] /; buiActive[StringDrop[SymbolName[h],-3]] && (buiActive["Equal"] || buiActive["SetEqual"]) := False
Equal$TM[ _?mathematicalConstantQ, (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___]] /; buiActive[StringDrop[SymbolName[h],-3]] && (buiActive["Equal"] || buiActive["SetEqual"]) := False
Equal$TM[ _Integer|_Rational|_Real|_Complex|_DirectedInfinity, h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive[StringDrop[SymbolName[h],-3]] && (buiActive["Equal"] || buiActive["SetEqual"]) := False
Equal$TM[ _?mathematicalConstantQ, h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive[StringDrop[SymbolName[h],-3]] && (buiActive["Equal"] || buiActive["SetEqual"]) := False
Set$TM /: Equal$TM[ _Set$TM, _Integer|_Rational|_Real|_Complex|_DirectedInfinity] /; buiActive["Equal"] || buiActive["SetEqual"] := False
Tuple$TM /: Equal$TM[ _Tuple$TM, _Integer|_Rational|_Real|_Complex|_DirectedInfinity] /; buiActive["Equal"] || buiActive["TupleEqual"] := False
Equal$TM[ _Integer|_Rational|_Real|_Complex|_DirectedInfinity, _?mathematicalConstantQ] /; buiActive["Equal"] := False
Set$TM /: Equal$TM[ _Set$TM, _?mathematicalConstantQ] /; buiActive["Equal"] || buiActive["SetEqual"] := False
Tuple$TM /: Equal$TM[ _Tuple$TM, _?mathematicalConstantQ] /; buiActive["Equal"] || buiActive["TupleEqual"] := False
Equal$TM[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___], _Integer|_Rational|_Real|_Complex|_DirectedInfinity] /; buiActive[StringDrop[SymbolName[h],-3]] && (buiActive["Equal"] || buiActive["SetEqual"]) := False
Equal$TM[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___], _?mathematicalConstantQ] /; buiActive[StringDrop[SymbolName[h],-3]] && (buiActive["Equal"] || buiActive["SetEqual"]) := False
Equal$TM[ h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM), _Integer|_Rational|_Real|_Complex|_DirectedInfinity] /; buiActive[StringDrop[SymbolName[h],-3]] && (buiActive["Equal"] || buiActive["SetEqual"]) := False
Equal$TM[ h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM), _?mathematicalConstantQ] /; buiActive[StringDrop[SymbolName[h],-3]] && (buiActive["Equal"] || buiActive["SetEqual"]) := False
Equal$TM[ a_?mathematicalConstantQ, b_?mathematicalConstantQ] /; buiActive["Equal"] := SameQ[ a, b]
Equal$TM[ a_?tmaAtomQ, b_?tmaAtomQ] /; buiActive["Equal"] := a == b

Plus$TM[ a___] /; buiActive["Plus"] :=
	With[ {res = applyFlexOperation[ Hold[ a], Plus$TM, Plus, 0, $Failed]},
		res /; res =!= $Failed
	]
Minus$TM[ a_?isIndividual] /; buiActive["Minus"] :=
	With[ {res = Minus[ a]},
		res /; !MatchQ[ res, Times[ _?Negative, __]]
	]
Subtract$TM[ a_?isIndividual, b___] /; buiActiveArithmetic["Subtract"] :=
	With[ {res = applyFlexOperation[ a, Hold[ b], Subtract$TM, Plus, x_ :> Times[ -1, x], 0, $Failed]},
		res /; res =!= $Failed
	]
Times$TM[ a___] /; buiActive["Times"] :=
	With[ {res = applyFlexOperation[ Hold[ a], Times$TM, Times, 1, 0]},
		res /; res =!= $Failed
	]
Divide$TM[ a_?isIndividual, b___] /; buiActiveArithmetic["Divide"] :=
	With[ {res = applyFlexOperation[ a, Hold[ b], Divide$TM, Times, x_ :> Power[ x, -1], 1, 0]},
		res /; res =!= $Failed
	]
Power$TM[ a_?isIndividual, b_?isIndividual] /; buiActivePower[ b] :=
	Module[ {res = Power[ a, b]},
		res /; (Head[ res] =!= Power || Hold[ a, b] =!= Apply[ Hold, res])
	]
Radical$TM[ a_?isIndividual, b_?isIndividual] /; buiActive["Radical"] :=
	Module[ {res = Power[ a, Power[ b, -1]]},
		res /; (Head[ res] =!= Power || Hold[ a, Power[ b, -1]] =!= Apply[ Hold, res])
	]
Factorial$TM[ a_?isIndividual] /; buiActive["Factorial"] :=
	Module[ {res = a!},
		res /; Head[ res] =!= Factorial
	]
	
Less$TM[ a__?isIndividual] /; buiActive["Less"] :=
	Module[ {res = Less[ a]},
		res /; (Head[ res] =!= Less || Hold[ a] =!= Hold @@ res)
	]
Less$TM[ a_?isIndividual, a_] /; buiActive["Less"] := False
LessEqual$TM[ a__?isIndividual] /; buiActive["LessEqual"] :=
	Module[ {res = LessEqual[ a]},
		res /; (Head[ res] =!= LessEqual || Hold[ a] =!= Hold @@ res)
	]
LessEqual$TM[ a_?isIndividual, a_] /; buiActive["Less"] := True
Greater$TM[ a__?isIndividual] /; buiActive["Greater"] :=
	Module[ {res = Greater[ a]},
		res /; (Head[ res] =!= Greater || Hold[ a] =!= Hold @@ res)
	]
Greater$TM[ a_?isIndividual, a_] /; buiActive["Less"] := False
GreaterEqual$TM[ a__?isIndividual] /; buiActive["GreaterEqual"] :=
	Module[ {res = GreaterEqual[ a]},
		res /; (Head[ res] =!= GreaterEqual || Hold[ a] =!= Hold @@ res)
	]
GreaterEqual$TM[ a_?isIndividual, a_] /; buiActive["Less"] := True

BracketingBar$TM[ a:(_Integer|_Rational|_Real|_Complex|_DirectedInfinity)] /; buiActive["AbsValue"] := Abs[ a]
BracketingBar$TM[ a:(Pi|E|Degree|EulerGamma|GoldenRatio|Catalan|Khinchin|Glaisher)] /; buiActive["AbsValue"] := a

(* "isValidArgNum", called on a symbol 's' and an integer 'n' gives True iff 's' is a function symbol that can
	be called with 'n' numbers and returns a number (that's why relations are not considered as functions),
	AND which, in addition to that, has an analogue in Mathematica with the same name withot "$TM"
	(that's why "Radical$TM" is not considered as an arithmetical operation and therefore has to be treated separately). *)
isValidArgNum[ Plus$TM|Times$TM, _Integer?NonNegative] := True
isValidArgNum[ Subtract$TM|Divide$TM, 2] := True
isValidArgNum[ Minus$TM, 1] := True
isValidArgNum[ _, _] := False

(* In the domain operations implemented below, we do not need to worry about sequence arguments:
	the operations are only applicable if all arguments *AND* the result are known to be in the
	respective domains, and this is certainly not the case with sequences. *)
	
(* We have to treat the case "Power[a, b]" differently, since 'b' does not have to be in the domain. Same for "Radical". *)
DomainOperation$TM[ dom:((h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ _, _, _, _]), Power$TM][ a_, b_] /; buiActive[StringDrop[SymbolName[h], -3]] && buiActivePower[ b] && isInInterval[ a, dom] :=
	Module[ {out},
		out /; (out = Power[ a, b]; isInInterval[ out, dom])
	]
DomainOperation$TM[ dom:((h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ _, _, _, _]), Radical$TM][ a_, b_] /; buiActive[StringDrop[SymbolName[h], -3]] && buiActive[ "Radical"] && isInInterval[ a, dom] :=
	Module[ {out},
		out /; (out = Power[ a, Power[ b, -1]]; isInInterval[ out, dom])
	]
DomainOperation$TM[ dom:((h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ _, _, _, _]), op_Symbol][ a___] /;
		buiActive[ StringDrop[ SymbolName[ h], -3]] && isValidArgNum[ op, Length[ {a}]] && And @@ Map[ isInInterval[ #, dom]&, Hold[ a]] :=
	Module[ {out, opShortName, opShort},
		out /; And[
					opShortName = StringDrop[ SymbolName[ op], -3]; buiActiveArithmetic[ opShortName],
					opShort = ToExpression[ opShortName]; out = opShort[ a]; isInInterval[ out, dom]
				  ]
	]

DomainOperation$TM[\[DoubleStruckCapitalC]$TM, Power$TM][ a_, b_] /; buiActive["\[DoubleStruckCapitalC]"] && buiActivePower[ b] && isComplex[ a] :=
	Module[ {out},
		out /; (out = Power[ a, b]; isComplex[ out])
	]
DomainOperation$TM[\[DoubleStruckCapitalC]$TM, Radical$TM][ a_, b_] /; buiActive["\[DoubleStruckCapitalC]"] && buiActive["Radical"] && isComplex[ a] :=
	Module[ {out},
		out /; (out = Power[ a, Power[ b, -1]]; isComplex[ out])
	]
DomainOperation$TM[\[DoubleStruckCapitalC]$TM, op_Symbol][ a___] /; buiActive["\[DoubleStruckCapitalC]"] && isValidArgNum[ op, Length[ {a}]] && And @@ Map[ isComplex, Hold[ a]] :=
	Module[ {out, opShortName, opShort},
		out /; And[
					opShortName = StringDrop[ SymbolName[ op], -3]; buiActiveArithmetic[ opShortName],
					opShort = ToExpression[ opShortName]; out = opShort[ a]; isComplex[ out]
				  ]
	]
	
DomainOperation$TM[\[DoubleStruckCapitalC]P$TM, Radical$TM][ a_Tuple$TM, b:Tuple$TM[ _?Positive, _]] /;
		buiActive["\[DoubleStruckCapitalC]P"] && buiActive["Radical"] && isComplexP[ a] && isComplexP[ b] :=
	Module[ {out},
		out /; (out = polarPower[ a, polarPower[ b, -1]]; isComplexP[ out])
	]
DomainOperation$TM[\[DoubleStruckCapitalC]P$TM, Radical$TM][ a:Tuple$TM[ r_, phi_], b_] /; buiActive["\[DoubleStruckCapitalC]P"] && buiActive["Radical"] && isComplexP[ a] :=
	Module[ {out},
		out /; (out = polarPower[ a, Power[ b, -1]]; isComplexP[ out])
	]
(* We implement some operations on polar-complexes separately because of efficiency. *)
DomainOperation$TM[\[DoubleStruckCapitalC]P$TM, Minus$TM][ a:Tuple$TM[ r_, phi_]] /;
		buiActive["\[DoubleStruckCapitalC]P"] && buiActive["Minus"] && isComplexP[ a] :=
	Tuple$TM[ r, If[ phi >= Pi, phi - Pi, phi + Pi]]
DomainOperation$TM[\[DoubleStruckCapitalC]P$TM, Times$TM][ a:Tuple$TM[ ra_, phia_], b:Tuple$TM[ rb_, phib_]] /;
		buiActive["\[DoubleStruckCapitalC]P"] && buiActive["Times"] && isComplexP[ a] && isComplexP[ b] :=
	Tuple$TM[ ra * rb, phia + phib]
DomainOperation$TM[\[DoubleStruckCapitalC]P$TM, Divide$TM][ a:Tuple$TM[ ra_, phia_], b:Tuple$TM[ rb_?Positive, phib_]] /;
		buiActive["\[DoubleStruckCapitalC]P"] && buiActiveArithmetic["Divide"] && isComplexP[ a] && isComplexP[ b] :=
	Tuple$TM[ ra / rb, phia - phib]
DomainOperation$TM[\[DoubleStruckCapitalC]P$TM, Power$TM][ a_Tuple$TM, b_Tuple$TM] /;
		buiActive["\[DoubleStruckCapitalC]P"] && buiActive["Power"] && isComplexP[ a] && isComplexP[ b] :=
	Module[ {out},
		out /; (out = polarPower[ a, b]; isComplexP[ out])
	]
DomainOperation$TM[\[DoubleStruckCapitalC]P$TM, Power$TM][ a:Tuple$TM[ r_, phi_], b_] /;
		buiActive["\[DoubleStruckCapitalC]P"] && buiActivePower[ b] && isComplexP[ a] :=
	Module[ {out},
		out /; (out = Tuple$TM[ Power[ r, b], phi * b]; isComplexP[ out])
	]
DomainOperation$TM[\[DoubleStruckCapitalC]P$TM, op_Symbol][ a___Tuple$TM] /;
		buiActive["\[DoubleStruckCapitalC]P"] && isValidArgNum[ op, Length[{a}]] && And @@ Map[ isComplexP, Hold[ a]] :=
	Module[ {outCartesian, out, opShortName, opShort, aCartesian},
		out /; And[
					opShortName = StringDrop[ SymbolName[ op], -3]; buiActiveArithmetic[ opShortName],
					opShort = ToExpression[ opShortName];
					aCartesian = Map[ (First[#] * (Cos[Last[#]] + I * Sin[Last[#]]))&, Hold[ a]];
					outCartesian = Apply[ opShort, aCartesian];
					out = Tuple$TM[ Abs[ outCartesian], Arg[ outCartesian]];
					isComplexP[ out]
				  ]
	]

polarPower[ Tuple$TM[ 0, _], Tuple$TM[0, _]] := Indeterminate
polarPower[ _Tuple$TM, Tuple$TM[0, _]] := Tuple$TM[ 1, 0]
polarPower[ Tuple$TM[ ra_, phia_], Tuple$TM[ rb_, phib_]] :=
	Module[ {breal, bim, outr},
		breal = rb * Cos[ phib];
		bim = rb * Sin[ phib];
		Which[
			Positive[ ra],
			outr = Power[ ra, breal] * Exp[ -phia * bim];
			If[ bim == 0,
				Tuple$TM[outr, breal * phia],
				Tuple$TM[outr, breal * phia + bim * Log[ ra]]
			],
			Positive[ breal] && bim == 0,
			Tuple$TM[0, 0],
			True,
			Indeterminate
		]
	]
	
DomainOperation$TM[ IntegerQuotientRing$TM[ m_?isModulus], Divide$TM][ a_?isInteger, b_?isInteger] /; buiActive["IntegerQuotientRing"] && buiActive["Radical"] && NonNegative[ a] && a < m && Positive[ b] && b < m:=
	Module[ {gcd, qr},
		Mod[ First[ qr] * gcd[[2, 1]], m] /; (gcd = ExtendedGCD[ b, m]; qr = QuotientRemainder[ a, First[ gcd]]; Last[ qr] === 0)
	]
(* We use "PowerMod" rather than "Mod[Power[..]]", because it is much more efficient
	(according to Mathematica's documentation center). *)
DomainOperation$TM[ IntegerQuotientRing$TM[ m_?isModulus], Radical$TM][ a_?isInteger, b_] /; buiActive["IntegerQuotientRing"] && buiActive["Radical"] && NonNegative[ a] && a < m :=
	Module[ {out},
		out /; Quiet[ Check[ out = PowerMod[ a, Power[ b, -1], m]; isInteger[ out], False]]
	]
DomainOperation$TM[ IntegerQuotientRing$TM[ m_?isModulus], Power$TM][ a_?isInteger, b_] /; buiActive["IntegerQuotientRing"] && buiActivePower[ b] && NonNegative[ a] && a < m :=
	Module[ {out},
		out /; Quiet[ Check[ out = PowerMod[ a, b, m]; isInteger[ out], False]]
	]
DomainOperation$TM[ IntegerQuotientRing$TM[ m_?isModulus], op_Symbol][ a___?isInteger] /;
		buiActive["IntegerQuotientRing"] && isValidArgNum[ op, Length[ {a}]] && And @@ Map[ (NonNegative[#] && # < m)&, Hold[ a]] :=
	Module[ {out, opShortName, opShort},
		Mod[ out, m] /; And[
						opShortName = StringDrop[ SymbolName[ op], -3]; buiActiveArithmetic[ opShortName],
						opShort = ToExpression[ opShortName]; out = opShort[ a]; isInteger[ out]
					]
	]
	
DomainOperation$TM[ IntegerQuotientRingPM$TM[ m_?isModulus], Divide$TM][ a_?isInteger, b_?isInteger] /; buiActive["IntegerQuotientRingPM"] && buiActive["Radical"] && lowerPM[ m] <= a <= upperPM[ m] && lowerPM[ m] <= b <= upperPM[ m] :=
	Module[ {gcd, qr},
		representPM[ First[ qr] * gcd[[2, 1]], m] /; (gcd = ExtendedGCD[ b, m]; qr = QuotientRemainder[ a, First[ gcd]]; Last[ qr] === 0)
	]
(* We use "PowerMod" rather than "Mod[Power[..]]", because it is much more efficient
	(according to Mathematica's documentation center). *)
DomainOperation$TM[ IntegerQuotientRingPM$TM[ m_?isModulus], Radical$TM][ a_?isInteger, b_] /; buiActive["IntegerQuotientRingPM"] && buiActive["Radical"] && lowerPM[ m] <= a <= upperPM[ m] :=
	Module[ {out},
		representPM[ out, m] /; Quiet[ Check[ out = PowerMod[ a, Power[ b, -1], m]; isInteger[ out], False]]
	]
DomainOperation$TM[ IntegerQuotientRingPM$TM[ m_?isModulus], Power$TM][ a_?isInteger, b_] /; buiActive["IntegerQuotientRingPM"] && buiActivePower[ b] && lowerPM[ m] <= a <= upperPM[ m] :=
	Module[ {out},
		representPM[ out, m] /; Quiet[ Check[ out = PowerMod[ a, b, m]; isInteger[ out], False]]
	]
DomainOperation$TM[ IntegerQuotientRingPM$TM[ m_?isModulus], op_Symbol][ a___?isInteger] /; buiActive["IntegerQuotientRingPM"] && isValidArgNum[ op, Length[{a}]] :=
	With[ {l = lowerPM[ m], u = upperPM[ m]},
	Module[ {out, opShortName, opShort},
		representPM[ out, m] /; And[
						Apply[ And, Map[ (l <= # <= u)&, Hold[ a]]],
						opShortName = StringDrop[ SymbolName[ op], -3]; buiActiveArithmetic[ opShortName],
						opShort = ToExpression[ opShortName]; out = opShort[ a]; isInteger[ out]
					]
	]
	]
representPM[ a_, m_] := With[ {b = Mod[ a, m]}, If[ b > upperPM[ m], b - m, b]]
lowerPM[ m_] := Ceiling[ (1 - m) / 2];
upperPM[ m_] := Ceiling[ (m - 1) / 2];

(* "isBinaryRelation" gives True for all binary relations that take two numbers as input, AND which, in addition
	to that, have an analogue in Mathematica with the same name withot "$TM". *)
isBinaryRelation[ Equal$TM|Less$TM|LessEqual$TM|Greater$TM|GreaterEqual$TM] := True
isBinaryRelation[ _] := False

DomainOperation$TM[ dom:((h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ _, _, _, _]), rel_Symbol?isBinaryRelation][ a_, b_] /;
		buiActive[ StringDrop[ SymbolName[ h], -3]] && isInInterval[ a, dom] && isInInterval[ b, dom] :=
	Module[ {relShortName, relShort},
		(relShort = ToExpression[ relShortName];
		relShort[ a, b]) /; (relShortName = StringDrop[ SymbolName[ rel], -3]; buiActive[ relShortName])
	]

(* The only relation that makes sense for complex numbers is equality, since no meaningful order relations
	are defined (give error by Mathematica). *)
DomainOperation$TM[ \[DoubleStruckCapitalC]$TM, Equal$TM][ a_, b_] /;
		buiActive["\[DoubleStruckCapitalC]"] && buiActive["Equal"] && isComplex[ a] && isComplex[ b] :=
	a == b
DomainOperation$TM[ \[DoubleStruckCapitalC]P$TM, Equal$TM][ a:Tuple$TM[ ra_, phia_], b:Tuple$TM[ rb_, phib_]] /;
		buiActive["\[DoubleStruckCapitalC]P"] && buiActive["Equal"] && isComplexP[ a] && isComplexP[ b] :=
	ra == rb && (ra == 0 || EvenQ[ (phia - phib) / Pi])

(* The only relation that makes sense for quotient rings is equality. *)
DomainOperation$TM[ IntegerQuotientRing$TM[ m_?isModulus], Equal$TM][ a_, b_] /;
		buiActive["IntegerQuotientRing"] && buiActive["Equal"] && NonNegative[ a] && a < m && NonNegative[ b] && b < m :=
	a == b
DomainOperation$TM[ IntegerQuotientRingPM$TM[ m_?isModulus], Equal$TM][ a_, b_] /;
		buiActive["IntegerQuotientRingPM"] && buiActive["Equal"] && lowerPM[ m] <= a <= upperPM[ m] && lowerPM[ m] <= b <= upperPM[ m] :=
	a == b



(* ::Section:: *)
(* Ring Constants/Operations *)

DomainOperation$TM[ dom:((h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ _, _, _, _]), 0] /;
		buiActive[ StringDrop[ SymbolName[ h], -3]] && isInInterval[ 0, dom] :=
	0
DomainOperation$TM[ \[DoubleStruckCapitalC]$TM, 0] /; buiActive["\[DoubleStruckCapitalC]"] :=
	0
DomainOperation$TM[ \[DoubleStruckCapitalC]P$TM, 0] /; buiActive["\[DoubleStruckCapitalC]P"] :=
	Tuple$TM[0, 0]
DomainOperation$TM[ (h:(IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ _?isModulus], 0] /;
		buiActive[ StringDrop[ SymbolName[ h], -3]] :=
	0

DomainOperation$TM[ dom:((h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ _, _, _, _]), 1] /;
		buiActive[ StringDrop[ SymbolName[ h], -3]] && isInInterval[ 1, dom] :=
	1
DomainOperation$TM[ \[DoubleStruckCapitalC]$TM, 1] /; buiActive["\[DoubleStruckCapitalC]"] :=
	1
DomainOperation$TM[ \[DoubleStruckCapitalC]P$TM, 1] /; buiActive["\[DoubleStruckCapitalC]P"] :=
	Tuple$TM[1, 0]
DomainOperation$TM[ (h:(IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ m_?isModulus], 1] /;
		buiActive[ StringDrop[ SymbolName[ h], -3]] && m > 1 :=
	1

DomainOperation$TM[ dom:((h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ _, _, _, _]), Element$TM][ a_] /;
		buiActive["IsElement"] && buiActive[ StringDrop[ SymbolName[ h], -3]] :=
	isInInterval[ a, dom]
DomainOperation$TM[ \[DoubleStruckCapitalC]$TM, Element$TM][ a_] /; buiActive["IsElement"] && buiActive["\[DoubleStruckCapitalC]"] :=
	isComplex$TM[ a]
DomainOperation$TM[ \[DoubleStruckCapitalC]P$TM, Element$TM][ a_] /; buiActive["IsElement"] && buiActive["\[DoubleStruckCapitalC]P"] :=
	isComplexP$TM[ a]
DomainOperation$TM[ IntegerQuotientRing$TM[ m_?isModulus], Element$TM][ a_] /; buiActive["IsElement"] && buiActive["IntegerQuotientRing"] :=
	isInteger$TM[ a] && 0 <= a && a <= m-1
DomainOperation$TM[ IntegerQuotientRingPM$TM[ m_?isModulus], Element$TM][ a_] /; buiActive["IsElement"] && buiActive["IntegerQuotientRingPM"] :=
	isInteger$TM[ a] && lowerPM[ m] <= a && a <= upperPM[ m]



(* ::Section:: *)
(* Logic *)


SetAttributes[ {And$TM, Or$TM, Nand$TM, Nor$TM}, HoldAll]
Not$TM[ a_] /; buiActive["Not"] := Not[ a]
And$TM[ pre___, a_, mid___, a_, post___] /; buiActive["And"] := And$TM[ pre, a, mid, post]
And$TM[ a___] /; buiActive["And"] :=
	With[ {res = applyFlexOperation[ Hold[ a], And$TM, And, True, False]},
		res /; res =!= $Failed
	]
Or$TM[ pre___, a_, mid___, a_, post___] /; buiActive["Or"] := Or$TM[ pre, a, mid, post]
Or$TM[ a___] /; buiActive["Or"] :=
	With[ {res = applyFlexOperation[ Hold[ a], Or$TM, Or, False, True]},
		res /; res =!= $Failed
	]
Implies$TM[ a_?isIndividual, b_?isIndividual] /; buiActive["Implies"] := Implies[ a, b]
Iff$TM[ _?isIndividual] /; buiActive["Iff"] := True
Iff$TM[ PatternSequence[___, True, ___, False, ___]|PatternSequence[___, False, ___, True, ___]] /; buiActive["Iff"] := False
Iff$TM[ a__?isIndividual] /; buiActive["Iff"] :=
	Module[ {res},
		ReleaseHold[ Iff$TM @@ res] /; (res = DeleteDuplicates[ List @@ (Hold /@ Hold[ a])]) =!= List @@ (Hold /@ Hold[ a])
	]
Nand$TM[ a___] /; buiActive["Nand"] := Not$TM[ And$TM[ a]]
Nor$TM[ a___] /; buiActive["Nor"] := Not$TM[ Or$TM[ a]]
Xor$TM[] /; buiActive["Xor"] := False
Xor$TM[ a_?isIndividual] /; buiActive["Xor"] := a
Xor$TM[ pre___, False, post___] /; buiActive["Xor"] := Xor$TM[ pre, post]
Xor$TM[ pre___, a_, mid___, a_, post___] /; buiActive["Xor"] := Xor$TM[ pre, mid, post]
Xor$TM[ pre___, True, post___] /; buiActive["Xor"] := Not$TM[ Xor$TM[ pre, post]]
Xor$TM[ a__?isIndividual] /; buiActive["Xor"] :=
	Module[ {l = Hold[ a], i, n, out = Hold[]},
		n = Length[ l];
		For[ i = 1, i <= n, i += 2,
			Scan[ PrependTo[ out, Join[ #, Map[ Not$TM, Complement[ l, #]]]]&, Subsets[ l, {i}]]
		];
		Or$TM @@ ReplacePart[ out, {_, 0} -> And$TM]
	]
Xnor$TM[] /; buiActive["Xnor"] := True
Xnor$TM[ a_] /; buiActive["Xnor"] := Not$TM[ a]
Xnor$TM[ pre___, False, post___] /; buiActive["Xnor"] := Xnor$TM[ pre, post]
Xnor$TM[ pre___, a_, mid___, a_, post___] /; buiActive["Xnor"] := Xnor$TM[ pre, mid, post]
Xnor$TM[ pre___, True, post___] /; buiActive["Xnor"] := Not$TM[ Xnor$TM[ pre, post]]
Xnor$TM[ a__?isIndividual] /; buiActive["Xnor"] :=
	Module[ {l = Hold[ a], i, n, out = Hold[]},
		n = Length[ l];
		For[ i = 0, i <= n, i += 2,
			Scan[ PrependTo[ out, Join[ #, Map[ Not$TM, Complement[ l, #]]]]&, Subsets[ l, {i}]]
		];
		Or$TM @@ ReplacePart[ out, {_, 0} -> And$TM]
	]
Componentwise$TM[ P_, args___?isIndividual] /; buiActive["Componentwise"] := And @@ (P /@ Hold[ args])

(* We replace the free variables one after the other, because some might depend on others, and a
	single "substitueFree" doesn't work properly then. This could also be good for global abbreviations ... *)
SetAttributes[ Abbrev$TM, HoldAll]
Abbrev$TM[ RNG$[ f_ABBRVRNG$, r__ABBRVRNG$], expr_] /; buiActive["Let"] :=
	Abbrev$TM[ RNG$[ f], Abbrev$TM[ RNG$[ r], expr]]
Abbrev$TM[ RNG$[ ABBRVRNG$[ _, r_, _[ pos___]]], expr_] /; buiActive["Let"] && isIndividual[ HoldComplete[ expr]] :=
	ReleaseHold[ ReplacePart[ Hold[ expr], List@@@{pos} -> r]]	(* The position specification might be a tuple. *)
(* The following definition of "Abbrev$TM" should not be needed any longer, but still we keep it (just in case). *)
Abbrev$TM[ RNG$[ ABBRVRNG$[ l_, r_]], expr_] /; buiActive["Let"] && isIndividual[ HoldComplete[ r]] && isIndividual[ HoldComplete[ expr]] :=
	ReleaseHold[ substituteFree[ Hold[ expr], {l -> r}, "checkTypes" -> False, "postprocessing" -> Identity]]

(* Any valid iterator only iterates over individuals, hence we do not need to check sequence-types in any of the calls of 'substituteFree' below. *)
rangeToIterator[ SETRNG$[ x_, A:Set$TM[ ___?isIndividual]]] := { x, List @@ A}
rangeToIterator[ 
  STEPRNG$[ x_, l_Integer, h_Integer, s_Integer]] := {x, l, h, s}
rangeToIterator[ _] := $Failed
rangeToIterator[ args___] := unexpected[ rangeToIterator, {args}]

(* ::Subsubsection:: *)
(* splitAnd *)


(*
	splitAnd[ expr_, v_List] splits a conjunction expr into 1. a conjunction of subexpr with free variables v and 2. the rest 
	splitAnd[ expr_, v_List, False] splits a conjunction expr into 1. a conjunction of subexpr containing the free variables in v and 2. the rest 
*)

splitAnd[ expr:Hold[(h:And$TM|And)[ __]], v_List, sub_:True] :=
	Module[ {depSingle = Hold[], depMulti = Hold[], p, l, e = simplifiedAnd[ expr], fi, i},
		Switch[ e,
			Hold[ (And$TM|And)[ __]],
			e = Map[ Hold, FlattenAt[ e, {1}]];
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
			depSingle = Switch[ Length[ depSingle],
				0,
				Hold[ True],
				1,
				First[ depSingle],
				_,
				Replace[ Flatten[ depSingle, 1], Hold[ a__] :> Hold[ h[ a]]]
			];
			depMulti = Switch[ Length[ depMulti],
				0,
				Hold[ True],
				1,
				First[ depMulti],
				_,
				Replace[ Flatten[ depMulti, 1], Hold[ a__] :> Hold[ h[ a]]]
			];
			{depSingle, depMulti},
			
			Hold[ _],
			fi = freeVariables[ e];
			If[ (sub && fi === v) || (!sub && Intersection[ v, fi] =!= {}), 
				{e, True},
				{True, e}
			],
			
			_,
			{$Failed, $Failed}
		]
	]
splitAnd[ expr_Hold, v_List, sub_:True] :=
    Module[ {fi = freeVariables[ expr]},
        If[ (sub && fi === v) || (!sub && Intersection[ v, fi] =!= {}),
            { expr, Hold[ True]},
            { Hold[ True], expr}
        ]
    ]
splitAnd[ expr:(h:And$TM|And)[ __], v_List, sub_:True] :=
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
		{makeConjunction[ depSingle, h], makeConjunction[ depMulti, h]}
	]
splitAnd[ expr_, v_List, sub_:True] :=
    Module[ {fi = freeVariables[ expr]},
        If[ (sub && fi === v) || (!sub && Intersection[ v, fi] =!= {}),
            {expr, True},
            {True, expr}
        ]
    ]
splitAnd[ args___] := unexpected[ splitAnd, {args}]

splitQuantifier[ h_, RNG$[ r : _SETRNG$|_STEPRNG$, s__], cond_, form_] :=
 	Module[ {splitC},
 		(* The condition MUST be kept unevaluated! *)
 		splitC = splitAnd[ Hold[ cond], {Hold[ r][[1, 1]]}];
 		With[ {rc = First[ splitC], sc = Last[ splitC]},
 			With[ {tmp = Delete[ Hold[ h[ RNG$[ s], sc, form]], {1, 2, 0}]},
	 			h @@ Flatten[ Hold[ RNG$[ r], rc, tmp], 1, Hold]
 			]
   		]
	]


ClearAll[ Forall$TM, Exists$TM, SequenceOf$TM, SumOf$TM, ProductOf$TM,
	SetOf$TM, TupleOf$TM, MaximumOf$TM, MinimumOf$TM, UnionOf$TM, IntersectionOf$TM, Such$TM, SuchUnique$TM,
	ArgMin$TM, ArgMax$TM, TheArgMin$TM, TheArgMax$TM]
Scan[ SetAttributes[ #, HoldRest] &, {Forall$TM, Exists$TM, 
  SequenceOf$TM, SumOf$TM, ProductOf$TM, SetOf$TM, TupleOf$TM, MaximumOf$TM, MinimumOf$TM,
  UnionOf$TM, IntersectionOf$TM, Such$TM, SuchUnique$TM, ArgMin$TM, ArgMax$TM, TheArgMin$TM, TheArgMax$TM}]
Scan[ SetAttributes[ #, HoldFirst] &, {SETRNG$, STEPRNG$}]

Forall$TM[ rng:RNG$[ _SETRNG$|_STEPRNG$, __], cond_, form_] /; buiActive["Forall"] :=
	splitQuantifier[ Forall$TM, rng, cond, form]

Forall$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["Forall"] :=
 	Module[ {iter},
    	forallIteration[ iter, cond, form] /; (iter = rangeToIterator[ r]) =!= $Failed
  	]

(* We introduce local variables for the iteration so that we can \
substitute only for free occurrences.
   Technically, Mathematica coulf iterate the VAR$[..] directly, but \
it would substitute ALL occurrences then *)
SetAttributes[forallIteration, HoldRest]
forallIteration[ {x_, iter__}, cond_, form_] :=
 Module[ {uneval = {}, ci, sub},
	Catch[
		Do[
			If[ Hold[ cond] === Hold[ True],
				ci = True,
				(*else*)
            	ci = ReleaseHold[ substituteFree[ Hold[ cond], {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]]
			];
			If[ ci,
				sub = ReleaseHold[ substituteFree[ Hold[ form], {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]];
				If[ sub,
					Continue[],
					(*else*)
					Throw[ False],
					(*default*)
					AppendTo[ uneval, sub]
				],
				(*else*)
				Continue[],
				(*default*)
				AppendTo[ uneval, Implies$TM[ ci, ReleaseHold[ substituteFree[ Hold[ form], {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]]]]
			],
			{ i, iter}
		]; (*end do*)
		makeConjunction[ uneval, And$TM]
	] (*end catch*)
 ]
    
Exists$TM[ rng:RNG$[ _SETRNG$|_STEPRNG$, __], cond_, form_] /; buiActive["Exists"] :=
 	splitQuantifier[ Exists$TM, rng, cond, form]

Exists$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["Exists"] :=
 	Module[ {iter},
    	existsIteration[ iter, cond, form] /; (iter = rangeToIterator[ r]) =!= $Failed
  	]

SetAttributes[ existsIteration, HoldRest]
existsIteration[ {x_, iter__}, cond_, form_] :=
 Module[ {uneval = {}, ci, sub},
	Catch[
		Do[
			If[ Hold[ cond] === Hold[ True],
				ci = True,
				ci = ReleaseHold[ substituteFree[ Hold[ cond], {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]]
			];
			If[ ci,
				sub = ReleaseHold[ substituteFree[ Hold[ form], {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]];
				If[ sub,
					Throw[ True],
					(*else*)
					Continue[],
					(*default*)
					AppendTo[ uneval, sub]
				],
				(*else*)
				Continue[],
				(*default*)
				AppendTo[ uneval, And$TM[ ci, ReleaseHold[ substituteFree[ Hold[ form], {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]]]]
			],
			{i, iter}
		]; (*end do*)
		makeDisjunction[ uneval, Or$TM]
	] (*end catch*)
 ]

(* Instead of nesting SequenceOf expressions and then concatenating the sequences, we construct a multi-iterator from the given ranges *)
SequenceOf$TM[ RNG$[ r__STEPRNG$], cond_, form_] :=
 	Module[ {s},
		Apply[ Sequence, s] /; (s = sequenceOfIteration[ Map[ rangeToIterator, {r}], cond, form]) =!= $Failed
	]

(* The multi-iterator is used in a Do-loop. Local variables have to \
be introduced to be substituted during the iteration *)   	
SetAttributes[ sequenceOfIteration, HoldRest]
sequenceOfIteration[ iter : {__List}, cond_, form_] :=  
 Module[ {seq = {}, ci, comp, 
		  tmpVar = Table[ Unique[], {Length[ iter]}], 
		  iVar = Map[ First, iter]},
	Catch[
		With[ {locIter = Apply[ Sequence, MapThread[ ReplacePart[ #1, 1 -> #2] &, {iter, tmpVar}]], 
     		   locSubs = Thread[ Rule[ iVar, tmpVar]]},
			Do[ If[ Hold[ cond] === Hold[ True], (* cond must be kept unevaluated! *)
					ci = True,
					ci = ReleaseHold[ substituteFree[ Hold[ cond], locSubs, "checkTypes" -> False, "postprocessing" -> Identity]]
				];
				If[ ci,
					comp = ReleaseHold[ substituteFree[ Hold[ form], locSubs, "checkTypes" -> False, "postprocessing" -> Identity]];
					AppendTo[ seq, comp],
					(*else*)
					Continue[],
					(*default*)
					Throw[ $Failed]
				],
				locIter
			] (*end do*)
		]; (*end with*)
		seq
	] (*end catch*)
 ]
sequenceOfIteration[ _List, _, _] := $Failed
sequenceOfIteration[ $Failed, _, _] := $Failed
sequenceOfIteration[ args___] := 
 unexpected[ sequenceOfIteration, {args}]

SetOf$TM[ RNG$[ r__], cond_, form_] :=
	Module[ {s},
		Set$TM @@ Union[ s] /; (s = sequenceOfIteration[ Map[ rangeToIterator, {r}], cond, form]) =!= $Failed
	]

TupleOf$TM[ RNG$[ r__], cond_, form_] :=
	Module[ {s},
		Tuple$TM @@ s /; (s = sequenceOfIteration[ Map[ rangeToIterator, {r}], cond, form]) =!= $Failed
	]
  	
(* We have to split several summations into individual ones,
	because the various ranges may depend on each other, and this does not work in connection with
	"sequenceOfIteration". Same with "ProductOf", "MaximumOf", etc. *)
SumOf$TM[ rng:RNG$[ _SETRNG$ | _STEPRNG$, __], cond_, form_] /; buiActive["SumOf"] :=
	splitQuantifier[ SumOf$TM, rng, cond, form]
SumOf$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["SumOf"] :=
	Module[ {v},
		v /; (v = valueIteration[ rangeToIterator[ r], cond, form, Plus$TM, 0]) =!= $Failed
	]
(h:DomainOperation$TM[ _, SumOf$TM])[ rng:RNG$[ _SETRNG$ | _STEPRNG$, __], cond_, form_] /; buiActive["SumOf"] :=
 	splitQuantifier[ h, rng, cond, form]
DomainOperation$TM[ dom_, SumOf$TM][ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["SumOf"] :=
	Module[ {v},
		v /; (v = valueIteration[ rangeToIterator[ r], cond, form, DomainOperation$TM[ dom, Plus$TM], DomainOperation$TM[ dom, 0]]) =!= $Failed
	]
	
ProductOf$TM[ rng:RNG$[ _SETRNG$ | _STEPRNG$, __], cond_, form_] /; buiActive["ProductOf"] :=
 	splitQuantifier[ ProductOf$TM, rng, cond, form]
ProductOf$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["ProductOf"] :=
	Module[ {v},
		v /; (v = valueIteration[ rangeToIterator[ r], cond, form, Times$TM, 1]) =!= $Failed
	]
(h:DomainOperation$TM[ _, ProductOf$TM])[ rng:RNG$[ _SETRNG$ | _STEPRNG$, __], cond_, form_] /; buiActive["ProductOf"] :=
 	splitQuantifier[ h, rng, cond, form]
DomainOperation$TM[ dom_, ProductOf$TM][ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["ProductOf"] :=
	Module[ {v},
		v /; (v = valueIteration[ rangeToIterator[ r], cond, form, DomainOperation$TM[ dom, Times$TM], DomainOperation$TM[ dom, 1]]) =!= $Failed
	]
	
SetAttributes[ valueIteration, HoldRest]
(* 'valueIteration[ iter, cond, term, op, def]' may only be called with both 'op' and 'def' being individuals! *)
valueIteration[ {x_, iter__}, cond_, term_, op_, def_] :=  
 Module[ {val = $Null, ci, comp, i},
 	(* "$Null" is meant to indicate that "val" does not have a value yet. *)
	Catch[
		Do[
			If[ Hold[ cond] === Hold[ True], (* cond must be kept unevaluated! *)
				ci = True,
				ci = ReleaseHold[ substituteFree[ Hold[ cond], {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]]
			];
			If[ ci,
				comp = ReleaseHold[ substituteFree[ Hold[ term], {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]];
				If[ val === $Null,
					val = comp,
					val = op[ val, comp]
				],
				(*else*)
				Continue[],
				(*default*)
				Throw[ $Failed];
			],
			{i, iter}
		]; (*end do*)
		If[ val === $Null,
			def,
			val
		]
	] (*end catch*)
 ]
valueIteration[ _List, _, _, _, _] := $Failed
valueIteration[ $Failed, _, _, _, _] := $Failed
valueIteration[ {x_, iter__}, cond_, term_] :=  
 Module[ {val = {}, ci, comp, i},
	Catch[
		Do[
			If[ TrueQ[ cond],
				ci = True,
				ci = ReleaseHold[ substituteFree[ Hold[ cond], {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]]
			];
			If[ ci,
				comp = ReleaseHold[ substituteFree[ Hold[ term], {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]];
				AppendTo[ val, comp],
				(*else*)
				Continue[],
				(*default*)
				Throw[ $Failed];
			],
			{i, iter}
		]; (*end do*)
		val
	] (*end catch*)
 ]
valueIteration[ _List, _, _] := $Failed
valueIteration[ $Failed, _, _] := $Failed
valueIteration[ args___] := unexpected[ valueIteration, {args}]


MaximumOf$TM[ rng:RNG$[ _SETRNG$ | _STEPRNG$, __], cond_, form_] /; buiActive["MaximumOf"] :=
 	splitQuantifier[ MaximumOf$TM, rng, cond, form]
MaximumOf$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["MaximumOf"] :=
	Module[ {v},
		max$TM[ Set$TM @@ Union[ v]] /; (v = valueIteration[ rangeToIterator[ r], cond, form]) =!= $Failed
	]
(h:Annotated$TM[ MaximumOf$TM, _SubScript$TM])[ rng:RNG$[ _SETRNG$ | _STEPRNG$, __], cond_, form_] /; buiActive["MaximumOf"] :=
 	splitQuantifier[ h, rng, cond, form]
Annotated$TM[ MaximumOf$TM, sub_SubScript$TM][ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["MaximumOf"] :=
	Module[ {v},
		Annotated$TM[ max$TM, sub][ Set$TM @@ Union[ v]] /; (v = valueIteration[ rangeToIterator[ r], cond, form]) =!= $Failed
	]
	
MinimumOf$TM[ rng:RNG$[ _SETRNG$ | _STEPRNG$, __], cond_, form_] /; buiActive["MinimumOf"] :=
 	splitQuantifier[ MinimumOf$TM, rng, cond, form]
MinimumOf$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["MinimumOf"] :=
	Module[ {v},
		min$TM[ Set$TM @@ Union[ v]] /; (v = valueIteration[ rangeToIterator[ r], cond, form]) =!= $Failed
	]
(h:Annotated$TM[ MinimumOf$TM, _SubScript$TM])[ rng:RNG$[ _SETRNG$ | _STEPRNG$, __], cond_, form_] /; buiActive["MinimumOf"] :=
 	splitQuantifier[ h, rng, cond, form]
Annotated$TM[ MinimumOf$TM, sub_SubScript$TM][ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["MinimumOf"] :=
	Module[ {v},
		Annotated$TM[ min$TM, sub][ Set$TM @@ Union[ v]] /; (v = valueIteration[ rangeToIterator[ r], cond, form]) =!= $Failed
	]
	
UnionOf$TM[ rng:RNG$[ _SETRNG$ | _STEPRNG$, __], cond_, form_] /; buiActive["UnionOf"] :=
 	splitQuantifier[ UnionOf$TM, rng, cond, form]
UnionOf$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["UnionOf"] :=
	Module[ {v},
		v /; (v = valueIteration[ rangeToIterator[ r], cond, form, Union$TM, Set$TM[]]) =!= $Failed
	]
(h:Annotated$TM[ UnionOf$TM, _SubScript$TM])[ rng:RNG$[ _SETRNG$ | _STEPRNG$, __], cond_, form_] /; buiActive["UnionOf"] :=
 	splitQuantifier[ h, rng, cond, form]
Annotated$TM[ UnionOf$TM, sub_SubScript$TM][ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["UnionOf"] :=
	Module[ {v},
		v /; (v = valueIteration[ rangeToIterator[ r], cond, form, Annotated$TM[ Union$TM, sub], Set$TM[]]) =!= $Failed
	]
	
IntersectionOf$TM[ rng:RNG$[ _SETRNG$ | _STEPRNG$, __], cond_, form_] /; buiActive["IntersectionOf"] :=
 	splitQuantifier[ IntersectionOf$TM, rng, cond, form]
IntersectionOf$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["IntersectionOf"] :=
	Module[ {v},
		v /; (v = valueIteration[ rangeToIterator[ r], cond, form, Intersection$TM, $Failed]) =!= $Failed
	]
(h:Annotated$TM[ IntersectionOf$TM, _SubScript$TM])[ rng:RNG$[ _SETRNG$ | _STEPRNG$, __], cond_, form_] /; buiActive["IntersectionOf"] :=
 	splitQuantifier[ h, rng, cond, form]
Annotated$TM[ IntersectionOf$TM, sub_SubScript$TM][ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["IntersectionOf"] :=
	Module[ {v},
		v /; (v = valueIteration[ rangeToIterator[ r], cond, form, Annotated$TM[ Intersection$TM, sub], $Failed]) =!= $Failed
	]
	
(* ::Subsection:: *)
(* the, such *)

(* "rngCondToIterator" converts several ranges into iterators, where for each iterator only the part of the condition
	'cond' is considered which really matters ("splitAnd"). It returns a list of pairs, where each pair consists of
	- an iterator and
	- the corresponding condition
	If at least one range cannot be converted into a valid iterator (i.e. a list with at least 2 elements),
	$Failed is returned.
*)
rngCondToIterator[ RNG$[ r_], cond_Hold ] :=
	Module[ {it},
		it = rangeToIterator[ r];
		If[ MatchQ[ it, {_, __}],
			{{rangeToIterator[ r], cond}},
			$Failed
		]
	]
rngCondToIterator[ RNG$[ r_, s__], cond_Hold ] :=
	Module[ {splitC, it, l},
		it = rangeToIterator[ r];
		If[ MatchQ[ it, {_, __}],
			splitC = splitAnd[ cond, {Hold[ r][[1, 1]]}];
			l = rngCondToIterator[ RNG$[ s], Last[ splitC]];
			If[ l === $Failed,
				$Failed,
				Append[ l, {it, First[ splitC]}]
			],
			$Failed
		]
	]

(* "suchIterationF" returns '{i}', where 'i' is such that 'form' gives True.
	If no such 'i' exists, $Failed is returned. *)
suchIterationF[ form_Hold, {{x_, iter__}, cond_Hold}] :=
 Module[ {ci, sub, i},
	Catch[
		Do[
			If[ cond === Hold[ True],
				ci = True,
				(*else*)
            	ci = ReleaseHold[ substituteFree[ cond, {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]]
			];
			If[ ci,
				sub = ReleaseHold[ substituteFree[ form, {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]];
				If[ sub, Throw[ {i}]]
			],
			{ i, iter}
		]; (*end do*)
		$Failed
	] (*end catch*)
 ]
suchIterationF[ _, {_List, _}] := $Failed
suchIterationF[ _, {$Failed, _}] := $Failed
suchIterationF[ args___] := 
 unexpected[ suchIterationF, {args}]
(* "suchIterationT" returns 'Prepend[term, i]', where 'i' is such that 'term' evaluates to a list.
	If no such 'i' exists, $Failed is returned. *)
suchIterationT[ term_Hold, {{x_, iter__}, cond_Hold}] :=
 Module[ {ci, sub, i},
	Catch[
		Do[
			If[ cond === Hold[ True],
				ci = True,
				(*else*)
            	ci = ReleaseHold[ substituteFree[ cond, {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]]
			];
			If[ ci,
				sub = ReleaseHold[ substituteFree[ term, {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]];
				If[ MatchQ[ sub, {___}], Throw[ Prepend[ sub, i]]]
			],
			{ i, iter}
		]; (*end do*)
		$Failed
	] (*end catch*)
 ]
suchIterationT[ _, {_List, _}] := $Failed
suchIterationT[ _, {$Failed, _}] := $Failed
suchIterationT[ args___] := 
 unexpected[ suchIterationT, {args}]
 
Such$TM[ r:RNG$[ _, __], cond_, form_] /; buiActive["Such"] :=
 	Module[ {rcList, res},
 		Apply[ Tuple$TM, res] /; (
 			rcList = rngCondToIterator[ r, Hold[ cond]];
 			If[ rcList === $Failed,
 				False,
	 			With[ {r1 = First[ rcList]},
	 				res = ReleaseHold[ Fold[ Hold[ suchIterationT[ #1, #2]]&, Hold[ suchIterationF[ Hold[ form], r1]], Rest[ rcList]]]
	 			];
	 			res =!= $Failed
 			]
 			)
	]
Such$TM[ RNG$[ r_], cond_, form_] /; buiActive["Such"] :=
	Module[ {res},
		(* "suchIterationF" always returns a 1-element list, unless it returns $Failed *)
		First[ res] /; (res = suchIterationF[ Hold[ form], {rangeToIterator[ r], Hold[ cond]}]) =!= $Failed
	]
	
	
theIterationF[ form_Hold, {{x_, iter__}, cond_Hold}] :=
 Module[ {ci, sub, i, out = $Failed},
	Catch[
		Do[
			If[ cond === Hold[ True],
				ci = True,
				(*else*)
            	ci = ReleaseHold[ substituteFree[ cond, {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]]
			];
			If[ ci,
				sub = ReleaseHold[ substituteFree[ form, {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]];
				If[ sub,
					If[ out === $Failed,
						out = {i},
						Throw[ $Failed]
					],
					Continue[],
					Throw[ $Failed]
				],
				Continue[],
				Throw[ $Failed]
			],
			{ i, iter}
		]; (*end do*)
		out
	] (*end catch*)
 ]
theIterationF[ _, {_List, _}] := $Failed
theIterationF[ _, {$Failed, _}] := $Failed
theIterationF[ args___] := 
 unexpected[ theIterationF, {args}]
theIterationT[ term_Hold, {{x_, iter__}, cond_Hold}] :=
 Module[ {ci, sub, i, out = $Failed},
	Catch[
		Do[
			If[ cond === Hold[ True],
				ci = True,
				(*else*)
            	ci = ReleaseHold[ substituteFree[ cond, {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]]
			];
			If[ ci,
				sub = ReleaseHold[ substituteFree[ term, {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]];
				If[ MatchQ[ sub, {___}],
					If[ out === $Failed,
						out = Prepend[ sub, i],
						Throw[ $Failed]
					]
				],
				Continue[],
				Throw[ $Failed]
			],
			{ i, iter}
		]; (*end do*)
		out
	] (*end catch*)
 ]
theIterationT[ _, {_List, _}] := $Failed
theIterationT[ _, {$Failed, _}] := $Failed
theIterationT[ args___] := 
 unexpected[ theIterationT, {args}]
 
SuchUnique$TM[ r:RNG$[ _, __], cond_, form_] /; buiActive["SuchUnique"] :=
 	Module[ {rcList, res},
 		Apply[ Tuple$TM, res] /; (
 			rcList = rngCondToIterator[ r, Hold[ cond]];
 			If[ rcList === $Failed,
 				False,
	 			With[ {r1 = First[ rcList]},
	 				res = ReleaseHold[ Fold[ Hold[ theIterationT[ #1, #2]]&, Hold[ theIterationF[ Hold[ form], r1]], Rest[ rcList]]]
	 			];
	 			res =!= $Failed
 			]
 			)
	]
SuchUnique$TM[ RNG$[ r_], cond_, form_] /; buiActive["SuchUnique"] :=
	Module[ {res},
		(* "theIterationF" always returns a 1-element list, unless it returns $Failed *)
		First[ res] /; (res = theIterationF[ Hold[ form], {rangeToIterator[ r], Hold[ cond]}]) =!= $Failed
	]
	
	
(* ::Subsection:: *)
(* argmin, argmax, theargmin, theargmax *)

(* "iteratorValueIteration" returns the list of all '{i, v}',
	where 'i' iterates over the whole range and 'v' is the value of 'term' at 'i'. *)
iteratorValueIteration[ term_Hold, {{x_, iter__}, cond_Hold}] :=
 Module[ {ci, i, out = {}},
	Catch[
		Do[
			If[ cond === Hold[ True],
				ci = True,
				(*else*)
            	ci = ReleaseHold[ substituteFree[ cond, {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]]
			];
			If[ ci,
				AppendTo[ out, {i, ReleaseHold[ substituteFree[ term, {x -> i}, "checkTypes" -> False, "postprocessing" -> Identity]]}],
				Continue[],
				Throw[ $Failed]
			],
			{ i, iter}
		]; (*end do*)
		out
	] (*end catch*)
 ]
iteratorValueIteration[ args___] := 
 unexpected[ iteratorValueIteration, {args}]
 
(* "findFirstPath" takes some object 'x' and a list as returned by "iteratorValueIteration"
	and returns the list of iterators leading to the first occurrence of 'x' as value.
	If not such iterators exist, $Failed is returned. *)
findFirstPath[x_, {a_, x_}] := {a}
findFirstPath[x_, {a_, l_List}] :=
	Module[{tmp},
		Catch[
			Scan[
				(tmp = findFirstPath[x, #];
				If[tmp =!= $Failed, Throw[Prepend[tmp, a]]]) &,
				l
	     	];
			$Failed
		]
	]
findFirstPath[x_, l_List] :=
	Module[{tmp},
		Catch[
			Scan[
				(tmp = findFirstPath[x, #];
				If[tmp =!= $Failed, Throw[tmp]]) &,
				l
			];
			$Failed
		]
	]
findFirstPath[___] := $Failed;
 
ArgMin$TM[ r:RNG$[ __], cond_, term_] /; buiActive["ArgMin"] :=
	Module[ {res, rcList, m},
		(
		If[ Length[ res] === 1,
			First[ res],
			Apply[ Tuple$TM, res]
		]
		) /; (
			rcList = rngCondToIterator[ r, Hold[ cond]];
			If[ rcList === $Failed,
				False,
	 			res = ReleaseHold[ Fold[ Hold[ iteratorValueIteration[ #1, #2]]&, Hold[ term], rcList]];
	 			(* The "Cases[...]" extracts all values and drops all iterators *)
	 			m = Min[ Cases[ res, {___, x:Except[ _List]} :> x, 2 * Length[ r]]];
	 			res = findFirstPath[ m, res];
	 			res =!= $Failed
			]
 			)
	]
Annotated$TM[ ArgMin$TM, SubScript$TM[ ord_]][ r_RNG$, cond_, term_] /; buiActive["ArgMin"] :=
	Module[ {res, rcList, m},
		(
		If[ Length[ res] === 1,
			First[ res],
			Apply[ Tuple$TM, res]
		]
		) /; (
			rcList = rngCondToIterator[ r, Hold[ cond]];
			If[ rcList === $Failed,
				False,
	 			res = ReleaseHold[ Fold[ Hold[ iteratorValueIteration[ #1, #2]]&, Hold[ term], rcList]];
	 			m = min[ Cases[ res, {___, x:Except[ _List]} :> x, 2 * Length[ r]], ord];
	 			If[ MatchQ[ m, {_}],
	 				res = findFirstPath[ First[ m], res];
	 				res =!= $Failed,
	 				False
	 			]
			]
 			)
	]
	
ArgMax$TM[ r:RNG$[ __], cond_, term_] /; buiActive["ArgMax"] :=
	Module[ {res, rcList, m},
		(
		If[ Length[ res] === 1,
			First[ res],
			Apply[ Tuple$TM, res]
		]
		) /; (
			rcList = rngCondToIterator[ r, Hold[ cond]];
			If[ rcList === $Failed,
				False,
	 			res = ReleaseHold[ Fold[ Hold[ iteratorValueIteration[ #1, #2]]&, Hold[ term], rcList]];
	 			m = Max[ Cases[ res, {___, x:Except[ _List]} :> x, 2 * Length[ r]]];
	 			res = findFirstPath[ m, res];
	 			res =!= $Failed
			]
 			)
	]
Annotated$TM[ ArgMax$TM, SubScript$TM[ ord_]][ r_RNG$, cond_, term_] /; buiActive["ArgMax"] :=
	Module[ {res, rcList, m},
		(
		If[ Length[ res] === 1,
			First[ res],
			Apply[ Tuple$TM, res]
		]
		) /; (
			rcList = rngCondToIterator[ r, Hold[ cond]];
			If[ rcList === $Failed,
				False,
	 			res = ReleaseHold[ Fold[ Hold[ iteratorValueIteration[ #1, #2]]&, Hold[ term], rcList]];
	 			m = max[ Cases[ res, {___, x:Except[ _List]} :> x, 2 * Length[ r]], ord];
	 			If[ MatchQ[ m, {_}],
	 				res = findFirstPath[ First[ m], res];
	 				res =!= $Failed,
	 				False
	 			]
			]
 			)
	]
	
TheArgMin$TM[ r:RNG$[ __], cond_, term_] /; buiActive["TheArgMin"] :=
	Module[ {res, rcList, m, v},
		(
		If[ Length[ res] === 1,
			First[ res],
			Apply[ Tuple$TM, res]
		]
		) /; (
			rcList = rngCondToIterator[ r, Hold[ cond]];
			If[ rcList === $Failed,
				False,
	 			res = ReleaseHold[ Fold[ Hold[ iteratorValueIteration[ #1, #2]]&, Hold[ term], rcList]];
	 			v = Cases[ res, {___, x:Except[ _List]} :> x, 2 * Length[ r]];
	 			m = Min[ v];
	 			If[ Count[ v, m] === 1,
	 				res = findFirstPath[ m, res];
	 				res =!= $Failed,
	 				False
	 			]
			]
 			)
	]
Annotated$TM[ TheArgMin$TM, SubScript$TM[ ord_]][ r:RNG$[ __], cond_, term_] /; buiActive["TheArgMin"] :=
	Module[ {res, rcList, m, v},
		(
		If[ Length[ res] === 1,
			First[ res],
			Apply[ Tuple$TM, res]
		]
		) /; (
			rcList = rngCondToIterator[ r, Hold[ cond]];
			If[ rcList === $Failed,
				False,
	 			res = ReleaseHold[ Fold[ Hold[ iteratorValueIteration[ #1, #2]]&, Hold[ term], rcList]];
	 			v = Cases[ res, {___, x:Except[ _List]} :> x, 2 * Length[ r]];
	 			m = min[ v, ord];
	 			If[ MatchQ[ m, {_}] && Count[ v, First[ m]] === 1,
	 				res = findFirstPath[ First[ m], res];
	 				res =!= $Failed,
	 				False
	 			]
			]
 			)
	]
	
TheArgMax$TM[ r:RNG$[ __], cond_, term_] /; buiActive["TheArgMax"] :=
	Module[ {res, rcList, m, v},
		(
		If[ Length[ res] === 1,
			First[ res],
			Apply[ Tuple$TM, res]
		]
		) /; (
			rcList = rngCondToIterator[ r, Hold[ cond]];
			If[ rcList === $Failed,
				False,
	 			res = ReleaseHold[ Fold[ Hold[ iteratorValueIteration[ #1, #2]]&, Hold[ term], rcList]];
	 			v = Cases[ res, {___, x:Except[ _List]} :> x, 2 * Length[ r]];
	 			m = Max[ v];
	 			If[ Count[ v, m] === 1,
	 				res = findFirstPath[ m, res];
	 				res =!= $Failed,
	 				False
	 			]
			]
 			)
	]
Annotated$TM[ TheArgMax$TM, SubScript$TM[ ord_]][ r:RNG$[ __], cond_, term_] /; buiActive["TheArgMax"] :=
	Module[ {res, rcList, m, v},
		(
		If[ Length[ res] === 1,
			First[ res],
			Apply[ Tuple$TM, res]
		]
		) /; (
			rcList = rngCondToIterator[ r, Hold[ cond]];
			If[ rcList === $Failed,
				False,
	 			res = ReleaseHold[ Fold[ Hold[ iteratorValueIteration[ #1, #2]]&, Hold[ term], rcList]];
	 			v = Cases[ res, {___, x:Except[ _List]} :> x, 2 * Length[ r]];
	 			m = max[ v, ord];
	 			If[ MatchQ[ m, {_}] && Count[ v, First[ m]] === 1,
	 				res = findFirstPath[ First[ m], res];
	 				res =!= $Failed,
	 				False
	 			]
			]
 			)
	]
	

(* ::Section:: *)
(* Sets *)

Set$TM /: Equal$TM[ _Set$TM, _Tuple$TM] /; buiActive["SetEqual"] || buiActive["TupleEqual"] := False
Set$TM /: Annotated$TM[ Equal$TM, SubScript$TM[ _]][ _Set$TM, _Tuple$TM] /; buiActive["SetEqual"] || buiActive["TupleEqual"] := False
Set$TM /: (h:(SubsetEqual$TM|Subset$TM|SupersetEqual$TM|Superset$TM))[ _Set$TM, _Tuple$TM] /; buiActive[StringDrop[SymbolName[h], -3]] := False
Set$TM /: Annotated$TM[ h:(SubsetEqual$TM|Subset$TM|SupersetEqual$TM|Superset$TM), SubScript$TM[ _]][ _Set$TM, _Tuple$TM] /; buiActive[StringDrop[SymbolName[h], -3]] := False

Set$TM /: Equal$TM[ (a_Set$TM)..] /; buiActive["SetEqual"] := True

Set$TM /: Equal$TM[ _Set$TM] /; buiActive["SetEqual"] := True
Set$TM /: Annotated$TM[ Equal$TM, SubScript$TM[ _]][ _Set$TM] /; buiActive["SetEqual"] := True
Set$TM /: (op:(SubsetEqual$TM|Subset$TM|SupersetEqual$TM|Superset$TM))[ _Set$TM] /; buiActive[StringDrop[SymbolName[op], -3]] := True
Set$TM /: Annotated$TM[ h:(SubsetEqual$TM|Subset$TM|SupersetEqual$TM|Superset$TM), SubScript$TM[ _]][ _Set$TM] /; buiActive[ StringDrop[ SymbolName[ h], -3]] := True
Set$TM /: Intersection$TM[ a_Set$TM] /; buiActive["Intersection"] := a
Set$TM /: Intersection$TM[ a_Set$TM, b_, c__] /; buiActive["Intersection"] :=
	Fold[ Intersection$TM, a, {b, c}]
Set$TM /: Annotated$TM[ Intersection$TM, SubScript$TM[ _]][ a_Set$TM] /; buiActive["Intersection"] := a
Set$TM /: (op:(Annotated$TM[ Intersection$TM, SubScript$TM[ _]]))[ a_Set$TM, b_, c__] /; buiActive["Intersection"] :=
	Fold[ op, a, {b, c}]


Set$TM /: Equal$TM[ a_Set$TM, b_Set$TM] /; buiActive["SetEqual"] :=
	Module[ {res},
		res /; (res = subseteq[ a, b, Equal$TM];
				If[ res === True,
					res = subseteq[ b, a, Equal$TM]
				];
				MatchQ[ res, True|False])
	]
Set$TM /: Annotated$TM[ Equal$TM, SubScript$TM[ dom_]][ a_Set$TM, b_Set$TM] /; buiActive["SetEqual"] :=
	Module[ {res},
		res /; (res = subseteq[ a, b, DomainOperation$TM[ dom, Equal$TM]];
				If[ res === True,
					res = subseteq[ b, a, DomainOperation$TM[ dom, Equal$TM]]
				];
				MatchQ[ res, True|False])
	]
Set$TM /: SubsetEqual$TM[ a_Set$TM, b_Set$TM] /; buiActive["SubsetEqual"] :=
	Module[ {res},
		res /; (res = subseteq[ a, b, Equal$TM]; MatchQ[ res, True|False])
	]
Set$TM /: Annotated$TM[ SubsetEqual$TM, SubScript$TM[ dom_]][ a_Set$TM, b_Set$TM] /; buiActive["SubsetEqual"] :=
		Module[ {res},
		res /; (res = subseteq[ a, b, DomainOperation$TM[ dom, Equal$TM]]; MatchQ[ res, True|False])
	]
Set$TM /: Subset$TM[ a_Set$TM, b_Set$TM] /; buiActive["Subset"] :=
	Module[ {res},
		res /; (res = subseteq[ a, b, Equal$TM];
				If[ res === True,
					res = !subseteq[ b, a, Equal$TM]
				];
				MatchQ[ res, True|False])
	]
Set$TM /: Annotated$TM[ Subset$TM, SubScript$TM[ dom_]][ a_Set$TM, b_Set$TM] /; buiActive["Subset"] :=
	Module[ {res},
		res /; (res = subseteq[ a, b, DomainOperation$TM[ dom, Equal$TM]];
				If[ res === True,
					res = !subseteq[ b, a, DomainOperation$TM[ dom, Equal$TM]]
				];
				MatchQ[ res, True|False])
	]
Set$TM /: SupersetEqual$TM[ a_Set$TM, b_Set$TM] /; buiActive["SupersetEqual"] :=
	Module[ {res},
		res /; (res = subseteq[ b, a, Equal$TM]; MatchQ[ res, True|False])
	]
Set$TM /: Annotated$TM[ SupersetEqual$TM, SubScript$TM[ dom_]][ a_Set$TM, b_Set$TM] /; buiActive["SupersetEqual"] :=
	Module[ {res},
		res /; (res = subseteq[ b, a, DomainOperation$TM[ dom, Equal$TM]]; MatchQ[ res, True|False])
	]
Set$TM /: Superset$TM[ a_Set$TM, b_Set$TM] /; buiActive["Superset"] :=
	Module[ {res},
		res /; (res = subseteq[ b, a, Equal$TM];
				If[ res === True,
					res = !subseteq[ a, b, Equal$TM]
				];
				MatchQ[ res, True|False])
	]
Set$TM /: Annotated$TM[ Superset$TM, SubScript$TM[ dom_]][ a_Set$TM, b_Set$TM] /; buiActive["Superset"] :=
	Module[ {res},
		res /; (res = subseteq[ b, a, DomainOperation$TM[ dom, Equal$TM]];
				If[ res === True,
					res = !subseteq[ a, b, DomainOperation$TM[ dom, Equal$TM]]
				];
				MatchQ[ res, True|False])
	]

(* "Union" can be implemented in this nice way (in contrast to "Intersection", "Complement", ...),
	because in any case it does not harm to put more elements into the resulting set than actually needed
	(some might be equal).
	Also note that it is possible to form the union over 0 sets, whereas the intersection of 0 sets is not defined. *)
Set$TM /: Union$TM[ a___Set$TM] /; buiActive["Union"] :=
	Union[ a, SameTest -> (SameQ[ #1, #2] || (isIndividual[ #1] && isIndividual[ #2] && TrueQ[ Equal$TM[ #1, #2]])&)]
Set$TM /: Annotated$TM[ Union$TM, SubScript$TM[ dom_]][ a___Set$TM] /; buiActive["Union"] :=
	Union[ a, SameTest -> (SameQ[ #1, #2] || (isIndividual[ #1] && isIndividual[ #2] && TrueQ[ DomainOperation$TM[ dom, Equal$TM][ #1, #2]])&)]
Set$TM /: Intersection$TM[ a_Set$TM, b_Set$TM] /; buiActive["Intersection"] :=
	Module[ {res = Set$TM[]},
		res /; (Scan[ If[ elementOf[ #, b, Equal$TM], AppendTo[ res, #], Null, res = False; Return[]]&, a]; res =!= False)
	]
Set$TM /: Annotated$TM[ Intersection$TM, SubScript$TM[ dom_]][ a_Set$TM, b_Set$TM] /; buiActive["Intersection"] :=
	Module[ {res = Set$TM[]},
		res /; (Scan[ If[ elementOf[ #, b, DomainOperation$TM[ dom, Equal$TM]], AppendTo[ res, #], Null, res = False; Return[]]&, a]; res =!= False)
	]
Set$TM /: Backslash$TM[ a_Set$TM, b___Set$TM] /; buiActive["Difference"] :=
	With[ {ub = Union[ b]},
		Module[ {res = Set$TM[]},
			res /; (Scan[ If[ elementOf[ #, ub, Equal$TM], Null, AppendTo[ res, #], res = False; Return[]] &, a]; res =!= False)
		]
	]
Set$TM /: Annotated$TM[ Backslash$TM, SubScript$TM[ dom_]][ a_Set$TM, b___Set$TM] /; buiActive["Difference"] :=
	With[ {ub = Union[ b]},
		Module[ {res = Set$TM[]},
			res /; (Scan[ If[ elementOf[ #, ub, DomainOperation$TM[ dom, Equal$TM]], Null, AppendTo[ res, #], res = False; Return[]] &, a]; res =!= False)
		]
	]
Set$TM /: EmptyUpTriangle$TM[ a_Set$TM, b_Set$TM] /; buiActive["SymmetricDifference"] :=
	Module[ {res = Set$TM[]},
		res /;
			(Scan[ If[ elementOf[ #, b, Equal$TM], Null, AppendTo[ res, #], res = False; Return[]] &, a];
			If[ res === False,
				False,
				Scan[ If[ elementOf[ #, a, Equal$TM], Null, AppendTo[ res, #], res = False; Return[]] &, b];
				res =!= False
			])
	]
Set$TM /: Annotated$TM[ EmptyUpTriangle$TM, SubScript$TM[ dom_]][ a_Set$TM, b_Set$TM] /; buiActive["SymmetricDifference"] :=
	Module[ {res = Set$TM[]},
		res /;
			(Scan[ If[ elementOf[ #, b, DomainOperation$TM[ dom, Equal$TM]], Null, AppendTo[ res, #], res = False; Return[]] &, a];
			If[ res === False,
				False,
				Scan[ If[ elementOf[ #, a, DomainOperation$TM[ dom, Equal$TM]], Null, AppendTo[ res, #], res = False; Return[]] &, b];
				res =!= False
			])
	]
Set$TM /: Cross$TM[ a:(Set$TM[ ___?isIndividual]..)] /; buiActive["CartesianProduct"] :=
	Set$TM @@ Replace[ Tuples[ {a}], List[ x__] :> Tuple$TM[ x], {1}]
Set$TM /: Element$TM[ p_, a_Set$TM] /; buiActive["IsElement"] :=
	With[ {res = elementOf[ p, a, Equal$TM]},
		res /; MatchQ[ res, True|False]
	]
Set$TM /: Annotated$TM[ Element$TM, SubScript$TM[ dom_]][ p_, a_Set$TM] /; buiActive["IsElement"] :=
	With[ {res = elementOf[ p, a, DomainOperation$TM[ dom, Equal$TM]]},
		res /; MatchQ[ res, True|False]
	]
Set$TM /: \[ScriptCapitalP]$TM[ a:Set$TM[ ___?isIndividual]] /; buiActive["PowerSet"] := Set$TM @@ Subsets[ a]
Set$TM /: BracketingBar$TM[ a_Set$TM] /; buiActive["Cardinality"] :=
	With[ {a0 = DeleteDuplicates[ a]},
		Length[ a0] /; pairwiseDistinct[ a0, Equal$TM]	(* 'a' must not contain sequence elements; this is checked in 'pairwiseDistinct'. *)
	]
Set$TM /: max$TM[ Set$TM[ e__]] /; buiActive["MaximumElementSet"] :=
	Module[ {res = applyFlexOperation[ DeleteDuplicates[ Hold[ e]], max$TM, Max, $Failed, DirectedInfinity[ 1]]},
		(res /. Max -> max$TM /. {m:(max$TM[ _Set$TM]) :> m, max$TM[ x___] :> max$TM[ Set$TM[ x]]}) /; res =!= $Failed
	]
Set$TM /: Annotated$TM[ max$TM, SubScript$TM[ _]][ Set$TM[ e_?isIndividual]] /; buiActive["MaximumElementSet"] :=
	e
Set$TM /: Annotated$TM[ max$TM, s:SubScript$TM[ ord_]][ Set$TM[ e__]] /; buiActive["MaximumElementSet"] :=
	Module[ {res},
		Annotated$TM[ max$TM, s][ Set$TM @@ res] /; (res = max[ {e}, ord]; Length[ res] < Length[ Hold[ e]])
	]
Set$TM /: min$TM[ Set$TM[ e__]] /; buiActive["MinimumElementSet"] :=
	Module[ {res = applyFlexOperation[ DeleteDuplicates[ Hold[ e]], min$TM, Min, $Failed, DirectedInfinity[ -1]]},
		(res /. Min -> min$TM /. {m:(min$TM[ _Set$TM]) :> m, min$TM[ x___] :> min$TM[ Set$TM[ x]]}) /; res =!= $Failed
	]
Set$TM /: Annotated$TM[ min$TM, SubScript$TM[ _]][ Set$TM[ e_?isIndividual]] /; buiActive["MinimumElementSet"] := e
Set$TM /: Annotated$TM[ min$TM, s:SubScript$TM[ ord_]][ Set$TM[ e__]] /; buiActive["MinimumElementSet"] :=
	Module[ {res},
		Annotated$TM[ min$TM, s][ Set$TM @@ res] /; (res = min[ {e}, ord]; Length[ res] < Length[ Hold[ e]])
	]
Set$TM /: \[AE]$TM[ Set$TM[ ___, a_?isIndividual, ___]] /; buiActive["AnElement"] := a
	

(* The following implementation of "max" and "min" has quadratic complexity in the length of the
	input. One could, however, also compare only successive elements, but this method would only give
	the right result in case of a linear ordering, not in case of an arbitrary partial ordering!
	Still, it is assumed that the given relation is at least transitive; If this is not the case, wrong
	results might be returned. *)
	
max[ {a_, b___}, ord_] := max[ {a}, {b}, ord]
max[ l_List, {a_, b___}, ord_] :=
	max[ updateMaxList[ l, a, ord], {b}, ord]
max[ l_List, {}, _] := l

updateMaxList[ l_List, a_?isIndividual, ord_] :=
	Module[ {add = True},
		With[ {out = Select[ l,
						If[ TrueQ[ a == #],
							False,
						(*else*)
							If[ isIndividual[ #],
								If[ TrueQ[ ord[ #, a]],
									False,
								(*else*)
									If[ TrueQ[ ord[ a, #]],
										add = False
									];
									True
								],
							(*else*)
								True
							]
						]&
					]
				},
			If[ add, Append[ out, a], out]
		]
	]
updateMaxList[ l_List, a_, _] :=
	If[ MemberQ[ l, a], l, Append[ l, a]]

min[ {a_, b___}, ord_] := min[ {a}, {b}, ord]
min[ l_List, {a_, b___}, ord_] :=
	min[ updateMinList[ l, a, ord], {b}, ord]
min[ l_List, {}, _] := l

updateMinList[ l_List, a_?isIndividual, ord_] :=
	Module[ {add = True},
		With[ {out = Select[ l,
						If[ TrueQ[ a == #],
							False,
						(*else*)
							If[ isIndividual[ #],
								If[ TrueQ[ ord[ a, #]],
									False,
								(*else*)
									If[ TrueQ[ ord[ #, a]],
										add = False
									];
									True
								],
							(*else*)
								True
							]
						]&
					]
				},
			If[ add, Append[ out, a], out]
		]
	]
updateMinList[ l_List, a_, _] :=
	If[ MemberQ[ l, a], l, Append[ l, a]]

elementOf[ p_, a_, test_] :=
	elementOf[ p, a, test, isIndividual[ p]]
elementOf[ p_, a_, test_, pInd_] :=
	Module[ {out = False},
		Catch[
			Scan[
				If[ p === # && test === Equal$TM,
					Throw[ True],
				(*else*)
					If[ pInd && isIndividual[ #],
						If[ test[ p, #],
							Throw[ True],
						(*else*)
							Null,
						(*else*)
							out = $Failed
						],
					(*else*)
						out = $Failed
					]
				]&,
				a
			];
			Throw[ out]
		]
	]

pairwiseDistinct[ _[ f_, rest___], test_] := isIndividual[ f] && elementOf[ f, {rest}, test, True] === False && pairwiseDistinct[ {rest}, test]
pairwiseDistinct[ _[], _] := True

subseteq[ a_, a_, Equal$TM] := True
subseteq[ a_Set$TM, b_Set$TM, test_] :=
	Module[ {res = True},
		Scan[ If[ elementOf[ #, b, test], Null, res = False; Return[], res = Null] &, a];
		res
	]
subseteq[ IntegerInterval$TM[ al_, ar_, alc_, arc_], b_Set$TM, Equal$TM] :=
	Module[ {s = intervalSize[ IntegerInterval$TM, al, ar, alc, arc], l, r},
		If[ s <= Length[ b],
			l = integerBoundary[ "left", al, alc];
			r = integerBoundary[ "right", ar, arc];
			NumberQ[ l] && NumberQ[ r] && subseteq[ Set$TM @@ Range[ l, r], b, Equal$TM],
		(*else*)
			False
		]
	]
subseteq[ (a:(RationalInterval$TM|RealInterval$TM))[ al_, ar_, alc_, arc_], b_Set$TM, Equal$TM] :=
	Switch[ intervalSize[ a, al, ar, alc, arc],
		1, elementOf[ al, b, Equal$TM],
		$Failed, $Failed,
		_, False
	]
subseteq[ \[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM, b_Set$TM, Equal$TM] := False
subseteq[ a_Set$TM, b:(_IntegerInterval$TM|_RationalInterval$TM|_RealInterval$TM), Equal$TM] :=
	Module[ {subset = True},
		Catch[
			Scan[ If[ isInInterval[ #, b], Null, Throw[ False], subset = $Failed]&, a];
			subset
		]
	]
subseteq[ a_Set$TM, \[DoubleStruckCapitalC]$TM, Equal$TM] :=
	Module[ {subset = True},
		Catch[
			Scan[ If[ isComplex[ #], Null, Throw[ False], subset = $Failed]&, a];
			subset
		]
	]
subseteq[ a_Set$TM, \[DoubleStruckCapitalC]P$TM, Equal$TM] :=
	Module[ {subset = True},
		Catch[
			Scan[ If[ isComplexP[ #], Null, Throw[ False], subset = $Failed]&, a];
			subset
		]
	]
subseteq[ _IntegerInterval$TM|_RationalInterval$TM|_RealInterval$TM, \[DoubleStruckCapitalC]$TM, Equal$TM] := True
subseteq[ _IntegerInterval$TM|_RationalInterval$TM|_RealInterval$TM, \[DoubleStruckCapitalC]P$TM, Equal$TM] := False
subseteq[ \[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM, _IntegerInterval$TM|_RationalInterval$TM|_RealInterval$TM, Equal$TM] := False
subseteq[ \[DoubleStruckCapitalC]$TM, \[DoubleStruckCapitalC]P$TM, Equal$TM] := False
subseteq[ \[DoubleStruckCapitalC]P$TM, \[DoubleStruckCapitalC]$TM, Equal$TM] := False
subseteq[ IntegerInterval$TM[ al_, ar_, alc_, arc_], IntegerInterval$TM[ bl_, br_, blc_, brc_], Equal$TM] :=
	integerBoundary["left", al, alc] >= integerBoundary["left", bl, blc] && integerBoundary["right", ar, arc] <= integerBoundary["right", br, brc]
subseteq[ IntegerInterval$TM[ al_, ar_, alc_, arc_], (b:(RationalInterval$TM|RealInterval$TM))[ bl_, br_, blc_, brc_], Equal$TM] :=
	Module[ {l, r,
			all = integerBoundary["left", al, alc],
			arr = integerBoundary[ "right", ar, arc],
			blcc = blc && TrueQ[ isInIntervalDomain[ b, bl]],
			brcc = brc && TrueQ[ isInIntervalDomain[ b, br]]},
		l = If[ MatchQ[ all, _DirectedInfinity] || blcc, GreaterEqual, Greater];
		r = If[ MatchQ[ arr, _DirectedInfinity] || brcc, LessEqual, Less];
		l[ all, bl] && r[ arr, br]
	]
subseteq[ (h:(RationalInterval$TM|RealInterval$TM))[ al_, ar_, alc_, arc_], b_IntegerInterval$TM, Equal$TM] :=
	Switch[ intervalSize[ h, al, ar, alc, arc],
		1, isInInterval[ al, b],
		$Failed, $Failed,
		_, False
	]
subseteq[ RationalInterval$TM[ al_, ar_, alc_, arc_], RationalInterval$TM[ bl_, br_, blc_, brc_], Equal$TM] :=
	Module[ {alcc = If[ alc && isInIntervalDomain[ RationalInterval$TM, al], True, False, $Failed],
			blcc = If[ blc && isInIntervalDomain[ RationalInterval$TM, bl], True, False, $Failed],
			arcc = If[ arc && isInIntervalDomain[ RationalInterval$TM, ar], True, False, $Failed],
			brcc = If[ brc && isInIntervalDomain[ RationalInterval$TM, br], True, False, $Failed]},
		Catch[
			And[
				Switch[ alcc,
					$Failed,
					Switch[ blcc,
						$Failed,
						al >= bl,
						_,
						Which[ al > bl, True, al < bl, False, True, Throw[ $Failed]]
					],
					True,
					Switch[ blcc,
						True,
						al >= bl,
						_,
						al > bl
					],
					False,
					al >= bl
				],
				Switch[ arcc,
					$Failed,
					Switch[ brcc,
						$Failed,
						ar <= br,
						_,
						Which[ ar < br, True, ar > br, False, True, Throw[ $Failed]]
					],
					True,
					Switch[ brcc,
						True,
						ar <= br,
						_,
						ar < br
					],
					False,
					ar <= br
				]
			]
		]
	]
subseteq[ RationalInterval$TM[ al_, ar_, alc_, arc_], RealInterval$TM[ bl_, br_, blc_, brc_], Equal$TM] :=
	Module[ {alcc = If[ alc && isInIntervalDomain[ RationalInterval$TM, al], True, False, $Failed],
			arcc = If[ arc && isInIntervalDomain[ RationalInterval$TM, ar], True, False, $Failed]},
		Catch[
			And[
				If[ blc && isInIntervalDomain[ RealInterval$TM, bl],
					al >= bl,
					Switch[ alcc,
						$Failed,
						Which[ al > bl, True, al < bl, False, True, Throw[ $Failed]],
						True,
						al > bl,
						False,
						al >= bl
					]
				],
				If[ brc && isInIntervalDomain[ RealInterval$TM, br],
					ar <= br,
					Switch[ arcc,
						$Failed,
						Which[ ar < br, True, ar > br, False, True, Throw[ $Failed]],
						True,
						ar < br,
						False,
						ar <= br
					]
				]
			]
		]
	]
subseteq[ RealInterval$TM[ al_, ar_, alc_, arc_], b_RationalInterval$TM, Equal$TM] :=
	Switch[ intervalSize[ RealInterval$TM, al, ar, alc, arc],
		1, isInInterval[ al, b],
		$Failed, $Failed,
		_, False
	]
subseteq[ RealInterval$TM[ al_, ar_, alc_, arc_], RealInterval$TM[ bl_, br_, blc_, brc_], Equal$TM] :=
	Module[ {l = If[ !alc || !isInIntervalDomain[ RealInterval$TM, al] || (blc && isInIntervalDomain[ RealInterval$TM, bl]), GreaterEqual, Greater],
			r = If[ !arc || !isInIntervalDomain[ RealInterval$TM, ar] || (brc && isInIntervalDomain[ RealInterval$TM, br]), LessEqual, Less]},
		l[ al, bl] && r[ ar, br]
	]
	
subseteq[ IntegerQuotientRing$TM[ m_], b_, rel_] := subseteq[ IntegerInterval$TM[ 0, m - 1, True, True], b, rel]
subseteq[ a_, IntegerQuotientRing$TM[ m_], rel_] := subseteq[ a, IntegerInterval$TM[ 0, m - 1, True, True], rel]
subseteq[ IntegerQuotientRingPM$TM[ m_], b_, rel_] := subseteq[ IntegerInterval$TM[ lowerPM[ m], upperPM[ m], True, True], b, rel]
subseteq[ a_, IntegerQuotientRingPM$TM[ m_], rel_] := subseteq[ a, IntegerInterval$TM[ lowerPM[ m], upperPM[ m], True, True], rel]


(* ::Section:: *)
(* Number Domains *)


(* ::Subsection:: *)
(* simplification *)

IntegerInterval$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)] /;
		buiActive["IntegerInterval"] && intervalSize[ IntegerInterval$TM, l, r, lc, rc] === 0 :=
	Set$TM[]
RationalInterval$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)] /;
		buiActive["RationalInterval"] && intervalSize[ RationalInterval$TM, l, r, lc, rc] === 0 :=
	Set$TM[]
RealInterval$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)] /;
		buiActive["RealInterval"] && intervalSize[ RealInterval$TM, l, r, lc, rc] === 0 :=
	Set$TM[]
IntegerQuotientRing$TM[ 0] /; buiActive["IntegerQuotientRing"] :=
	IntegerInterval$TM[ DirectedInfinity[ -1], DirectedInfinity[ 1], False, False] (* Z_0 is isomorphic to Z *)
IntegerQuotientRingPM$TM[ 0] /; buiActive["IntegerQuotientRingPM"] :=
	IntegerInterval$TM[ DirectedInfinity[ -1], DirectedInfinity[ 1], False, False]
	
(* Transform operations called on only one argument (more than two arguments have already been eliminated at the beginning of this file) *)
(* Since domain-subscripted operations are not defined for intervals, we do not need to transform them here *)
Equal$TM[ _?isActiveDomain] /; buiActive["SetEqual"] := True
SubsetEqual$TM[ _?isActiveDomain] /; buiActive["SubsetEqual"] := True
Subset$TM[ _?isActiveDomain] /; buiActive["Subset"] := True
SupersetEqual$TM[ _?isActiveDomain] /; buiActive["SupersetEqual"] := True
Superset$TM[ _?isActiveDomain] /; buiActive["Superset"] := True

Intersection$TM[ a_?isActiveDomain] /; buiActive["Intersection"] := a
Intersection$TM[ a_?isActiveDomain, c__, d_] /; buiActive["Intersection"] :=
	Fold[ Intersection$TM, a, {c, d}]


(* ::Subsection:: *)
(* Equal *)

Tuple$TM /: Equal$TM[ _?isActiveDomain, _Tuple$TM] /; (buiActive["SetEqual"] || buiActive["TupleEqual"]) := False
Tuple$TM /: Equal$TM[ _Tuple$TM, _?isActiveDomain] /; (buiActive["SetEqual"] || buiActive["TupleEqual"]) := False
Tuple$TM /: (op:(SubsetEqual$TM|Subset$TM|SupersetEqual$TM|Superset$TM))[ _?isActiveDomain, _Tuple$TM] /; buiActive[ StringDrop[ SymbolName[ op], -3]] := False
Tuple$TM /: (op:(SubsetEqual$TM|Subset$TM|SupersetEqual$TM|Superset$TM))[ _Tuple$TM, _?isActiveDomain] /; buiActive[ StringDrop[ SymbolName[ op], -3]] := False

Equal$TM[ a_?isActiveDomain, a_] /; buiActive["SetEqual"] := True

Set$TM /: Equal$TM[ a:(h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ al_?isRealOrInf, ar_?isRealOrInf, alc:(True|False), arc:(True|False)],
		b:Set$TM[ e___]] /; buiActive["SetEqual"] && buiActive[StringDrop[SymbolName[h], -3]] :=
	Module[ {rs, subset},
		subset && rs === Length[ b] /;
			And[
				(rs = intervalSize[ h, al, ar, alc, arc]) =!= $Failed,
				MatchQ[ subset = subseteq[ b, a, Equal$TM], True|False]
			]
	]
Set$TM /: Equal$TM[ a_Set$TM, b:(_IntegerInterval$TM|_RationalInterval$TM|_RealInterval$TM)] /; buiActive["SetEqual"] := Equal$TM[ b, a]
Set$TM /: Equal$TM[ _Set$TM, b:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive["SetEqual"] && buiActive[StringDrop[SymbolName[b], -3]] := False
Set$TM /: Equal$TM[ b:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM), _Set$TM] /; buiActive["SetEqual"] && buiActive[StringDrop[SymbolName[b], -3]] := False
Set$TM /: Equal$TM[ IntegerQuotientRing$TM[ m_?isModulus], a_Set$TM] /; buiActive["SetEqual"] && buiActive["IntegerQuotientRing"] :=
	Length[ a] == m && And @@ Map[ (isInteger$TM[ #] && 0 <= # && # < m)&, Hold @@ a]
Set$TM /: Equal$TM[ IntegerQuotientRingPM$TM[ m_?isModulus], a_Set$TM] /; buiActive["SetEqual"] && buiActive["IntegerQuotientRingPM"] :=
	Length[ a] == m && And @@ Map[ (isInteger$TM[ #] && lowerPM[ m] <= # && # <= upperPM[ m])&, Hold @@ a]
Set$TM /: Equal$TM[ a_Set$TM, b:(_IntegerQuotientRing$TM|_IntegerQuotientRingPM$TM)] /; buiActive["SetEqual"] := Equal$TM[ b, a]

Equal$TM[ a_?isActiveDomain, b_?isActiveDomain] /; buiActive["SetEqual"] :=
	Module[ {res},
		res /; (If[ TrueQ[ res = subseteq[ a, b, Equal$TM]],
					res = subseteq[ b, a, Equal$TM]
				];
				MatchQ[ res, True|False])
	]
	
	
(* ::Subsection:: *)
(* SubsetEqual *)

SubsetEqual$TM[ a_?isActiveDomain, a_] /; buiActive["SubsetEqual"] := True

Set$TM /: SubsetEqual$TM[ a_?isActiveDomain, b_Set$TM] /; buiActive["SubsetEqual"] :=
	Module[ {res},
		res /; MatchQ[ res = subseteq[ a, b, Equal$TM], True|False]
	]
Set$TM /: SubsetEqual$TM[ a_Set$TM, b_?isActiveDomain] /; buiActive["SubsetEqual"] :=
	Module[ {res},
		res /; MatchQ[ res = subseteq[ a, b, Equal$TM], True|False]
	]
SubsetEqual$TM[ a_?isActiveDomain, b_?isActiveDomain] /; buiActive["SubsetEqual"] :=
	Module[ {res},
		res /; MatchQ[ res = subseteq[ a, b, Equal$TM], True|False]
	]
	
	
(* ::Subsection:: *)
(* Subset *)

Subset$TM[ a_?isActiveDomain, a_] /; buiActive["Subset"] := False

Set$TM /: Subset$TM[ a_?isActiveDomain, b_Set$TM] /; buiActive["Subset"] :=
	Module[ {res},
		res /; (If[ TrueQ[ res = subseteq[ a, b, Equal$TM]],
					res = !subseteq[ b, a, Equal$TM]
				];
				MatchQ[ res, True|False])
	]
Set$TM /: Subset$TM[ a_Set$TM, b_?isActiveDomain] /; buiActive["Subset"] :=
	Module[ {res},
		res /; (If[ TrueQ[ res = subseteq[ a, b, Equal$TM]],
					res = !subseteq[ b, a, Equal$TM]
				];
				MatchQ[ res, True|False])
	]
Subset$TM[ a_?isActiveDomain, b_?isActiveDomain] /; buiActive["Subset"] :=
	Module[ {res},
		res /; (If[ TrueQ[ res = subseteq[ a, b, Equal$TM]],
					res = !subseteq[ b, a, Equal$TM]
				];
				MatchQ[ res, True|False])
	]
	
	
(* ::Subsection:: *)
(* SupersetEqual *)

SupersetEqual$TM[ a_?isActiveDomain, a_] /; buiActive["SupersetEqual"] := True

Set$TM /: SupersetEqual$TM[ a_?isActiveDomain, b_Set$TM] /; buiActive["SupersetEqual"] :=
	Module[ {res},
		res /; MatchQ[ res = subseteq[ b, a, Equal$TM], True|False]
	]
Set$TM /: SupersetEqual$TM[ a_Set$TM, b_?isActiveDomain] /; buiActive["SupersetEqual"] :=
	Module[ {res},
		res /; MatchQ[ res = subseteq[ b, a, Equal$TM], True|False]
	]
SupersetEqual$TM[ a_?isActiveDomain, b_?isActiveDomain] /; buiActive["SupersetEqual"] :=
	Module[ {res},
		res /; MatchQ[ res = subseteq[ b, a, Equal$TM], True|False]
	]
	
	
(* ::Subsection:: *)
(* Superset *)

Superset$TM[ a_?isActiveDomain, a_] /; buiActive["Superset"] := False

Set$TM /: Superset$TM[ a_?isActiveDomain, b_Set$TM] /; buiActive["Superset"] :=
	Module[ {res},
		res /; (If[ TrueQ[ res = subseteq[ b, a, Equal$TM]],
					res = !subseteq[ a, b, Equal$TM]
				];
				MatchQ[ res, True|False])
	]
Set$TM /: Superset$TM[ a_Set$TM, b_?isActiveDomain] /; buiActive["Superset"] :=
	Module[ {res},
		res /; (If[ TrueQ[ res = subseteq[ b, a, Equal$TM]],
					res = !subseteq[ a, b, Equal$TM]
				];
				MatchQ[ res, True|False])
	]
Superset$TM[ a_?isActiveDomain, b_?isActiveDomain] /; buiActive["Superset"] :=
	Module[ {res},
		res /; (If[ TrueQ[ res = subseteq[ b, a, Equal$TM]],
					res = !subseteq[ a, b, Equal$TM]
				];
				MatchQ[ res, True|False])
	]
	
	
(* ::Subsection:: *)
(* Intersection *)

Intersection$TM[ a_?isActiveDomain, a_] /; buiActive["Intersection"] := a

Set$TM /: Intersection$TM[ a:(h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ _?isRealOrInf, _?isRealOrInf, True|False, True|False], b:Set$TM[ ___]] /;
		buiActive["Intersection"] && buiActive[ StringDrop[ SymbolName[ h], -3]] :=
	Module[ {out = Set$TM[]},
		out /; Catch[
				Scan[
					If[ isInInterval[ #, a],
						AppendTo[ out, #],
					(*else*)
						Null,
					(*else*)
						Throw[ False]
					]&,
					b
				];
				True
			]
	]
Set$TM /: Intersection$TM[ a_Set$TM, b:(_IntegerInterval$TM|_RationalInterval$TM|_RealInterval$TM)] /; buiActive["Intersection"] := Intersection$TM[ b, a]
Set$TM /: Intersection$TM[ \[DoubleStruckCapitalC]$TM, b:Set$TM[ ___]] /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]"] :=
	Module[ {out = Set$TM[]},
		out /; Catch[
				Scan[
					If[ isComplex[ #],
						AppendTo[ out, #],
					(*else*)
						Null,
					(*else*)
						Throw[ False]
					]&,
					b
				];
				True
			]
	]
Set$TM /: Intersection$TM[ b_Set$TM, \[DoubleStruckCapitalC]$TM] /; buiActive["Intersection"] := Intersection$TM[ \[DoubleStruckCapitalC]$TM, b]
Set$TM /: Intersection$TM[ \[DoubleStruckCapitalC]P$TM, b:Set$TM[ ___]] /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]"] :=
	Module[ {out = Set$TM[]},
		out /; Catch[
				Scan[
					If[ isComplexP[ #],
						AppendTo[ out, #],
					(*else*)
						Null,
					(*else*)
						Throw[ False]
					]&,
					b
				];
				True
			]
	]
Set$TM /: Intersection$TM[ b_Set$TM, \[DoubleStruckCapitalC]P$TM] /; buiActive["Intersection"] := Intersection$TM[ \[DoubleStruckCapitalC]P$TM, b]
Set$TM /: Intersection$TM[ IntegerQuotientRing$TM[ m_?isModulus], b_Set$TM] /; buiActive["Intersection"] && buiActive["IntegerQuotientRing"] :=
	Module[ {out = Set$TM[]},
		out /; Catch[
				Scan[
					If[ isInteger[ #] && NonNegative[ #] && # < m,
						AppendTo[ out, #],
					(*else*)
						Null,
					(*else*)
						Throw[ False]
					]&,
					b
				];
				True
			]
	]
Set$TM /: Intersection$TM[ IntegerQuotientRingPM$TM[ m_?isModulus], b_Set$TM] /; buiActive["Intersection"] && buiActive["IntegerQuotientRingPM"] :=
	Module[ {l = lowerPM[ m], u = upperPM[ m], out = Set$TM[]},
		out /; Catch[
				Scan[
					If[ isInteger[ #] && l <= # && # <= u,
						AppendTo[ out, #],
					(*else*)
						Null,
					(*else*)
						Throw[ False]
					]&,
					b
				];
				True
			]
	]
Set$TM /: Intersection$TM[ a_Set$TM, b:(_IntegerQuotientRing$TM|_IntegerQuotientRingPM$TM)] /; buiActive["Intersection"] := Intersection$TM[ b, a]

\[DoubleStruckCapitalC]$TM /: Intersection$TM[ \[DoubleStruckCapitalC]$TM, b:((h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ ___])] :=
	b /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]"] && buiActive[StringDrop[SymbolName[h], -3]]
\[DoubleStruckCapitalC]$TM /: Intersection$TM[ b:((h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ ___]), \[DoubleStruckCapitalC]$TM] :=
	b /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]"] && buiActive[StringDrop[SymbolName[h], -3]]
\[DoubleStruckCapitalC]$TM /: Intersection$TM[ \[DoubleStruckCapitalC]$TM, b:((h:(IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ _])] :=
	b /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]"] && buiActive[StringDrop[SymbolName[h], -3]]
\[DoubleStruckCapitalC]$TM /: Intersection$TM[ b:((h:(IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ _]), \[DoubleStruckCapitalC]$TM] :=
	b /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]"] && buiActive[StringDrop[SymbolName[h], -3]]
\[DoubleStruckCapitalC]P$TM /: Intersection$TM[ \[DoubleStruckCapitalC]P$TM, (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ ___]] :=
	Set$TM[ ] /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]P"] && buiActive[StringDrop[SymbolName[h], -3]]
\[DoubleStruckCapitalC]P$TM /: Intersection$TM[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ ___], \[DoubleStruckCapitalC]P$TM] :=
	Set$TM[ ] /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]P"] && buiActive[StringDrop[SymbolName[h], -3]]
\[DoubleStruckCapitalC]P$TM /: Intersection$TM[ \[DoubleStruckCapitalC]P$TM, b:((h:(IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ _])] :=
	Set$TM[ ] /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]P"] && buiActive[StringDrop[SymbolName[h], -3]]
\[DoubleStruckCapitalC]P$TM /: Intersection$TM[ b:((h:(IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ _]), \[DoubleStruckCapitalC]P$TM] :=
	Set$TM[ ] /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]P"] && buiActive[StringDrop[SymbolName[h], -3]]
	
\[DoubleStruckCapitalC]$TM /: Intersection$TM[ \[DoubleStruckCapitalC]$TM, \[DoubleStruckCapitalC]P$TM] :=
	Set$TM[ ] /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]"] && buiActive["\[DoubleStruckCapitalC]P"]
\[DoubleStruckCapitalC]P$TM /: Intersection$TM[ \[DoubleStruckCapitalC]P$TM, \[DoubleStruckCapitalC]$TM] :=
	Set$TM[ ] /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]P"] && buiActive["\[DoubleStruckCapitalC]"]
		
IntegerInterval$TM /: Intersection$TM[ a:IntegerInterval$TM[ _?isRealOrInf, _?isRealOrInf, True|False, True|False],
		b:(h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ _?isRealOrInf, _?isRealOrInf, True|False, True|False]] /;
			buiActive["Intersection"] && buiActive["IntegerInterval"] && buiActive[StringDrop[SymbolName[h],-3]] :=
	IntegerInterval$TM[ intersectIntervals[ a, b]]
IntegerInterval$TM /: Intersection$TM[ a:(_RationalInterval$TM|_RealInterval$TM), b_IntegerInterval$TM] /; buiActive["Intersection"] := Intersection$TM[ b, a]

RationalInterval$TM /: Intersection$TM[ a:RationalInterval$TM[ _?isRealOrInf, _?isRealOrInf, True|False, True|False],
		b:(h:(RationalInterval$TM|RealInterval$TM))[ _?isRealOrInf, _?isRealOrInf, True|False, True|False]] /;
			buiActive["Intersection"] && buiActive["RationalInterval"] && buiActive[ StringDrop[ SymbolName[ h], -3]] :=
	RationalInterval$TM[ intersectIntervals[ a, b]]
RationalInterval$TM /: Intersection$TM[ a_RealInterval$TM, b_RationalInterval$TM] /; buiActive["Intersection"] := Intersection$TM[ b, a]

RealInterval$TM /: Intersection$TM[ a:RealInterval$TM[ _?isRealOrInf, _?isRealOrInf, True|False, True|False],
		b:RealInterval$TM[ _?isRealOrInf, _?isRealOrInf, True|False, True|False]] /; buiActive["Intersection"] && buiActive["RealInterval"] :=
	RealInterval$TM[ intersectIntervals[ a, b]]
	
IntegerQuotientRing$TM /: Intersection$TM[ IntegerQuotientRing$TM[ m_?isModulus],
		b:(h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ _?isRealOrInf, _?isRealOrInf, True|False, True|False]] /;
			buiActive["Intersection"] && buiActive["IntegerQuotientRing"] && buiActive[ StringDrop[ SymbolName[ h], -3]] :=
	IntegerInterval$TM[ intersectIntervals[ IntegerInterval$TM[ 0, m - 1, True, True], b]]
IntegerQuotientRingPM$TM /: Intersection$TM[ IntegerQuotientRingPM$TM[ m_?isModulus],
		b:(h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ _?isRealOrInf, _?isRealOrInf, True|False, True|False]] /;
			buiActive["Intersection"] && buiActive["IntegerQuotientRingPM"] && buiActive[ StringDrop[ SymbolName[ h], -3]] :=
	IntegerInterval$TM[ intersectIntervals[ IntegerInterval$TM[ lowerPM[ m], upperPM[ m], True, True], b]]
Intersection$TM[ a:(_IntegerInterval$TM|_RationalInterval$TM|_RealInterval$TM), b:(_IntegerQuotientRing$TM|_IntegerQuotientRingPM$TM)] /; buiActive["Intersection"] := Intersection$TM[ b, a]

IntegerQuotientRing$TM /: Intersection$TM[ IntegerQuotientRing$TM[ m1_?isModulus], IntegerQuotientRingPM$TM[ m2_?isModulus]] /;
			buiActive["Intersection"] && buiActive["IntegerQuotientRing"] && buiActive["IntegerQuotientRingPM"] :=
	IntegerInterval$TM[ 0, Min[ m1 - 1, upperPM[ m2]], True, True]
IntegerQuotientRing$TM /: Intersection$TM[ a_IntegerQuotientRingPM$TM, b_IntegerQuotientRing$TM] /; buiActive["Intersection"] := Intersection$TM[ b, a]
	
IntegerQuotientRing$TM /: Intersection$TM[ IntegerQuotientRing$TM[ m1_?isModulus], IntegerQuotientRing$TM[ m2_?isModulus]] /;
			buiActive["Intersection"] && buiActive["IntegerQuotientRing"] :=
	IntegerQuotientRing$TM[ Min[ m1, m2]]
IntegerQuotientRingPM$TM /: Intersection$TM[ IntegerQuotientRingPM$TM[ m1_?isModulus], IntegerQuotientRingPM$TM[ m2_?isModulus]] /;
			buiActive["Intersection"] && buiActive["IntegerQuotientRingPM"] :=
	IntegerQuotientRingPM$TM[ Min[ m1, m2]]


(* ::Subsection:: *)
(* Union *)

IntegerQuotientRing$TM /: Union$TM[ IntegerQuotientRing$TM[ m1_?isModulus], IntegerQuotientRing$TM[ m2_?isModulus]] /;
			buiActive["Union"] && buiActive["IntegerQuotientRing"] :=
	IntegerQuotientRing$TM[ Max[ m1, m2]]
IntegerQuotientRingPM$TM /: Union$TM[ IntegerQuotientRingPM$TM[ m1_?isModulus], IntegerQuotientRingPM$TM[ m2_?isModulus]] /;
			buiActive["Union"] && buiActive["IntegerQuotientRingPM"] :=
	IntegerQuotientRingPM$TM[ Max[ m1, m2]]
	

(* ::Subsection:: *)
(* element *)

\[DoubleStruckCapitalC]$TM /: Element$TM[ p_, \[DoubleStruckCapitalC]$TM] /;
		buiActive["IsElement"] && buiActive["\[DoubleStruckCapitalC]"] :=
	isComplex$TM[ p]
\[DoubleStruckCapitalC]P$TM /: Element$TM[ p_, \[DoubleStruckCapitalC]P$TM] /;
		buiActive["IsElement"] && buiActive["\[DoubleStruckCapitalC]P"] :=
	isComplexP$TM[ p]
Element$TM[ p_, h:(_IntegerInterval$TM|_RationalInterval$TM|_RealInterval$TM)] /;
		buiActive["IsElement"] && buiActive[StringDrop[SymbolName[Head[h]],-3]] :=
	isInInterval[ p, h]
IntegerQuotientRing$TM /: Element$TM[ p_, IntegerQuotientRing$TM[ m_?isModulus]] /;
		buiActive["IntegerQuotientRing"] :=
	isInteger$TM[ p] && 0 <= p && p <= m - 1
IntegerQuotientRingPM$TM /: Element$TM[ p_, IntegerQuotientRingPM$TM[ m_?isModulus]] /;
		buiActive["IntegerQuotientRingPM"] :=
	isInteger$TM[ p] && lowerPM[ m] <= p && p <= upperPM[ m]


(* ::Subsection:: *)
(* cardinality *)

\[DoubleStruckCapitalC]$TM /: BracketingBar$TM[ \[DoubleStruckCapitalC]$TM] /;
		buiActive["Cardinality"] && buiActive["\[DoubleStruckCapitalC]"] :=
	Infinity
\[DoubleStruckCapitalC]P$TM /: BracketingBar$TM[ \[DoubleStruckCapitalC]P$TM] /;
		buiActive["Cardinality"] && buiActive["\[DoubleStruckCapitalC]P"] :=
	Infinity
IntegerQuotientRing$TM /: BracketingBar$TM[ IntegerQuotientRing$TM[ m_?isModulus]] /;
		buiActive["Cardinality"] && buiActive["IntegerQuotientRing"] :=
	m
IntegerQuotientRingPM$TM /: BracketingBar$TM[ IntegerQuotientRingPM$TM[ m_?isModulus]] /;
		buiActive["Cardinality"] && buiActive["IntegerQuotientRingPM"] :=
	m
IntegerInterval$TM /: BracketingBar$TM[ IntegerInterval$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)]] /;
		buiActive["Cardinality"] && buiActive["IntegerInterval"] :=
	intervalSize[ IntegerInterval$TM, l, r, lc, rc]
RationalInterval$TM /: BracketingBar$TM[ RationalInterval$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)]] :=
	Module[ {rs},
		rs /; buiActive["Cardinality"] && buiActive["RationalInterval"] && ((rs = intervalSize[ RationalInterval$TM, l, r, lc, rc]) =!= $Failed)
	]
RealInterval$TM /: BracketingBar$TM[ RealInterval$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)]] /;
		buiActive["Cardinality"] && buiActive["RealInterval"] :=
	intervalSize[ RealInterval$TM, l, r, lc, rc]
	
	
(* ::Subsection:: *)
(* min/max *)

IntegerInterval$TM /: min$TM[ IntegerInterval$TM[ l_?isRealOrInf, _?isRealOrInf, lc:(True|False), True|False]] /;
		buiActive["MinimumElementSet"] && buiActive["IntegerInterval"] && l > -Infinity :=
	integerBoundary[ "left", l, lc]
RationalInterval$TM /: min$TM[ RationalInterval$TM[ l_?isInIntervalDomain[ RationalInterval$TM, #]&, _?isRealOrInf, True, True|False]] /;
		buiActive["MinimumElementSet"] && buiActive["RationalInterval"] :=
	l
RealInterval$TM /: min$TM[ RealInterval$TM[ l_?isRealOrInf, _?isRealOrInf, True, True|False]] /;
		buiActive["MinimumElementSet"] && buiActive["RealInterval"] && l > -Infinity :=
	l
IntegerQuotientRing$TM /: min$TM[ IntegerQuotientRing$TM[ m_?isModulus]] /;
		buiActive["MinimumElementSet"] && buiActive["IntegerQuotientRing"] :=
	0
IntegerQuotientRingPM$TM /: min$TM[ IntegerQuotientRingPM$TM[ m_?isModulus]] /;
		buiActive["MinimumElementSet"] && buiActive["IntegerQuotientRingPM"] :=
	lowerPM[ m]
	
IntegerInterval$TM /: max$TM[ IntegerInterval$TM[ _?isRealOrInf, r_?isRealOrInf, True|False, rc:(True|False)]] /;
		buiActive["MaximumElementSet"] && buiActive["IntegerInterval"] && r < Infinity :=
	integerBoundary[ "right", r, rc]
RationalInterval$TM /: max$TM[ RationalInterval$TM[ _?isRealOrInf, r_?isInIntervalDomain[ RationalInterval$TM, #]&, True|False, True]] /;
		buiActive["MaximumElementSet"] && buiActive["RationalInterval"] :=
	r
RealInterval$TM /: max$TM[ RealInterval$TM[ _?isRealOrInf, r_?isRealOrInf, True|False, True]] /;
		buiActive["MaximumElementSet"] && buiActive["RealInterval"] && r < Infinity :=
	r
IntegerQuotientRing$TM /: max$TM[ IntegerQuotientRing$TM[ m_?isModulus]] /;
		buiActive["MaximumElementSet"] && buiActive["IntegerQuotientRing"] :=
	m - 1
IntegerQuotientRingPM$TM /: max$TM[ IntegerQuotientRingPM$TM[ m_?isModulus]] /;
		buiActive["MaximumElementSet"] && buiActive["IntegerQuotientRingPM"] :=
	upperPM[ m]
	
	
(* ::Subsection:: *)
(* ae *)

IntegerInterval$TM /: \[AE]$TM[ IntegerInterval$TM[ DirectedInfinity[-1], DirectedInfinity[1], True|False, True|False]] /;
		buiActive["AnElement"] && buiActive["IntegerInterval"] :=
	0
IntegerInterval$TM /: \[AE]$TM[ IntegerInterval$TM[ DirectedInfinity[-1], r_?isReal, True|False, rc:(True|False)]] /;
		buiActive["AnElement"] && buiActive["IntegerInterval"] :=
	integerBoundary[ "right", r, rc]
IntegerInterval$TM /: \[AE]$TM[ IntegerInterval$TM[ l_?isReal, _?isRealOrInf, lc:(True|False), True|False]] /;
		buiActive["AnElement"] && buiActive["IntegerInterval"] :=
	integerBoundary[ "left", l, lc]
	
RationalInterval$TM /: \[AE]$TM[ RationalInterval$TM[ DirectedInfinity[-1], DirectedInfinity[1], True|False, True|False]] /;
		buiActive["AnElement"] && buiActive["RationalInterval"] :=
	0
RationalInterval$TM /: \[AE]$TM[ RationalInterval$TM[ DirectedInfinity[-1], r_?isReal, True|False, True|False]] /;
		buiActive["AnElement"] && buiActive["RationalInterval"] :=
	Floor[ r] - 1
RationalInterval$TM /: \[AE]$TM[ RationalInterval$TM[ l_?isReal, DirectedInfinity[1], True|False, True|False]] /;
		buiActive["AnElement"] && buiActive["RationalInterval"] :=
	Ceiling[ l] + 1
RationalInterval$TM /: \[AE]$TM[ RationalInterval$TM[ l_?isRational, r_?isRational, True|False, True|False]] /;
		buiActive["AnElement"] && buiActive["RationalInterval"] :=
	(l + r) / 2
RationalInterval$TM /: \[AE]$TM[ RationalInterval$TM[ l_?isReal, r_?isReal, True|False, True|False]] /;
		buiActive["AnElement"] && buiActive["RationalInterval"] :=
	Module[ {res},
		res /; isRational[ res = Rationalize[ (l + r) / 2, (r - l) / 4]]
	]
	
RealInterval$TM /: \[AE]$TM[ RealInterval$TM[ DirectedInfinity[-1], DirectedInfinity[1], True|False, True|False]] /;
		buiActive["AnElement"] && buiActive["RealInterval"] :=
	0
RealInterval$TM /: \[AE]$TM[ RealInterval$TM[ DirectedInfinity[-1], r_?isReal, True|False, True|False]] /;
		buiActive["AnElement"] && buiActive["RealInterval"] :=
	Floor[ r] - 1
RealInterval$TM /: \[AE]$TM[ RealInterval$TM[ l_?isReal, DirectedInfinity[1], True|False, True|False]] /;
		buiActive["AnElement"] && buiActive["RealInterval"] :=
	Ceiling[ l] + 1
RealInterval$TM /: \[AE]$TM[ RealInterval$TM[ l_?isReal, r_?isReal, True|False, True|False]] /;
		buiActive["AnElement"] && buiActive["RealInterval"] :=
	(l + r) / 2
	
\[DoubleStruckCapitalC]$TM /: \[AE]$TM[ \[DoubleStruckCapitalC]$TM] /;
		buiActive["AnElement"] && buiActive["\[DoubleStruckCapitalC]"] :=
	0
\[DoubleStruckCapitalC]P$TM /: \[AE]$TM[ \[DoubleStruckCapitalC]P$TM] /;
		buiActive["AnElement"] && buiActive["\[DoubleStruckCapitalC]P"] :=
	Tuple$TM[ 0, 0]
	
IntegerQuotientRing$TM /: \[AE]$TM[ IntegerQuotientRing$TM[ m_?isModulus]] /;
		buiActive["AnElement"] && buiActive["IntegerQuotientRing"] :=
	0
IntegerQuotientRingPM$TM /: \[AE]$TM[ IntegerQuotientRingPM$TM[ m_?isModulus]] /;
		buiActive["AnElement"] && buiActive["IntegerQuotientRingPM"] :=
	0


(* ::Subsection:: *)
(* auxiliary functions *)

isActiveDomain[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ _?isRealOrInf, _?isRealOrInf, True|False, True|False]] := buiActive[ StringDrop[ SymbolName[ h], -3]]
isActiveDomain[ (h:(IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ _?isModulus]] := buiActive[ StringDrop[ SymbolName[ h], -3]]
isActiveDomain[ a:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] := buiActive[ StringDrop[ SymbolName[ a], -3]]
isActiveDomain[ _] := False

isInInterval[ p_, (h:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[DirectedInfinity[-1], DirectedInfinity[1], _, _]] :=
	isInIntervalDomain[ h, p]
isInInterval[ p_, (h:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[DirectedInfinity[-1], u_, _, True]] :=
	And[ isInIntervalDomain[ h, p], LessEqual[ p, u]]
isInInterval[ p_, (h:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[DirectedInfinity[-1], u_, _, False]] :=
	And[ isInIntervalDomain[ h, p], Less[ p, u]]
isInInterval[ p_, (h:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[l_, DirectedInfinity[1], True, _]] :=
	And[ isInIntervalDomain[ h, p], GreaterEqual[ p, l]]
isInInterval[ p_, (h:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[l_, DirectedInfinity[1], False, _]] :=
	And[ isInIntervalDomain[ h, p], Greater[ p, l]]
isInInterval[ p_, (h:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[l_, u_, True, True]] :=
	And[ isInIntervalDomain[ h, p], GreaterEqual[ p, l], LessEqual[ p, u]]
isInInterval[ p_, (h:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[l_, u_, False, True]] :=
	And[ isInIntervalDomain[ h, p], Greater[ p, l], LessEqual[ p, u]]
isInInterval[ p_, (h:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[l_, u_, True, False]] :=
	And[ isInIntervalDomain[ h, p], GreaterEqual[ p, l], Less[ p, u]]
isInInterval[ p_, (h:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[l_, u_, False, False]] :=
	And[ isInIntervalDomain[ h, p], Greater[ p, l], Less[ p, u]]

(* The only thing that function "isInIntervalDomain" does is to provide a shortcut, such that one does not have to
	distinguish all the time between the 3 different intervals; "isInIntervalDomain" does the job. *)
isInIntervalDomain[ IntegerInterval$TM, a_] := isInteger$TM[ a]
isInIntervalDomain[ RationalInterval$TM, a_] := isRational$TM[ a]
isInIntervalDomain[ RealInterval$TM, a_] := isReal$TM[ a]

(* isRealOrInf returns True iff its argument is either a real number or real infinity. These are the only
	values that make sense as interval boundaries. *)
isRealOrInf[ _Integer|_Rational|_Real] := True
isRealOrInf[ DirectedInfinity[1|-1]] := True
isRealOrInf[ Pi|E|EulerGamma|GoldenRatio|Degree|Catalan|Khinchin|Glaisher] := True
isRealOrInf[ _] := False

isModulus[ m_] := TrueQ[ isInteger[ m] && Positive[ m]]

(* Since we allow arbitrary real numbers as boundaries, we need to compute the actual integer boundaries
	of the interval, also taking into account open/closed intervals. *)
integerBoundary[ "left", b_, c_] := With[ {bb = Ceiling[ b]}, If[ c || bb > b, bb, bb + 1]]
integerBoundary[ "right", b_, c_] := With[ {bb = Floor[ b]}, If[ c || bb < b, bb, bb - 1]]

(* intervalSize[] returns $Failed if the cardinality of RationalInterval$TM[Catalan, Catalan, True, True]
	should be determined. If Catalan is rational, the cardinality is 1, otherwise it is 0. *)
intervalSize[ IntegerInterval$TM, l_, r_, lc_, rc_] :=
	Module[ {ll = integerBoundary[ "left", l, lc],
			rr = integerBoundary[ "right", r, rc]},
		If[ ll == rr,
			Switch[ ll,
				_DirectedInfinity, 0,
				_, 1
			],
		(*else*)
			Max[ 0, rr - ll + 1]
		]
	]
intervalSize[ ran:(RealInterval$TM|RationalInterval$TM), l_, r_, lc_, rc_] :=
	If[ lc && rc,
		Which[
			l == r, If[ isInIntervalDomain[ ran, l], 1, 0, $Failed],
			l > r, 0,
			True, Infinity
		],
	(*else*)
		If[ l >= r,
			0,
			Infinity
		]
	]

intersectIntervals[ _[ al_, ar_, alc_, arc_], _[ bl_, br_, blc_, brc_]] :=
	Module[ {l = Max[ al, bl], r = Min[ ar, br]},
		Apply[ Sequence, {l, r, (al < l || alc) && (bl < l || blc), (ar > r || arc) && (br > r || brc)}]
	]


(* ::Section:: *)
(* Tuples *)


Tuple$TM /: Insert$TM[ a:Tuple$TM[ ___?isIndividual], p_, q_?isPositionSpec] /; buiActive["Insert"] := Insert[ a, p, q /. Tuple$TM -> List]

(* Delete elements at one or more positions *)
Tuple$TM /: DeleteAt$TM[ a:Tuple$TM[ ___?isIndividual], b_?isPositionSpec] /; buiActive["DeleteAt"] := Delete[ a, b //. Tuple$TM -> List]

DeleteAt$TM[ ReplacePart$TM[ a_, Tuple$TM[ i_, _]], i_] /; buiActive["ReplacePart"] && buiActive["DeleteAt"] :=
	DeleteAt$TM[ a, i]

(* Delete elements of a certain shape. Multiple deletions are not possible, because it would need
	special syntax how to specify multiple shapes. Tuples cannot be used because for this *)
Tuple$TM /: Delete$TM[ a_Tuple$TM?isGround, d__?isGround] /; buiActive["Delete"] := Fold[ DeleteCases[ #1, #2]&, a, {d}]

Tuple$TM /: Equal$TM[ _Tuple$TM, _Set$TM] /; buiActive["SetEqual"] || buiActive["TupleEqual"] := False

Tuple$TM /: Equal$TM[ a_Tuple$TM, a_] /; buiActive["TupleEqual"] := True
Tuple$TM /: Equal$TM[ a_Tuple$TM, b_Tuple$TM] /; buiActive["TupleEqual"] :=
	Module[ {res = (Length[ a] === Length[ b] &&
					Catch[
						MapThread[
							If[ #1 =!= #2,	(* works also for sequence expressions *)
								If[ isIndividual[ #1] && isIndividual[ #2],
									If[ Equal$TM[ #1, #2],
										Null,
									(*else*)
										Throw[ False],
									(*else*)
										Throw[ $Failed]
									],
								(*else*)
									Throw[ $Failed]
								]
							]&,
							{List @@ a, List @@ b}
						];
						True
					]
				)
			},
		res /; MatchQ[ res, True|False]
	]
Tuple$TM /: Annotated$TM[ Equal$TM, SubScript$TM[ dom_]][ a_Tuple$TM, b_Tuple$TM] /; buiActive["TupleEqual"] :=
	Module[ {res = (Length[ a] === Length[ b] &&
					Catch[
						Scan[
							If[ isIndividual[ #1] && isIndividual[ #2],
								If[ DomainOperation$TM[ dom, Equal$TM][ First[ #], Last[ #]],
									Null,
								(*else*)
									Throw[ False],
								(*else*)
									Throw[ $Failed]
								],
							(*else*)
								Throw[ $Failed]
							]&,
							Transpose[ {List @@ a, List @@ b}]
						];
						True
					]
				)
			},
		res /; MatchQ[ res, True|False]
	]

Tuple$TM /: appendElem$TM[ a_Tuple$TM, p_] /; buiActive["appendElem"] := Append[ a, p]
Tuple$TM /: prependElem$TM[ p_, a_Tuple$TM] /; buiActive["prependElem"] := Prepend[ a, p]
Tuple$TM /: joinTuples$TM[ a__Tuple$TM] /; buiActive["joinTuples"] := Join[ a]

Tuple$TM /: elemTuple$TM[ p_, a_Tuple$TM] /; buiActive["elemTuple"] :=
	Module[ {res},
		res /; (res = elementOf[ p, a, Equal$TM]; MatchQ[ res, True|False])
	]
Tuple$TM /: Annotated$TM[ elemTuple$TM, SubScript$TM[ dom_]][ p_, a_Tuple$TM] /; buiActive["elemTuple"] :=
	Module[ {res},
		res /; (res = elementOf[ p, a, DomainOperation$TM[ dom, Equal$TM]]; MatchQ[ res, True|False])
	]

Tuple$TM /: max$TM[ Tuple$TM[ e__]] /; buiActive["Max"] :=
	Module[ {res = applyFlexOperation[ DeleteDuplicates[ Hold[ e]], max$TM, Max, $Failed, DirectedInfinity[ 1]]},
		(res /. Max -> max$TM /. {m:(max$TM[ _Tuple$TM]) :> m, max$TM[ x___] :> max$TM[ Tuple$TM[ x]]}) /; res =!= $Failed
	]
Tuple$TM /: Annotated$TM[ max$TM, SubScript$TM[ _]][ Tuple$TM[ e_?isIndividual]] /; buiActive["Max"] := e
Tuple$TM /: Annotated$TM[ max$TM, s:SubScript$TM[ ord_]][ Tuple$TM[ e__]] /; buiActive["Max"] :=
	Module[ {res},
		Annotated$TM[ max$TM, s][ Tuple$TM @@ res] /; (res = max[ {e}, ord]; Length[ res] < Length[ Hold[ e]])
	]
Tuple$TM /: min$TM[ Tuple$TM[ e__]] /; buiActive["Min"] :=
	Module[ {res = applyFlexOperation[ DeleteDuplicates[ Hold[ e]], min$TM, Min, $Failed, DirectedInfinity[ -1]]},
		(res /. Min -> min$TM /. {m:(min$TM[ _Tuple$TM]) :> m, min$TM[ x___] :> min$TM[ Tuple$TM[ x]]}) /; res =!= $Failed
	]
Tuple$TM /: Annotated$TM[ min$TM, SubScript$TM[ _]][ Tuple$TM[ e_?isIndividual]] /; buiActive["Min"] := e
Tuple$TM /: Annotated$TM[ min$TM, s:SubScript$TM[ ord_]][ Tuple$TM[ e__]] /; buiActive["Min"] :=
	Module[ {res},
		Annotated$TM[ min$TM, s][ Tuple$TM @@ res] /; (res = min[ {e}, ord]; Length[ res] < Length[ Hold[ e]])
	]

Tuple$TM /: BracketingBar$TM[ a:Tuple$TM[ ___?isIndividual]] /; buiActive["Length"] := Length[ a]

Tuple$TM /: ReplacePart$TM[ a:Tuple$TM[ ___?isIndividual], p:Tuple$TM[ _?isPositionSpec, _]..] /; buiActive["ReplacePart"] :=
	ReplacePart[ a, MapAt[ # /. {Tuple$TM -> List}&, Replace[ {p}, Tuple$TM[ l_, r_] :> Rule[ l, r], {1}], Table[ {i, 1}, {i, Length[ {p}]}]]]

Tuple$TM /: Replace$TM[ a_Tuple$TM?isGround, s:Tuple$TM[ _?isGround, _]..] /; buiActive["Replace"] :=
	Fold[ ReplaceAll, a, Replace[ {s}, Tuple$TM[ l_, r_] :> Rule[ l, r], {1}]]

Tuple$TM /: Subscript$TM[ a_Tuple$TM, p__Integer] /; buiActive["Subscript"] := Subscript$TM[ a, Tuple$TM[ p]]
Tuple$TM /: Subscript$TM[ Tuple$TM[ a___?isIndividual], p_?isPositionSpec] /; buiActive["Subscript"] :=
	ReleaseHold[ Extract[ Hold[ a] /. List -> List$dummy, p /. Tuple$TM -> List, Hold] /. {List -> Tuple$TM, List$dummy -> List}]
	(* The expression must not be evaluated while we have "List$dummy" instead of "List". *)

Subscript$TM[ ReplacePart$TM[ a_, Tuple$TM[ i_, new_]], i_] /; buiActive["ReplacePart"] && buiActive["Subscript"] := new
Subscript$TM[ ReplacePart$TM[ a_, Tuple$TM[ i_, _]], j_] /; buiActive["ReplacePart"] && buiActive["Subscript"] := Subscript$TM[ a, j]

isPositionSpec[ 0] := False	(* The head of an expression must not be accessible *)
isPositionSpec[ _Integer] := True
isPositionSpec[ Tuple$TM[ p__]] := And @@ Map[ isPositionSpec, {p}]
isPositionSpec[ _] := False
isPositionSpec[ args___] := unexpected[ isPositionSpec, {args}]



(* ::Section:: *)
(* Data Types *)

isInteger$TM[ a_] /; buiActive["isInteger"] :=
	Module[ {res},
		res /; !MatchQ[ res = isInteger[ a], _isInteger]
	]
isRational$TM[ a_] /; buiActive["isRational"] :=
	Module[ {res},
		res /; !MatchQ[ res = isRational[ a], _isRational]
	]
isReal$TM[ a_] /; buiActive["isReal"] :=
	Module[ {res},
		res /; !MatchQ[ res = isReal[ a], _isReal]
	]
isComplex$TM[ a_] /; buiActive["isComplex"] :=
	Module[ {res},
		res /; !MatchQ[ res = isComplex[ a], _isComplex]
	]
isComplexP$TM[ a_] /; buiActive["isComplexP"] :=
	Module[ {res},
		res /; !MatchQ[ res = isComplexP[ a], _isComplexP]
	]
isSet$TM[ a_] /; buiActive["isSet"] :=
	Module[ {res},
		res /; !MatchQ[ res = isSet[ a], _isSet]
	]
isTuple$TM[ a_] /; buiActive["isTuple"] :=
	Module[ {res},
		res /; !MatchQ[ res = isTuple[ a], _isTuple]
	]


isInteger[ _Integer] := True
isInteger[ _Rational|_Real|_Complex|_DirectedInfinity] := False
isInteger[ _Set$TM|_Tuple$TM] := False
isInteger[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___]] /; buiActive[StringDrop[SymbolName[h],-3]] := False
isInteger[ h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive[StringDrop[SymbolName[h],-3]] := False
isInteger[ Indeterminate|True|False|I|Pi|E|Infinity|Degree|EulerGamma|GoldenRatio|Catalan|Khinchin|Glaisher] := False

isRational[ _Integer|_Rational] := True
isRational[ _Real|_Complex|_DirectedInfinity] := False
isRational[ _Set$TM|_Tuple$TM] := False
isRational[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___]] /; buiActive[StringDrop[SymbolName[h],-3]] := False
isRational[ h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive[StringDrop[SymbolName[h],-3]] := False
(* it is not known whether Catalan is rational, therefore we leave "isRational[Catalan]" unevaluated *)
isRational[ Indeterminate|True|False|I|Pi|E|Infinity|Degree|EulerGamma|GoldenRatio|Khinchin|Glaisher] := False

isReal[ _Integer|_Rational|_Real] := True
isReal[ Pi|Degree|GoldenRatio|E|EulerGamma|Catalan|Khinchin|Glaisher] := True
isReal[ _Complex|_DirectedInfinity] := False
isReal[ _Set$TM|_Tuple$TM] := False
isReal[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___]] /; buiActive[StringDrop[SymbolName[h],-3]] := False
isReal[ h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive[StringDrop[SymbolName[h],-3]] := False
isReal[ Indeterminate|True|False|I|Infinity] := False

isComplex[ _Integer|_Rational|_Real|_Complex] := True
isComplex[ I|Pi|Degree|GoldenRatio|E|EulerGamma|Catalan|Khinchin|Glaisher] := True
isComplex[ _Set$TM|_Tuple$TM|_DirectedInfinity] := False
isComplex[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___]] /; buiActive[StringDrop[SymbolName[h],-3]] := False
isComplex[ h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive[StringDrop[SymbolName[h],-3]] := False
isComplex[ Indeterminate|True|False|Infinity] := False

isComplexP[ Tuple$TM[ a_, b_]] := isReal$TM[ a] && isReal$TM[ b] && a >= 0
isComplexP[ _Integer|_Rational|_Real|_Complex|_Set$TM|_Tuple$TM|_DirectedInfinity] := False
isComplexP[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___]] /; buiActive[StringDrop[SymbolName[h],-3]] := False
isComplexP[ h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive[StringDrop[SymbolName[h],-3]] := False
isComplexP[ Indeterminate|True|False|I|Pi|E|Infinity|Degree|EulerGamma|GoldenRatio|Catalan|Khinchin|Glaisher] := False

isSet[ _Set$TM] := True
isSet[ _Integer|_Rational|_Real|_Complex|_DirectedInfinity] := False
isSet[ _Tuple$TM] := False
isSet[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___]] /; buiActive[StringDrop[SymbolName[h],-3]] := True
isSet[ h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive[StringDrop[SymbolName[h],-3]] := True
isSet[ Indeterminate|True|False|I|Pi|E|Infinity|Degree|EulerGamma|GoldenRatio|Catalan|Khinchin|Glaisher] := False

isTuple[ _Tuple$TM] := True
isTuple[ _Integer|_Rational|_Real|_Complex|_DirectedInfinity] := False
isTuple[ _Set$TM] := False
isTuple[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___]] /; buiActive[StringDrop[SymbolName[h],-3]] := False
isTuple[ h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive[StringDrop[SymbolName[h],-3]] := False
isTuple[ Indeterminate|True|False|I|Pi|E|Infinity|Degree|EulerGamma|GoldenRatio|Catalan|Khinchin|Glaisher] := False


(* ::Section:: *)
(* Mathematica programming constructs *)


(* In a "Theorema program", sets and Mathematica lists (as in Module, Do, ...) may be mixed. Also, there is "=" assignment as opposed
   to "=" as equality in standard Theorema language.
   Solution: we write a program inside "Program", and the preprocessor renames symbols differently inside Program, i.e.
   Set -> Assign$TM (instead of Equal), List -> List$TM
   When executing the programming constructs, replace List$TM by {} where interpretation as Mathematica lists is desired.
   *)
   
SetAttributes[ Module$TM, HoldAll]
Module$TM[ l_[v___], body_] /; buiActive["Module"] := Apply[ Module, Hold[ {v}, body]]

SetAttributes[ Do$TM, HoldAll]
Do$TM[ body_, l_[v___]] /; buiActive["Do"] := Apply[ Do, Hold[ body, {v}]]

SetAttributes[ Piecewise$TM, HoldAll]
Piecewise$TM[ Tuple$TM[ Tuple$TM[ expr_, cond_], rest___Tuple$TM]] :=
	Module[ {c},
		If[ c, expr, Piecewise$TM[ Tuple$TM[ rest]]] /; (buiActive[ "CaseDistinction"] && (c = cond; (TrueQ[ c] && isIndividual[ HoldComplete[ expr]]) || c === False))
	]


(* We assume that all lists not treated by the above constructs should in fact be sets *)
SetAttributes[ List$TM, HoldAll]
List$TM[ l___] := Set$TM[l]

cleanupComputation[]
    
End[]
EndPackage[]
