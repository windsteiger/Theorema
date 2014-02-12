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
(* Arithmetic *)

(* "buiActiveArithmetic" extends "buiActive" such that the activation of "Subtract" and "Divide" can also
	be determined in one stroke. *)
buiActiveArithmetic["Subtract"] := buiActive["Plus"] && buiActive["Minus"]
buiActiveArithmetic["Divide"] := buiActive["Times"] && (buiActive["MultInverse"] || buiActive["Power"])
buiActiveArithmetic[s_String] := buiActive[s]

(* "buiActivePower" determines whether "Power" is activated for the given exponent. *)
buiActivePower[-1] := buiActive["MultInverse"] || buiActive["Power"]
buiActivePower[_] := buiActive["Power"]

   
Plus$TM[ a___] /; buiActive["Plus"] := Plus[ a]
Minus$TM[ a_] /; buiActive["Minus"] := Minus[ a]
Subtract$TM[ a_, b_] /; buiActiveArithmetic["Subtract"] := Subtract[ a, b] (* "Subtract" requires exactly 2 arguments. *)
Times$TM[ a___] /; buiActive["Times"] := Times[ a]
Divide$TM[ a_, b_] /; buiActiveArithmetic["Divide"] := Divide[ a, b] (* "Divide" requires exactly 2 arguments. *)
Power$TM[ a_, b_] /; buiActivePower[ b] := Power[ a, b]
Radical$TM[ a_, b_] /; buiActive["Radical"] := Power[ a, 1/b]
Factorial$TM[ a_] /; buiActive["Factorial"] := a!
Equal$TM[ a_, b_] /; buiActive["Equal"] := a == b
Less$TM[ a__] /; buiActive["Less"] := Less[ a]
LessEqual$TM[ a__] /; buiActive["LessEqual"] := LessEqual[ a]
Greater$TM[ a__] /; buiActive["Greater"] := Greater[ a]
GreaterEqual$TM[ a__] /; buiActive["GreaterEqual"] := GreaterEqual[ a]
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

(* amaletzk: Although the following definitions do exactly the same thing (only that they are defined for the different
	intervals), I think it is not possible to only give 1 definition dealing with all of those intervals at once
	(alternatives ("|") unfortunately don't work in this case). *)
	
(* Note that we have to treat the case "Power[a, b]" differently, since 'b' does not have to be in the domain.
	Same for "Radical[a, b]". *)
(dom_IntegerInterval$TM)[Power$TM][ a_, b_] /; buiActive["IntegerInterval"] && buiActivePower[ b] && isInInterval[ a, dom] :=
	Module[ {out},
		out /; (out = Power[ a, b]; isInInterval[ out, dom])
	]
(dom_IntegerInterval$TM)[Radical$TM][ a_, b_] /; buiActive["IntegerInterval"] && buiActive["Radical"] && isInInterval[ a, dom] :=
	Module[ {out},
		out /; (out = Power[ a, Power[ b, -1]]; isInInterval[ out, dom])
	]
(dom_IntegerInterval$TM)[op_Symbol][ a___] /; buiActive["IntegerInterval"] && isValidArgNum[ op, Length[{a}]] && Apply[ And, Map[ isInInterval[ #, dom]&, Hold[ a]]] :=
	Module[ {out, opShortName, opShort},
		out /; And[
					opShortName = StringDrop[ SymbolName[ op], -3]; buiActiveArithmetic[ opShortName],
					opShort = ToExpression[ opShortName]; out = opShort[ a]; isInInterval[ out, dom]
				  ]
	]
	
(dom_RationalInterval$TM)[Power$TM][ a_, b_] /; buiActive["RationalInterval"] && buiActivePower[ b] && isInInterval[ a, dom] :=
	Module[ {out},
		out /; (out = Power[ a, b]; isInInterval[ out, dom])
	]
(dom_RationalInterval$TM)[Radical$TM][ a_, b_] /; buiActive["RationalInterval"] && buiActive["Radical"] && isInInterval[ a, dom] :=
	Module[ {out},
		out /; (out = Power[ a, Power[ b, -1]]; isInInterval[ out, dom])
	]
(dom_RationalInterval$TM)[op_Symbol][ a___] /; buiActive["RationalInterval"] && isValidArgNum[ op, Length[{a}]] && Apply[ And, Map[ isInInterval[ #, dom]&, Hold[ a]]] :=
	Module[ {out, opShortName, opShort},
		out /; And[
					opShortName = StringDrop[ SymbolName[ op], -3]; buiActiveArithmetic[ opShortName],
					opShort = ToExpression[ opShortName]; out = opShort[ a]; isInInterval[ out, dom]
				  ]
	]
	
(dom_RealInterval$TM)[Power$TM][ a_, b_] /; buiActive["RealInterval"] && buiActivePower[ b] && isInInterval[ a, dom] :=
	Module[ {out},
		out /; (out = Power[ a, b]; isInInterval[ out, dom])
	]
(dom_RealInterval$TM)[Radical$TM][ a_, b_] /; buiActive["RealInterval"] && buiActive["Radical"] && isInInterval[ a, dom] :=
	Module[ {out},
		out /; (out = Power[ a, Power[ b, -1]]; isInInterval[ out, dom])
	]
(dom_RealInterval$TM)[op_Symbol][ a___] /; buiActive["RealInterval"] && isValidArgNum[ op, Length[{a}]] && Apply[ And, Map[ isInInterval[ #, dom]&, Hold[ a]]] :=
	Module[ {out, opShortName, opShort},
		out /; And[
					opShortName = StringDrop[ SymbolName[ op], -3]; buiActiveArithmetic[ opShortName],
					opShort = ToExpression[ opShortName]; out = opShort[ a]; isInInterval[ out, dom]
				  ]
	]

\[DoubleStruckCapitalC]$TM[Power$TM][ a_, b_] /; buiActive["\[DoubleStruckCapitalC]"] && buiActivePower[ b] && isComplex[ a] :=
	Module[ {out},
		out /; (out = Power[ a, b]; isComplex[ out])
	]
\[DoubleStruckCapitalC]$TM[Radical$TM][ a_, b_] /; buiActive["\[DoubleStruckCapitalC]"] && buiActive["Radical"] && isComplex[ a] :=
	Module[ {out},
		out /; (out = Power[ a, Power[ b, -1]]; isComplex[ out])
	]
\[DoubleStruckCapitalC]$TM[op_Symbol][ a___] /; buiActive["\[DoubleStruckCapitalC]"] && isValidArgNum[ op, Length[{a}]] && Apply[ And, Map[ isComplex, Hold[ a]]] :=
	Module[ {out, opShortName, opShort},
		out /; And[
					opShortName = StringDrop[ SymbolName[ op], -3]; buiActiveArithmetic[ opShortName],
					opShort = ToExpression[ opShortName]; out = opShort[ a]; isComplex[ out]
				  ]
	]
	
\[DoubleStruckCapitalC]P$TM[Radical$TM][ a_Tuple$TM, b:Tuple$TM[ _?Positive, _]] /; buiActive["\[DoubleStruckCapitalC]P"] && buiActive["Radical"] && isComplexP[ a] && isComplexP[ b] :=
	Module[ {out},
		out /; (out = polarPower[ a, polarPower[ b, -1]]; isComplexP[ out])
	]
\[DoubleStruckCapitalC]P$TM[Radical$TM][ a:Tuple$TM[ r_, phi_], b_] /; buiActive["\[DoubleStruckCapitalC]P"] && buiActive["Radical"] && isComplexP[ a] :=
	Module[ {out},
		out /; (out = polarPower[ a, Power[ b, -1]]; isComplexP[ out])
	]
(* We implement some operations on polar-complexes separately because of efficiency. *)
\[DoubleStruckCapitalC]P$TM[Minus$TM][ a:Tuple$TM[ r_, phi_]] /; buiActive["\[DoubleStruckCapitalC]P"] && buiActive["Minus"] && isComplexP[ a] :=
	Tuple$TM[ r, If[ phi >= Pi, phi - Pi, phi + Pi]]
\[DoubleStruckCapitalC]P$TM[Times$TM][ a:Tuple$TM[ ra_, phia_], b:Tuple$TM[ rb_, phib_]] /; buiActive["\[DoubleStruckCapitalC]P"] && buiActive["Times"] && isComplexP[ a] && isComplexP[ b] :=
	Tuple$TM[ ra * rb, phia + phib]
\[DoubleStruckCapitalC]P$TM[Divide$TM][ a:Tuple$TM[ ra_, phia_], b:Tuple$TM[ rb_?Positive, phib_]] /; buiActive["\[DoubleStruckCapitalC]P"] && buiActiveArithmetic["Divide"] && isComplexP[ a] && isComplexP[ b] :=
	Tuple$TM[ ra / rb, phia - phib]
\[DoubleStruckCapitalC]P$TM[Power$TM][ a_Tuple$TM, b_Tuple$TM] /; buiActive["\[DoubleStruckCapitalC]P"] && buiActive["Power"] && isComplexP[ a] && isComplexP[ b] :=
	Module[ {out},
		out /; (out = polarPower[ a, b]; isComplexP[ out])
	]
\[DoubleStruckCapitalC]P$TM[Power$TM][ a:Tuple$TM[ r_, phi_], b_] /; buiActive["\[DoubleStruckCapitalC]P"] && buiActivePower[ b] && isComplexP[ a] :=
	Module[ {out},
		out /; (out = Tuple$TM[ Power[ r, b], phi * b]; isComplexP[ out])
	]
\[DoubleStruckCapitalC]P$TM[op_Symbol][ a___Tuple$TM] /; buiActive["\[DoubleStruckCapitalC]P"] && isValidArgNum[ op, Length[{a}]] && Apply[ And, Map[ isComplexP, Hold[ a]]] :=
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
	
IntegerQuotientRing$TM[ m_?isModulus][Divide$TM][ a_?isInteger, b_?isInteger] /; buiActive["IntegerQuotientRing"] && buiActive["Radical"] && NonNegative[ a] && a < m && Positive[ b] && b < m:=
	Module[ {gcd, qr},
		Mod[ First[ qr] * gcd[[2, 1]], m] /; (gcd = ExtendedGCD[ b, m]; qr = QuotientRemainder[ a, First[ gcd]]; Last[ qr] === 0)
	]
(* We use "PowerMod" rather than "Mod[Power[..]]", because it is much more efficient
	(according to Mathematica's documentation center). *)
IntegerQuotientRing$TM[ m_?isModulus][Radical$TM][ a_?isInteger, b_] /; buiActive["IntegerQuotientRing"] && buiActive["Radical"] && NonNegative[ a] && a < m :=
	Module[ {out},
		out /; Quiet[ Check[ out = PowerMod[ a, Power[ b, -1], m]; True, False]]
	]
IntegerQuotientRing$TM[ m_?isModulus][Power$TM][ a_?isInteger, b_] /; buiActive["IntegerQuotientRing"] && buiActivePower[ b] && NonNegative[ a] && a < m :=
	Module[ {out},
		out /; Quiet[ Check[ out = PowerMod[ a, b, m]; True, False]]
	]
IntegerQuotientRing$TM[ m_?isModulus][op_Symbol][ a___?isInteger] /; buiActive["IntegerQuotientRing"] && isValidArgNum[ op, Length[{a}]] && Apply[ And, Map[ (NonNegative[#] && # < m)&, Hold[ a]]] :=
	Module[ {out, opShortName, opShort},
		Mod[ out, m] /; And[
						opShortName = StringDrop[ SymbolName[ op], -3]; buiActiveArithmetic[ opShortName],
						opShort = ToExpression[ opShortName]; out = opShort[ a]; isInteger[ out]
					]
	]
	
IntegerQuotientRingPM$TM[ m_?isModulus][Divide$TM][ a_?isInteger, b_?isInteger] /; buiActive["IntegerQuotientRingPM"] && buiActive["Radical"] && lowerPM[ m] <= a <= upperPM[ m] && lowerPM[ m] <= b <= upperPM[ m] :=
	Module[ {gcd, qr},
		representPM[ First[ qr] * gcd[[2, 1]], m] /; (gcd = ExtendedGCD[ b, m]; qr = QuotientRemainder[ a, First[ gcd]]; Last[ qr] === 0)
	]
(* We use "PowerMod" rather than "Mod[Power[..]]", because it is much more efficient
	(according to Mathematica's documentation center). *)
IntegerQuotientRingPM$TM[ m_?isModulus][Radical$TM][ a_?isInteger, b_] /; buiActive["IntegerQuotientRingPM"] && buiActive["Radical"] && lowerPM[ m] <= a <= upperPM[ m] :=
	Module[ {out},
		representPM[ out, m] /; Quiet[ Check[ out = PowerMod[ a, Power[ b, -1], m]; True, False]]
	]
IntegerQuotientRingPM$TM[ m_?isModulus][Power$TM][ a_?isInteger, b_] /; buiActive["IntegerQuotientRingPM"] && buiActivePower[ b] && lowerPM[ m] <= a <= upperPM[ m] :=
	Module[ {out},
		representPM[ out, m] /; Quiet[ Check[ out = PowerMod[ a, b, m]; True, False]]
	]
IntegerQuotientRingPM$TM[ m_?isModulus][op_Symbol][ a___?isInteger] /; buiActive["IntegerQuotientRingPM"] && isValidArgNum[ op, Length[{a}]] :=
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

(* Although the following definitions do exactly the same thing (only that they are defined for the different
	intervals), I think it is not possible to only give 1 definition dealing with all of those intervals at once
	(alternatives ("|") unfortunately don't work). *)
(dom_IntegerInterval$TM)[rel_Symbol?isBinaryRelation][ a_, b_] /; buiActive["IntegerInterval"] && isInInterval[ a, dom] && isInInterval[ b, dom] :=
	Module[ {relShortName, relShort},
		(relShort = ToExpression[ relShortName];
		relShort[ a, b]) /; (relShortName = StringDrop[ SymbolName[ rel], -3]; buiActive[ relShortName])
	]
(dom_RationalInterval$TM)[rel_Symbol?isBinaryRelation][ a_, b_] /; buiActive["RationalInterval"] && isInInterval[ a, dom] && isInInterval[ b, dom] :=
	Module[ {relShortName, relShort},
		(relShort = ToExpression[ relShortName];
		relShort[ a, b]) /; (relShortName = StringDrop[ SymbolName[ rel], -3]; buiActive[ relShortName])
	]
(dom_RealInterval$TM)[rel_Symbol?isBinaryRelation][ a_, b_] /; buiActive["RealInterval"] && isInInterval[ a, dom] && isInInterval[ b, dom] :=
	Module[ {relShortName, relShort},
		(relShort = ToExpression[ relShortName];
		relShort[ a, b]) /; (relShortName = StringDrop[ SymbolName[ rel], -3]; buiActive[ relShortName])
	]
(* The only relation that makes sense for complex numbers is equality, since no meaningful order relations
	are defined (give error by Mathematica). *)
\[DoubleStruckCapitalC]$TM[Equal$TM][ a_, b_] /; buiActive["\[DoubleStruckCapitalC]"] && buiActive["Equal"] && isComplex[ a] && isComplex[ b] :=
	a == b
\[DoubleStruckCapitalC]P$TM[Equal$TM][ a:Tuple$TM[ ra_, phia_], b:Tuple$TM[ rb_, phib_]] /; buiActive["\[DoubleStruckCapitalC]P"] && buiActive["Equal"] && isComplexP[ a] && isComplexP[ b] :=
	ra == rb && (ra == 0 || EvenQ[ (phia - phib) / Pi])
(* The only relation that makes sense for quotient rings is equality. *)
IntegerQuotientRing$TM[ m_?isModulus][Equal$TM][ a_, b_] /; buiActive["IntegerQuotientRing"] && buiActive["Equal"] && NonNegative[ a] && a < m && NonNegative[ b] && b < m :=
	a == b
IntegerQuotientRingPM$TM[ m_?isModulus][Equal$TM][ a_, b_] /; buiActive["IntegerQuotientRingPM"] && buiActive["Equal"] && lowerPM[ m] <= a <= upperPM[ m] && lowerPM[ m] <= b <= upperPM[ m] :=
	a == b



(* ::Section:: *)
(* Ring Constants/Operations *)

(dom_IntegerInterval$TM)[0] /; buiActive["IntegerInterval"] && isInInterval[ 0, dom] := 0
(dom_RationalInterval$TM)[0] /; buiActive["RationalInterval"] && isInInterval[ 0, dom] := 0
(dom_RealInterval$TM)[0] /; buiActive["RealInterval"] && isInInterval[ 0, dom] := 0
\[DoubleStruckCapitalC]$TM[0] /; buiActive["\[DoubleStruckCapitalC]"] := 0
\[DoubleStruckCapitalC]P$TM[0] /; buiActive["\[DoubleStruckCapitalC]P"] := Tuple$TM[0, 0]
IntegerQuotientRing$TM[ m_?isModulus][0] /; buiActive["IntegerQuotientRing"] := 0
IntegerQuotientRingPM$TM[ m_?isModulus][0] /; buiActive["IntegerQuotientRingPM"] := 0

(dom_IntegerInterval$TM)[1] /; buiActive["IntegerInterval"] && isInInterval[ 1, dom] := 1
(dom_RationalInterval$TM)[1] /; buiActive["RationalInterval"] && isInInterval[ 1, dom] := 1
(dom_RealInterval$TM)[1] /; buiActive["RealInterval"] && isInInterval[ 1, dom] := 1
\[DoubleStruckCapitalC]$TM[1] /; buiActive["\[DoubleStruckCapitalC]"] := 1
\[DoubleStruckCapitalC]P$TM[1] /; buiActive["\[DoubleStruckCapitalC]P"] := Tuple$TM[1, 0]
IntegerQuotientRing$TM[ m_?isModulus][1] /; buiActive["IntegerQuotientRing"] && m > 1 := 1
IntegerQuotientRingPM$TM[ m_?isModulus][1] /; buiActive["IntegerQuotientRingPM"] && m > 1 := 1

(dom_IntegerInterval$TM)[Element$TM][ a_] /; buiActive["IntegerInterval"] := isInInterval[ a, dom]
(dom_RationalInterval$TM)[Element$TM][ a_] /; buiActive["RationalInterval"] := isInInterval[ a, dom]
(dom_RealInterval$TM)[Element$TM][ a_] /; buiActive["RealInterval"] := isInInterval[ a, dom]
\[DoubleStruckCapitalC]$TM[Element$TM][ a_] /; buiActive["\[DoubleStruckCapitalC]"] := isComplex[ a]
\[DoubleStruckCapitalC]P$TM[Element$TM][ a_] /; buiActive["\[DoubleStruckCapitalC]P"] := isComplexP[ a]
IntegerQuotientRing$TM[ m_?isModulus][Element$TM][ a_] /; buiActive["IntegerQuotientRing"] := isInteger[ a] && 0 <= a && a <= m-1
IntegerQuotientRingPM$TM[ m_?isModulus][Element$TM][ a_] /; buiActive["IntegerQuotientRingPM"] := isInteger[ a] && lowerPM[ m] <= a && a <= upperPM[ m]



(* ::Section:: *)
(* Logic *)


SetAttributes[ {And$TM, Or$TM}, HoldAll]
Not$TM[ a_] /; buiActive["Not"] := Not[ a]
And$TM[ pre___, a_, mid___, a_, post___] /; buiActive["And"] := And$TM[ pre, a, mid, post]
And$TM[ a___] /; buiActive["And"] := And[ a]
Or$TM[ pre___, a_, mid___, a_, post___] /; buiActive["Or"] := Or$TM[ pre, a, mid, post]
Or$TM[ a___] /; buiActive["Or"] := Or[ a]
Implies$TM[ a__] /; buiActive["Implies"] := Implies[ a]
Iff$TM[ a__] /; buiActive["Iff"] := Equivalent[ a]
Componentwise$TM[ P_, args___] /; buiActive["Componentwise"] := Apply[ And, Map[ P, Hold[args]]]

(* We replace the free variables one after the other, because some might depend on others, and a
	single "substitueFree" doesn't work properly then. This could also be good for global abbreviations ... *)
SetAttributes[ Abbrev$TM, HoldAll]
Abbrev$TM[ RNG$[ f_ABBRVRNG$, r__ABBRVRNG$], expr_] /; buiActive["Let"] :=
	Abbrev$TM[ RNG$[ f], Abbrev$TM[ RNG$[ r], expr]]
Abbrev$TM[ rng:RNG$[ ABBRVRNG$[ l_, r_]], expr_] /; buiActive["Let"] :=
	ReleaseHold[ substituteFree[ Hold[ expr], {l -> r}]]

rangeToIterator[ SETRNG$[ x_, A_Set$TM]] := { x, Apply[ List, A]}
rangeToIterator[ 
  STEPRNG$[ x_, l_Integer, h_Integer, s_Integer]] := {x, l, h, s}
rangeToIterator[ _] := $Failed
rangeToIterator[ args___] := unexpected[ rangeToIterator, {args}]

ClearAll[ Forall$TM, Exists$TM, SequenceOf$TM, SumOf$TM, ProductOf$TM,
	SetOf$TM, TupleOf$TM, MaximumOf$TM, MinimumOf$TM, UnionOf$TM, IntersectionOf$TM]
Scan[ SetAttributes[ #, HoldRest] &, {Forall$TM, Exists$TM, 
  SequenceOf$TM, SumOf$TM, ProductOf$TM, SetOf$TM, TupleOf$TM, MaximumOf$TM, MinimumOf$TM,
  UnionOf$TM, IntersectionOf$TM}]
Scan[ SetAttributes[ #, HoldFirst] &, {SETRNG$, STEPRNG$}]

Forall$TM[ RNG$[ r_, s__], cond_, form_] /; buiActive["Forall"] := 
 	Module[ {splitC},
 		(* The condition MUST be kept unevaluated! Same in all other quantifiers. *)
 		splitC = splitAnd[ Hold[ cond], {Hold[ r][[1, 1]]}];
 		With[ {rc = Apply[ Unevaluated, splitC[[1]]], sc = Apply[ Unevaluated, splitC[[2]]]},
   			Forall$TM[ RNG$[r], rc, Forall$TM[ RNG$[s], sc, form]]
   		]
  	]

Forall$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; 
  buiActive["Forall"] :=
 	Module[ {iter},
     		forallIteration[ iter, cond, 
    form] /; (iter = rangeToIterator[ r]) =!= $Failed
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
			If[ TrueQ[ cond],
				ci = True,
				(*else*)
            	ci = ReleaseHold[ substituteFree[ Hold[ cond], {x -> i}]]
			];
			If[ ci,
				sub = ReleaseHold[ substituteFree[ Hold[ form], {x -> i}]];
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
				AppendTo[ uneval, Implies$TM[ ci, ReleaseHold[ substituteFree[ Hold[ form], {x -> i}]]]]
			],
			{ i, iter}
		]; (*end do*)
		makeConjunction[ uneval, And$TM]
	] (*end catch*)
 ]
    
Exists$TM[ RNG$[ r_, s__], cond_, form_] /; buiActive["Exists"] := 
 	Module[ {splitC},
 		splitC = splitAnd[ Hold[ cond], {Hold[ r][[1, 1]]}];
 		With[ {rc = Apply[ Unevaluated, splitC[[1]]], sc = Apply[ Unevaluated, splitC[[2]]]},
   			Exists$TM[ RNG$[r], rc, Exists$TM[ RNG$[s], sc, form]]
   		]
  	]

Exists$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; 
  buiActive["Exists"] :=
 	Module[ {iter},
     		existsIteration[ iter, cond, 
    form] /; (iter = rangeToIterator[ r]) =!= $Failed
  	]

SetAttributes[ existsIteration, HoldRest]
existsIteration[ {x_, iter__}, cond_, form_] :=
 Module[ {uneval = {}, ci, sub},
	Catch[
		Do[
			If[ TrueQ[ cond],
				ci = True,
				ci = ReleaseHold[ substituteFree[ Hold[ cond], {x -> i}]]
			];
			If[ ci,
				sub = ReleaseHold[ substituteFree[ Hold[ form], {x -> i}]];
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
				AppendTo[ uneval, And$TM[ ci, ReleaseHold[ substituteFree[ Hold[ form], {x -> i}]]]]
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
					ci = ReleaseHold[ substituteFree[ Hold[ cond], locSubs]]
				];
				If[ ci,
					comp = ReleaseHold[ substituteFree[ Hold[ form], locSubs]];
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
		Apply[ makeSet, s] /; (s = sequenceOfIteration[ Map[ rangeToIterator, {r}], cond, form]) =!= $Failed
	]

TupleOf$TM[ RNG$[ r__], cond_, form_] :=
	Module[ {s},
		Apply[ makeTuple, s] /; (s = sequenceOfIteration[ Map[ rangeToIterator, {r}], cond, form]) =!= $Failed
	]
  	
(* We have to split several summations into individual ones,
	because the various ranges may depend on each other, and this does not work in connection with
	"sequenceOfIteration". Same with "ProductOf", "MaximumOf", etc. *)
SumOf$TM[ RNG$[ r_, s__], cond_, form_] /; buiActive["SumOf"] :=
 	Module[ {splitC},
 		splitC = splitAnd[ Hold[ cond], {Hold[ r][[1, 1]]}];
 		With[ {rc = Apply[ Unevaluated, splitC[[1]]], sc = Apply[ Unevaluated, splitC[[2]]]},
 			SumOf$TM[ RNG$[r], rc, SumOf$TM[ RNG$[s], sc, form]]
 		]
	]
SumOf$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["SumOf"] :=
	Module[ {v},
		v /; (v = valueIteration[ rangeToIterator[ r], cond, form, Plus$TM, 0]) =!= $Failed
	]
SumOf$TM[ RNG$[ r_, s__], cond_, dom_, form_] /; buiActive["SumOf"] :=
 	Module[ {splitC},
 		splitC = splitAnd[ Hold[ cond], {Hold[ r][[1, 1]]}];
 		With[ {rc = Apply[ Unevaluated, splitC[[1]]], sc = Apply[ Unevaluated, splitC[[2]]]},
 			SumOf$TM[ RNG$[r], rc, dom, SumOf$TM[ RNG$[s], sc, dom, form]]
 		]
	]
SumOf$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, dom_, form_] /; buiActive["SumOf"] :=
	Module[ {v},
		v /; (v = valueIteration[ rangeToIterator[ r], cond, form, dom[Plus$TM], Theorema`Computation`Knowledge`Underscript$TM[0, dom]]) =!= $Failed
	]
	
ProductOf$TM[ RNG$[ r_, s__], cond_, form_] /; buiActive["ProductOf"] :=
 	Module[ {splitC},
 		splitC = splitAnd[ Hold[ cond], {Hold[ r][[1, 1]]}];
 		With[ {rc = Apply[ Unevaluated, splitC[[1]]], sc = Apply[ Unevaluated, splitC[[2]]]},
 			ProductOf$TM[ RNG$[r], rc, ProductOf$TM[ RNG$[s], sc, form]]
 		]
	]
ProductOf$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["ProductOf"] :=
	Module[ {v},
		v /; (v = valueIteration[ rangeToIterator[ r], cond, form, Times$TM, 1]) =!= $Failed
	]
ProductOf$TM[ RNG$[ r_, s__], cond_, dom_, form_] /; buiActive["ProductOf"] :=
 	Module[ {splitC},
 		splitC = splitAnd[ Hold[ cond], {Hold[ r][[1, 1]]}];
 		With[ {rc = Apply[ Unevaluated, splitC[[1]]], sc = Apply[ Unevaluated, splitC[[2]]]},
 			ProductOf$TM[ RNG$[r], rc, dom, ProductOf$TM[ RNG$[s], sc, dom, form]]
 		]
	]
ProductOf$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, dom_, form_] /; buiActive["ProductOf"] :=
	Module[ {v},
		v /; (v = valueIteration[ rangeToIterator[ r], cond, form, dom[Times$TM], Theorema`Computation`Knowledge`Underscript$TM[1, dom]]) =!= $Failed
	]
	
SetAttributes[ valueIteration, HoldRest]
valueIteration[ {x_, iter__}, cond_, term_, op_, def_] :=  
 Module[ {val = $Null, ci, comp, i},
 	(* "$Null" is meant to indicate that "val" does not have a value yet. *)
	Catch[
		Do[
			If[ Hold[ cond] === Hold[ True], (* cond must be kept unevaluated! *)
				ci = True,
				ci = ReleaseHold[ substituteFree[ Hold[ cond], {x -> i}]]
			];
			If[ ci,
				comp = ReleaseHold[ substituteFree[ Hold[ term], {x -> i}]];
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
				ci = ReleaseHold[ substituteFree[ Hold[ cond], {x -> i}]]
			];
			If[ ci,
				comp = ReleaseHold[ substituteFree[ Hold[ term], {x -> i}]];
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


MaximumOf$TM[ RNG$[ r_, s__], cond_, form_] /; buiActive["MaximumOf"] :=
 	Module[ {splitC},
 		splitC = splitAnd[ Hold[ cond], {Hold[ r][[1, 1]]}];
 		With[ {rc = Apply[ Unevaluated, splitC[[1]]], sc = Apply[ Unevaluated, splitC[[2]]]},
 			MaximumOf$TM[ RNG$[r], rc, MaximumOf$TM[ RNG$[s], sc, form]]
 		]
	]
MaximumOf$TM[ RNG$[ r_], cond_, form_] /; buiActive["MaximumOf"] :=
	Module[ {v},
		max$TM[ Apply[ makeSet, v]] /; (v = valueIteration[ rangeToIterator[ r], cond, form]) =!= $Failed
	]
MaximumOf$TM[ RNG$[ r_, s__], cond_, ord_, form_] /; buiActive["MaximumOf"] :=
 	Module[ {splitC},
 		splitC = splitAnd[ Hold[ cond], {Hold[ r][[1, 1]]}];
 		With[ {rc = Apply[ Unevaluated, splitC[[1]]], sc = Apply[ Unevaluated, splitC[[2]]]},
 			MaximumOf$TM[ RNG$[r], rc, ord, MaximumOf$TM[ RNG$[s], sc, ord, form]]
 		]
	]
MaximumOf$TM[ RNG$[ r_], cond_, ord_, form_] /; buiActive["MaximumOf"] :=
	Module[ {v},
		Subscript$TM[ max$TM, ord][ Apply[ makeSet, v]] /; (v = valueIteration[ rangeToIterator[ r], cond, form]) =!= $Failed
	]
	
MinimumOf$TM[ RNG$[ r_, s__], cond_, form_] /; buiActive["MinimumOf"] :=
 	Module[ {splitC},
 		splitC = splitAnd[ Hold[ cond], {Hold[ r][[1, 1]]}];
 		With[ {rc = Apply[ Unevaluated, splitC[[1]]], sc = Apply[ Unevaluated, splitC[[2]]]},
 			MinimumOf$TM[ RNG$[r], rc, MinimumOf$TM[ RNG$[s], sc, form]]
 		]
	]
MinimumOf$TM[ RNG$[ r_], cond_, form_] /; buiActive["MinimumOf"] :=
	Module[ {v},
		min$TM[ Apply[ makeSet, v]] /; (v = valueIteration[ rangeToIterator[ r], cond, form]) =!= $Failed
	]
MinimumOf$TM[ RNG$[ r_, s__], cond_, ord_, form_] /; buiActive["MinimumOf"] :=
 	Module[ {splitC},
 		splitC = splitAnd[ Hold[ cond], {Hold[ r][[1, 1]]}];
 		With[ {rc = Apply[ Unevaluated, splitC[[1]]], sc = Apply[ Unevaluated, splitC[[2]]]},
 			MinimumOf$TM[ RNG$[r], rc, ord, MinimumOf$TM[ RNG$[s], sc, ord, form]]
 		]
	]
MinimumOf$TM[ RNG$[ r_], cond_, ord_, form_] /; buiActive["MinimumOf"] :=
	Module[ {v},
		Subscript$TM[ min$TM, ord][ Apply[ makeSet, v]] /; (v = valueIteration[ rangeToIterator[ r], cond, form]) =!= $Failed
	]
	
UnionOf$TM[ RNG$[ r_, s__], cond_, form_] /; buiActive["UnionOf"] :=
 	Module[ {splitC},
 		splitC = splitAnd[ Hold[ cond], {Hold[ r][[1, 1]]}];
 		With[ {rc = Apply[ Unevaluated, splitC[[1]]], sc = Apply[ Unevaluated, splitC[[2]]]},
 			UnionOf$TM[ RNG$[r], rc, UnionOf$TM[ RNG$[s], sc, form]]
 		]
	]
UnionOf$TM[ RNG$[ r_], cond_, form_] /; buiActive["UnionOf"] :=
	Module[ {v},
		v /; (v = valueIteration[ rangeToIterator[ r], cond, form, Union$TM, Set$TM[]]) =!= $Failed
	]
UnionOf$TM[ RNG$[ r_, s__], cond_, dom_, form_] /; buiActive["UnionOf"] :=
 	Module[ {splitC},
 		splitC = splitAnd[ Hold[ cond], {Hold[ r][[1, 1]]}];
 		With[ {rc = Apply[ Unevaluated, splitC[[1]]], sc = Apply[ Unevaluated, splitC[[2]]]},
 			UnionOf$TM[ RNG$[r], rc, dom, UnionOf$TM[ RNG$[s], sc, dom, form]]
 		]
	]
UnionOf$TM[ RNG$[ r_], cond_, dom_, form_] /; buiActive["UnionOf"] :=
	Module[ {v},
		v /; (v = valueIteration[ rangeToIterator[ r], cond, form, Annotated$TM[ Union$TM, SubScript$TM[ dom]], Set$TM[]]) =!= $Failed
	]
	
IntersectionOf$TM[ RNG$[ r_, s__], cond_, form_] /; buiActive["IntersectionOf"] :=
 	Module[ {splitC},
 		splitC = splitAnd[ Hold[ cond], {Hold[ r][[1, 1]]}];
 		With[ {rc = Apply[ Unevaluated, splitC[[1]]], sc = Apply[ Unevaluated, splitC[[2]]]},
 			IntersectionOf$TM[ RNG$[r], rc, IntersectionOf$TM[ RNG$[s], sc, form]]
 		]
	]
IntersectionOf$TM[ RNG$[ r_], cond_, form_] /; buiActive["IntersectionOf"] :=
	Module[ {v},
		v /; (v = valueIteration[ rangeToIterator[ r], cond, form, Intersection$TM, $Failed]) =!= $Failed
	]
IntersectionOf$TM[ RNG$[ r_, s__], cond_, dom_, form_] /; buiActive["IntersectionOf"] :=
 	Module[ {splitC},
 		splitC = splitAnd[ Hold[ cond], {Hold[ r][[1, 1]]}];
 		With[ {rc = Apply[ Unevaluated, splitC[[1]]], sc = Apply[ Unevaluated, splitC[[2]]]},
 			IntersectionOf$TM[ RNG$[r], rc, dom, IntersectionOf$TM[ RNG$[s], sc, dom, form]]
 		]
	]
IntersectionOf$TM[ RNG$[ r_], cond_, dom_, form_] /; buiActive["IntersectionOf"] :=
	Module[ {v},
		v /; (v = valueIteration[ rangeToIterator[ r], cond, form, Annotated$TM[ Intersection$TM, SubScript$TM[ dom]], $Failed]) =!= $Failed
	]
	

(* ::Section:: *)
(* Sets *)

Set$TM /: Equal$TM[a__Set$TM] /; buiActive["SetEqual"] && SameQ[a] := True
Set$TM /: Equal$TM[_Set$TM] /; buiActive["SetEqual"] := True
Set$TM /: Equal$TM[a_Set$TM, b_Set$TM, c__Set$TM] /; buiActive["SetEqual"] :=
	Equal$TM[ a, b] && Map[ Equal$TM[ a, #]&, And[ c]]
Set$TM /: Equal$TM[a_Set$TM, b_Set$TM] /; buiActive["SetEqual"] :=
	Module[ {res},
		res /; (res = subseteq[ a, b, Equal$TM];
				If[ res === True,
					res = subseteq[ b, a, Equal$TM]
				];
				MatchQ[ res, True|False])
	]
Set$TM /: Annotated$TM[Equal$TM, SubScript$TM[ _]][_Set$TM] /; buiActive["SetEqual"] := True
Set$TM /: Annotated$TM[Equal$TM, SubScript$TM[ dom_]][a_Set$TM, b_Set$TM, c__Set$TM] /; buiActive["SetEqual"] :=
	dom[Equal$TM][ a, b] && Map[ dom[Equal$TM][ a, #]&, And[ c]]
Set$TM /: Annotated$TM[Equal$TM, SubScript$TM[ dom_]][a_Set$TM, b_Set$TM] /; buiActive["SetEqual"] :=
	Module[ {res},
		res /; (res = subseteq[ a, b, dom[Equal$TM]];
				If[ res === True,
					res = subseteq[ b, a, dom[Equal$TM]]
				];
				MatchQ[ res, True|False])
	]
Set$TM /: SubsetEqual$TM[a_Set$TM, b_Set$TM] /; buiActive["SubsetEqual"] :=
	Module[ {res},
		res /; (res = subseteq[ a, b, Equal$TM]; MatchQ[ res, True|False])
	]
Set$TM /: Annotated$TM[SubsetEqual$TM, SubScript$TM[ dom_]][a_Set$TM, b_Set$TM] /; buiActive["SubsetEqual"] :=
		Module[ {res},
		res /; (res = subseteq[ a, b, dom[Equal$TM]]; MatchQ[ res, True|False])
	]
Set$TM /: Subset$TM[a_Set$TM, b_Set$TM] /; buiActive["Subset"] :=
	Module[ {res},
		res /; (res = subseteq[ a, b, Equal$TM];
				If[ res === True,
					res = !subseteq[ b, a, Equal$TM]
				];
				MatchQ[ res, True|False])
	]
Set$TM /: Annotated$TM[Subset$TM, SubScript$TM[ dom_]][a_Set$TM, b_Set$TM] /; buiActive["Subset"] :=
	Module[ {res},
		res /; (res = subseteq[ a, b, dom[Equal$TM]];
				If[ res === True,
					res = !subseteq[ b, a, dom[Equal$TM]]
				];
				MatchQ[ res, True|False])
	]
Set$TM /: SupersetEqual$TM[a_Set$TM, b_Set$TM] /; buiActive["SupersetEqual"] :=
	Module[ {res},
		res /; (res = subseteq[ b, a, Equal$TM]; MatchQ[ res, True|False])
	]
Set$TM /: Annotated$TM[SupersetEqual$TM, SubScript$TM[ dom_]][a_Set$TM, b_Set$TM] /; buiActive["SupersetEqual"] :=
	Module[ {res},
		res /; (res = subseteq[ b, a, dom[Equal$TM]]; MatchQ[ res, True|False])
	]
Set$TM /: Superset$TM[a_Set$TM, b_Set$TM] /; buiActive["Superset"] :=
	Module[ {res},
		res /; (res = subseteq[ b, a, Equal$TM];
				If[ res === True,
					res = !subseteq[ a, b, Equal$TM]
				];
				MatchQ[ res, True|False])
	]
Set$TM /: Annotated$TM[Superset$TM, SubScript$TM[ dom_]][a_Set$TM, b_Set$TM] /; buiActive["Superset"] :=
	Module[ {res},
		res /; (res = subseteq[ b, a, dom[Equal$TM]];
				If[ res === True,
					res = !subseteq[ a, b, dom[Equal$TM]]
				];
				MatchQ[ res, True|False])
	]

(* "Union" can be implemented in this nice way (in contrast to "Intersection", "Complement", ...),
	because in any case it does not harm to put more elements into the resulting set than actually needed
	(some might be equal).
	Also note that it is possible to form the union over 0 sets, whereas the intersection of 0 sets is not defined. *)
Set$TM /: Union$TM[ a___Set$TM] /; buiActive["Union"] := Union[ a, SameTest -> (TrueQ[ Equal$TM[ #1, #2]]&)]
Set$TM /: Annotated$TM[ Union$TM, SubScript$TM[ dom_]][ a___Set$TM] /; buiActive["Union"] := Union[ a, SameTest -> (TrueQ[ dom[Equal$TM][ #1, #2]]&)]
Set$TM /: Intersection$TM[ a_Set$TM, b___Set$TM] /; buiActive["Intersection"] :=
	Module[ {res = Set$TM[]},
		res /; (Scan[ If[ ElementOfAll[#, {b}, Equal$TM], AppendTo[res, #], Null, res = False; Return[]] &, a]; res =!= False)
	]
Set$TM /: Annotated$TM[ Intersection$TM, SubScript$TM[ dom_]][ a_Set$TM, b___Set$TM] /; buiActive["Intersection"] :=
	Module[ {res = Set$TM[]},
		res /; (Scan[ If[ ElementOfAll[#, {b}, dom[Equal$TM]], AppendTo[res, #], Null, res = False; Return[]] &, a]; res =!= False)
	]
Set$TM /: Backslash$TM[ a_Set$TM, b_Set$TM] /; buiActive["Difference"] :=
	Module[ {res = Set$TM[]},
		res /; (Scan[ If[ ElementOf[#, b, Equal$TM], Null, AppendTo[res, #], res = False; Return[]] &, a]; res =!= False)
	]
Set$TM /: Annotated$TM[ Backslash$TM, SubScript$TM[ dom_]][ a_Set$TM, b_Set$TM] /; buiActive["Difference"] :=
	Module[ {res = Set$TM[]},
		res /; (Scan[ If[ ElementOf[#, b, dom[Equal$TM]], Null, AppendTo[res, #], res = False; Return[]] &, a]; res =!= False)
	]
Set$TM /: EmptyUpTriangle$TM[ a_Set$TM, b_Set$TM] /; buiActive["SymmetricDifference"] :=
	Module[ {res = Set$TM[]},
		res /;
			(Scan[ If[ ElementOf[#, b, Equal$TM], Null, AppendTo[res, #], res = False; Return[]] &, a];
			If[ res === False,
				False,
				Scan[ If[ ElementOf[#, a, Equal$TM], Null, AppendTo[res, #], res = False; Return[]] &, b];
				res =!= False
			])
	]
Set$TM /: Annotated$TM[ EmptyUpTriangle$TM, SubScript$TM[ dom_]][ a_Set$TM, b_Set$TM] /; buiActive["SymmetricDifference"] :=
	Module[ {res = Set$TM[]},
		res /;
			(Scan[ If[ ElementOf[#, b, dom[Equal$TM]], Null, AppendTo[res, #], res = False; Return[]] &, a];
			If[ res === False,
				False,
				Scan[ If[ ElementOf[#, a, dom[Equal$TM]], Null, AppendTo[res, #], res = False; Return[]] &, b];
				res =!= False
			])
	]
Set$TM /: Cross$TM[ a__Set$TM] /; buiActive["CartesianProduct"] := Apply[Set$TM, Replace[Tuples[{a}],List[x__]:> Tuple$TM[x] ,{1}]]
Set$TM /: Element$TM[ p_, a_Set$TM] /; buiActive["IsElement"] :=
	Module[ {res},
		res /; (res = ElementOf[ p, a, Equal$TM]; MatchQ[ res, True|False])
	]
Set$TM /: Annotated$TM[ Element$TM, SubScript$TM[dom_]][ p_, a_Set$TM] /; buiActive["IsElement"] :=
	Module[ {res},
		res /; (res = ElementOf[ p, a, dom[Equal$TM]]; MatchQ[ res, True|False])
	]
Set$TM /: \[ScriptCapitalP]$TM[ a_Set$TM] /; buiActive["PowerSet"] := Subsets[ a] /. List -> Set$TM
Set$TM /: BracketingBar$TM[ a_Set$TM?isSequenceFree] /; buiActive["Cardinality"] && pairwiseDistinct[ a, Equal$TM] :=
	Length[ a]
Set$TM /: max$TM[ Set$TM[ e__]] /; buiActive["MaximumElementSet"] :=
	Module[ {s},
		(s /. Max -> max$TM /. {max$TM[x_Set$TM] :> max$TM[x], max$TM[x___] :> max$TM[Set$TM[x]]}) /; (s = Max[ e]; Apply[ Hold, {s}] =!= Hold[ Max[ e]])
	]
Set$TM /: Subscript$TM[ max$TM, ord_][ Set$TM[ e__]] /; buiActive["MaximumElementSet"] :=
	Module[ {res},
		First[ res] /; (res = max[ {e}, ord]; Length[ res] === 1)
	]
Set$TM /: min$TM[ Set$TM[ e__]] /; buiActive["MinimumElementSet"] :=
	Module[ {s},
		(s /. Min -> min$TM /. {min$TM[x_Set$TM] :> min$TM[x], min$TM[x___] :> min$TM[Set$TM[x]]}) /; (s = Min[ e]; Apply[ Hold, {s}] =!= Hold[ Min[ e]])
	]
Set$TM /: Subscript$TM[ min$TM, ord_][ Set$TM[ e__]] /; buiActive["MinimumElementSet"] :=
	Module[ {res},
		First[ res] /; (res = min[ {e}, ord]; Length[ res] === 1)
	]
Set$TM /: \[AE]$TM[ Set$TM[ a_, ___]] /; buiActive["AnElement"] := a
	

(* amaletzk: The following implementation of "max" and "min" has quadratic complexity in the length of the
	input. One could, however, also compare only successive elements, but this method would only give
	the right result in case of a linear ordering, not in case of an arbitrary partial ordering! *)
max[ l:{___, a_, ___}, ord_] /; greatest[ a, l, ord] := {a}
max[ _List, _] := {}

greatest[ _, {}, _] := True
greatest[ a_, {b_, rest___}, ord_] := TrueQ[ ord[ b, a] || a == b] && greatest[ a, {rest}, ord]

min[ l:{___, a_, ___}, ord_] /; smallest[ a, l, ord] := {a}
min[ _List, _] := {}

smallest[ _, {}, _] := True
smallest[ a_, {b_, rest___}, ord_] := TrueQ[ ord[ a, b] || a == b] && smallest[ a, {rest}, ord]

ElementOf[ p_, a_, test_] := Apply[ Or, Map[ (test[ p, #])&, Apply[ Hold, a]]]
ElementOfAll[ p_, {a_, rest___}, test_] := ElementOf[ p, a, test] && ElementOfAll[ p, {rest}, test]
ElementOfAll[ _, {}, _] := True

pairwiseDistinct[ _[ f_, rest___], test_] := ElementOf[ f, {rest}, test] === False && pairwiseDistinct[ {rest}, test]
pairwiseDistinct[ _[], _] := True

subseteq[ a_, b_, test_] :=
	Module[ {res = True},
		Scan[ If[ ElementOf[#, b, test], Null, res = False; Return[], res = Null] &, a];
		res
	]


(* ::Section:: *)
(* Number Domains *)


(* ::Subsection:: *)
(* simplification *)

IntegerInterval$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)] /; buiActive["IntegerInterval"] && intervalSize[ IntegerInterval$TM, l, r, lc, rc] === 0 := Set$TM[ ]
RationalInterval$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)] /; buiActive["RationalInterval"] && intervalSize[ RationalInterval$TM, l, r, lc, rc] === 0 := Set$TM[ ]
RealInterval$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)] /; buiActive["RealInterval"] && intervalSize[ RealInterval$TM, l, r, lc, rc] === 0 := Set$TM[ ]
IntegerQuotientRing$TM[ 0] /; buiActive["IntegerQuotientRing"] := IntegerInterval$TM[ DirectedInfinity[ -1], DirectedInfinity[ 1], False, False] (* Z_0 is isomorphic to Z *)
IntegerQuotientRingPM$TM[ 0] /; buiActive["IntegerQuotientRingPM"] := IntegerInterval$TM[ DirectedInfinity[ -1], DirectedInfinity[ 1], False, False]


(* ::Subsection:: *)
(* equality *)

Set$TM /: Equal$TM[ a:(h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ al_?isRealOrInf, ar_?isRealOrInf, alc:(True|False), arc:(True|False)],
		b:Set$TM[ e___?isGround]] :=
	Module[ {rs},
		SameQ[ rs, Length[ b], Length[ Select[ b, isInInterval[ #, a]&]]] /; buiActive["SetEqual"] && buiActive[StringDrop[SymbolName[h], -3]] && ((rs = intervalSize[h, al, ar, alc, arc]) =!= $Failed)
	]
Set$TM /: Equal$TM[ a_Set$TM, b:(_IntegerInterval$TM|_RationalInterval$TM|_RealInterval$TM)] /; buiActive["SetEqual"] := Equal$TM[ b, a]
Set$TM /: Equal$TM[ _Set$TM, b:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive["SetEqual"] && buiActive[StringDrop[SymbolName[b], -3]] := False
Set$TM /: Equal$TM[ b:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM), _Set$TM] /; buiActive["SetEqual"] && buiActive[StringDrop[SymbolName[b], -3]] := False
(* Set$TM /: Equal$TM[ (h:(IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ m_?isModulus], a:Set$TM[ e___?isGround]] /; buiActive["SetEqual"] && buiActive[StringDrop[SymbolName[h], -3]] :=
	Length[ a] == m && Apply[ And, Map[ (isInteger[ #] && IQRLower[ h, m] <= # <= IQRUpper[ h, m])&, Hold[ e]]]
Set$TM /: Equal$TM[ a_Set$TM, b:(_IntegerQuotientRing$TM|_IntegerQuotientRingPM$TM)] /; buiActive["SetEqual"] := Equal$TM[ b, a] *)

\[DoubleStruckCapitalC]$TM /: Equal$TM[ (a:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[ ___], \[DoubleStruckCapitalC]$TM] :=
	False /; buiActive["SetEqual"] && buiActive[StringDrop[SymbolName[a], -3]] && buiActive["\[DoubleStruckCapitalC]"]
\[DoubleStruckCapitalC]$TM /: Equal$TM[ \[DoubleStruckCapitalC]$TM, (a:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[ ___]] :=
	False /; buiActive["SetEqual"] && buiActive[StringDrop[SymbolName[a], -3]] && buiActive["\[DoubleStruckCapitalC]"]
\[DoubleStruckCapitalC]P$TM /: Equal$TM[ (a:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[ ___], \[DoubleStruckCapitalC]P$TM] :=
	False /; buiActive["SetEqual"] && buiActive[StringDrop[SymbolName[a], -3]] && buiActive["\[DoubleStruckCapitalC]P"]
\[DoubleStruckCapitalC]P$TM /: Equal$TM[ \[DoubleStruckCapitalC]P$TM, (a:IntegerInterval$TM|RationalInterval$TM|RealInterval$TM)[ ___]] :=
	False /; buiActive["SetEqual"] && buiActive[StringDrop[SymbolName[a], -3]] && buiActive["\[DoubleStruckCapitalC]P"]
\[DoubleStruckCapitalC]$TM /: Equal$TM[ (h:(IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ _], \[DoubleStruckCapitalC]$TM] :=
	False /; buiActive["SetEqual"] && buiActive[StringDrop[SymbolName[h], -3]] && buiActive["\[DoubleStruckCapitalC]"]
\[DoubleStruckCapitalC]$TM /: Equal$TM[ \[DoubleStruckCapitalC]$TM, (h:(IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ _]] :=
	False /; buiActive["SetEqual"] && buiActive[StringDrop[SymbolName[h], -3]] && buiActive["\[DoubleStruckCapitalC]"]
\[DoubleStruckCapitalC]P$TM /: Equal$TM[ (h:(IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ _], \[DoubleStruckCapitalC]P$TM] :=
	False /; buiActive["SetEqual"] && buiActive[StringDrop[SymbolName[h], -3]] && buiActive["\[DoubleStruckCapitalC]P"]
\[DoubleStruckCapitalC]P$TM /: Equal$TM[ \[DoubleStruckCapitalC]P$TM, (h:(IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ _]] :=
	False /; buiActive["SetEqual"] && buiActive[StringDrop[SymbolName[h], -3]] && buiActive["\[DoubleStruckCapitalC]P"]
	
\[DoubleStruckCapitalC]$TM /: Equal$TM[ \[DoubleStruckCapitalC]$TM, \[DoubleStruckCapitalC]P$TM] :=
	False /; buiActive["SetEqual"] && buiActive["\[DoubleStruckCapitalC]"] && buiActive["\[DoubleStruckCapitalC]P"]
\[DoubleStruckCapitalC]$TM /: Equal$TM[ \[DoubleStruckCapitalC]$TM, \[DoubleStruckCapitalC]$TM] :=
	True /; buiActive["SetEqual"] && buiActive["\[DoubleStruckCapitalC]"]
\[DoubleStruckCapitalC]P$TM /: Equal$TM[ \[DoubleStruckCapitalC]P$TM, \[DoubleStruckCapitalC]$TM] :=
	False /; buiActive["SetEqual"] && buiActive["\[DoubleStruckCapitalC]"] && buiActive["\[DoubleStruckCapitalC]P"]
\[DoubleStruckCapitalC]P$TM /: Equal$TM[ \[DoubleStruckCapitalC]P$TM, \[DoubleStruckCapitalC]P$TM] :=
	True /; buiActive["SetEqual"] && buiActive["\[DoubleStruckCapitalC]P"]
	
(* IntegerQuotientRing$TM /: Equal$TM[ _IntegerQuotientRing$TM, (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ ___]] :=
	False /; buiActive["SetEqual"] && buiActive["IntegerQuotientRing"] && buiActive[StringDrop[SymbolName[h], -3]]
IntegerQuotientRing$TM /: Equal$TM[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ ___], _IntegerQuotientRing$TM] :=
	False /; buiActive["SetEqual"] && buiActive["IntegerQuotientRing"] && buiActive[StringDrop[SymbolName[h], -3]]
IntegerQuotientRingPM$TM /: Equal$TM[ _IntegerQuotientRingPM$TM, (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ ___]] :=
	False /; buiActive["SetEqual"] && buiActive["IntegerQuotientRingPM"] && buiActive[StringDrop[SymbolName[h], -3]]
IntegerQuotientRingPM$TM /: Equal$TM[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ ___], _IntegerQuotientRingPM$TM] :=
	False /; buiActive["SetEqual"] && buiActive["IntegerQuotientRingPM"] && buiActive[StringDrop[SymbolName[h], -3]]
	
IntegerQuotientRing$TM /: Equal$TM[ IntegerQuotientRing$TM[ m_], IntegerQuotientRing$TM[ n_]] :=
	m == n /; buiActive["SetEqual"] && buiActive["IntegerQuotientRing"]
IntegerQuotientRing$TM /: Equal$TM[ IntegerQuotientRing$TM[ m_?isModulus], IntegerQuotientRingPM$TM[ n_?isModulus]] :=
	m == n && m <= 2 /; buiActive["SetEqual"] && buiActive["IntegerQuotientRing"] && buiActive["IntegerQuotientRingPM"]
IntegerQuotientRingPM$TM /: Equal$TM[ IntegerQuotientRingPM$TM[ m_?isModulus], IntegerQuotientRing$TM[ n_?isModulus]] :=
	m == n && m <= 2 /; buiActive["SetEqual"] && buiActive["IntegerQuotientRing"] && buiActive["IntegerQuotientRingPM"]
IntegerQuotientRingPM$TM /: Equal$TM[ IntegerQuotientRingPM$TM[ m_], IntegerQuotientRingPM$TM[ n_]] :=
	m == n /; buiActive["SetEqual"] && buiActive["IntegerQuotientRingPM"] *)

IntegerInterval$TM /: Equal$TM[ IntegerInterval$TM[ al_?isRealOrInf, ar_?isRealOrInf, alc:(True|False), arc:(True|False)],
		IntegerInterval$TM[ bl_?isRealOrInf, br_?isRealOrInf, blc:(True|False), brc:(True|False)]] /; buiActive["SetEqual"] && buiActive["IntegerInterval"] :=
	And[ integerBoundary["left", al, alc] == integerBoundary["left", bl, blc], integerBoundary["right", ar, arc] == integerBoundary["right", br, brc]]
IntegerInterval$TM /: Equal$TM[ IntegerInterval$TM[ al_?isRealOrInf, ar_?isRealOrInf, alc:(True|False), arc:(True|False)],
		(b:(RationalInterval$TM|RealInterval$TM))[ bl_?isRealOrInf, br_?isRealOrInf, blc:(True|False), brc:(True|False)]] /; buiActive["SetEqual"] && buiActive["IntegerInterval"] && buiActive[StringDrop[SymbolName[b],-3]] :=
	And[ SameQ[ 1, intervalSize[IntegerInterval$TM, al, ar, alc, arc], intervalSize[b, bl, br, blc, brc]], integerBoundary["left", al, alc] == bl]
IntegerInterval$TM /: Equal$TM[ a:(_RationalInterval$TM|_RealInterval$TM), b_IntegerInterval$TM] /; buiActive["SetEqual"] := Equal$TM[ b, a]

RationalInterval$TM /: Equal$TM[ RationalInterval$TM[ al_?isRealOrInf, ar_?isRealOrInf, alc:(True|False), arc:(True|False)],
		RationalInterval$TM[ bl_?isRealOrInf, br_?isRealOrInf, blc:(True|False), brc:(True|False)]] /; buiActive["SetEqual"] && buiActive["RationalInterval"] :=
	Module[ {alcc, arcc, blcc, brcc},
		(al === bl && ar === br && alcc === blcc && arcc === brcc) /;
				(alcc = If[ alc && isInIntervalDomain[ RationalInterval$TM, al], True, False, $Failed];
				arcc = If[ arc && isInIntervalDomain[ RationalInterval$TM, ar], True, False, $Failed];
				blcc = If[ blc && isInIntervalDomain[ RationalInterval$TM, bl], True, False, $Failed];
				brcc = If[ brc && isInIntervalDomain[ RationalInterval$TM, br], True, False, $Failed];
				Xor[ alcc =!= $Failed, blcc === $Failed] && Xor[ arcc =!= $Failed, brcc === $Failed])
	]
RationalInterval$TM /: Equal$TM[ RationalInterval$TM[ al_?isRealOrInf, ar_?isRealOrInf, alc:(True|False), arc:(True|False)],
		RealInterval$TM[ bl_?isRealOrInf, br_?isRealOrInf, blc:(True|False), brc:(True|False)]] :=
	Module[ {rs},
		And[ SameQ[ 1, rs, intervalSize[RealInterval$TM, bl, br, blc, brc]], al == bl] /;
				buiActive["SetEqual"] && buiActive["RationalInterval"] && buiActive["RealInterval"] && ((rs = intervalSize[RationalInterval$TM, al, ar, alc, arc]) =!= $Failed)
	]
RationalInterval$TM /: Equal$TM[ a_RealInterval$TM, b_RationalInterval$TM] /; buiActive["SetEqual"] := Equal$TM[ b, a]

RealInterval$TM /: Equal$TM[ RealInterval$TM[ al_?isRealOrInf, ar_?isRealOrInf, alc:(True|False), arc:(True|False)],
		RealInterval$TM[ bl_?isRealOrInf, br_?isRealOrInf, blc:(True|False), brc:(True|False)]] /; buiActive["SetEqual"] && buiActive["RealInterval"] :=
	With[ {alcc = Switch[ al, _DirectedInfinity, False, _, alc],
			arcc = Switch[ ar, _DirectedInfinity, False, _, arc],
			blcc = Switch[ bl, _DirectedInfinity, False, _, blc],
			brcc = Switch[ br, _DirectedInfinity, False, _, brc]},
		And[ al == bl, ar == br, alcc === blcc, arcc === brcc]
	]
	
	
(* ::Subsection:: *)
(* intersection *)

Set$TM /: Intersection$TM[ a:(h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ _?isRealOrInf, _?isRealOrInf, True|False, True|False],
		b:Set$TM[ ___?isGround]] /; buiActive["Intersection"] && buiActive[StringDrop[SymbolName[h],-3]] :=
	Select[ b, isInInterval[ #, a]&]
Set$TM /: Intersection$TM[ a_Set$TM, b:(_IntegerInterval$TM|_RationalInterval$TM|_RealInterval$TM)] /; buiActive["Intersection"] := Intersection$TM[ b, a]
Set$TM /: Intersection$TM[ \[DoubleStruckCapitalC]$TM, b:Set$TM[ ___?isGround]] /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]"] :=
	Select[ b, isComplex]
Set$TM /: Intersection$TM[ b_Set$TM, \[DoubleStruckCapitalC]$TM] /; buiActive["Intersection"] := Intersection$TM[ \[DoubleStruckCapitalC]$TM, b]
Set$TM /: Intersection$TM[ \[DoubleStruckCapitalC]P$TM, b:Set$TM[ ___?isGround]] /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]"] :=
	Select[ b, isComplex]
Set$TM /: Intersection$TM[ b_Set$TM, \[DoubleStruckCapitalC]P$TM] /; buiActive["Intersection"] := Intersection$TM[ \[DoubleStruckCapitalC]P$TM, b]

\[DoubleStruckCapitalC]$TM /: Intersection$TM[ \[DoubleStruckCapitalC]$TM, b:((h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ ___])] :=
	b /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]"] && buiActive[StringDrop[SymbolName[h], -3]]
\[DoubleStruckCapitalC]$TM /: Intersection$TM[ b:((h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ ___]), \[DoubleStruckCapitalC]$TM] :=
	b /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]"] && buiActive[StringDrop[SymbolName[h], -3]]
\[DoubleStruckCapitalC]P$TM /: Intersection$TM[ \[DoubleStruckCapitalC]P$TM, (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ ___]] :=
	Set$TM[ ] /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]P"] && buiActive[StringDrop[SymbolName[h], -3]]
\[DoubleStruckCapitalC]P$TM /: Intersection$TM[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ ___], \[DoubleStruckCapitalC]P$TM] :=
	Set$TM[ ] /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]P"] && buiActive[StringDrop[SymbolName[h], -3]]
	
\[DoubleStruckCapitalC]$TM /: Intersection$TM[ \[DoubleStruckCapitalC]$TM, \[DoubleStruckCapitalC]$TM] :=
	\[DoubleStruckCapitalC]$TM /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]"]
\[DoubleStruckCapitalC]$TM /: Intersection$TM[ \[DoubleStruckCapitalC]$TM, \[DoubleStruckCapitalC]P$TM] :=
	Set$TM[ ] /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]"] && buiActive["\[DoubleStruckCapitalC]P"]
\[DoubleStruckCapitalC]P$TM /: Intersection$TM[ \[DoubleStruckCapitalC]P$TM, \[DoubleStruckCapitalC]$TM] :=
	Set$TM[ ] /; buiActive["Intersection"] && buiActive["\[DoubleStruckCapitalC]P"] && buiActive["\[DoubleStruckCapitalC]"]
\[DoubleStruckCapitalC]P$TM /: Intersection$TM[ \[DoubleStruckCapitalC]P$TM, \[DoubleStruckCapitalC]P$TM] :=
	\[DoubleStruckCapitalC]P$TM /; buiActive["Intersection"] buiActive["\[DoubleStruckCapitalC]P"]
		
IntegerInterval$TM /: Intersection$TM[ a:IntegerInterval$TM[ _?isRealOrInf, _?isRealOrInf, True|False, True|False],
		b:(h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM))[ _?isRealOrInf, _?isRealOrInf, True|False, True|False]] /;
			buiActive["Intersection"] && buiActive["IntegerInterval"] && buiActive[StringDrop[SymbolName[h],-3]] :=
	IntegerInterval$TM[ intersectIntervals[ a, b]]
IntegerInterval$TM /: Intersection$TM[ a:(_RationalInterval$TM|_RealInterval$TM), b_IntegerInterval$TM] /; buiActive["Intersection"] := Intersection$TM[ b, a]

RationalInterval$TM /: Intersection$TM[ a:RationalInterval$TM[ _?isRealOrInf, _?isRealOrInf, True|False, True|False],
		b:(h:(RationalInterval$TM|RealInterval$TM))[ _?isRealOrInf, _?isRealOrInf, True|False, True|False]] /;
			buiActive["Intersection"] && buiActive["RationalInterval"] && buiActive[StringDrop[SymbolName[h],-3]] :=
	RationalInterval$TM[ intersectIntervals[ a, b]]
RationalInterval$TM /: Intersection$TM[ a_RationalInterval$TM, b_RealInterval$TM] /; buiActive["Intersection"] := Intersection$TM[ b, a]

RealInterval$TM /: Intersection$TM[ a:RealInterval$TM[ _?isRealOrInf, _?isRealOrInf, True|False, True|False],
		b:RealInterval$TM[ _?isRealOrInf, _?isRealOrInf, True|False, True|False]] /; buiActive["Intersection"] && buiActive["RealInterval"] :=
	RealInterval$TM[ intersectIntervals[ a, b]]


(* ::Subsection:: *)
(* element *)

\[DoubleStruckCapitalC]$TM /: Element$TM[ p_, \[DoubleStruckCapitalC]$TM] /; buiActive["IsElement"] && buiActive["\[DoubleStruckCapitalC]"] := isComplex[ p]
\[DoubleStruckCapitalC]P$TM /: Element$TM[ p_, \[DoubleStruckCapitalC]P$TM] /; buiActive["IsElement"] && buiActive["\[DoubleStruckCapitalC]P"] := isComplexP[ p]
Element$TM[ p_, h:(_IntegerInterval$TM|_RationalInterval$TM|_RealInterval$TM)] /; buiActive["IsElement"] && buiActive[StringDrop[SymbolName[Head[h]],-3]] := isInInterval[ p, h]


(* ::Subsection:: *)
(* cardinality *)

\[DoubleStruckCapitalC]$TM /: BracketingBar$TM[ \[DoubleStruckCapitalC]$TM] /; buiActive["Cardinality"] && buiActive["\[DoubleStruckCapitalC]"] := Infinity
\[DoubleStruckCapitalC]P$TM /: BracketingBar$TM[ \[DoubleStruckCapitalC]P$TM] /; buiActive["Cardinality"] && buiActive["\[DoubleStruckCapitalC]P"] := Infinity
IntegerQuotientRing$TM /: BracketingBar$TM[ IntegerQuotientRing$TM[ m_?isModulus]] /; buiActive["Cardinality"] && buiActive["IntegerQuotientRing"] := m
IntegerQuotientRingPM$TM /: BracketingBar$TM[ IntegerQuotientRingPM$TM[ m_?isModulus]] /; buiActive["Cardinality"] && buiActive["IntegerQuotientRingPM"] := m
IntegerInterval$TM /: BracketingBar$TM[ IntegerInterval$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)]] /; buiActive["Cardinality"] && buiActive["IntegerInterval"] :=
	intervalSize[ IntegerInterval$TM, l, r, lc, rc]
RationalInterval$TM /: BracketingBar$TM[ RationalInterval$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)]] :=
	Module[ {rs},
		rs /; buiActive["Cardinality"] && buiActive["RationalInterval"] && ((rs = intervalSize[ RationalInterval$TM, l, r, lc, rc]) =!= $Failed)
	]
RealInterval$TM /: BracketingBar$TM[ RealInterval$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)]] /; buiActive["Cardinality"] && buiActive["RealInterval"] :=
	intervalSize[ RealInterval$TM, l, r, lc, rc]
	
	
(* ::Subsection:: *)
(* min/max *)

IntegerInterval$TM /: min$TM[ IntegerInterval$TM[ l_?isRealOrInf, _?isRealOrInf, lc:(True|False), True|False]] /; buiActive["MinimumElementSet"] && buiActive["IntegerInterval"] && l > -Infinity :=
	integerBoundary[ "left", l, lc]
RationalInterval$TM /: min$TM[ RationalInterval$TM[ l_?isInIntervalDomain[ RationalInterval$TM, #]&, _?isRealOrInf, True, True|False]] /; buiActive["MinimumElementSet"] && buiActive["RationalInterval"] :=
	l
RealInterval$TM /: min$TM[ RealInterval$TM[ l_?isRealOrInf, _?isRealOrInf, True, True|False]] /; buiActive["MinimumElementSet"] && buiActive["RealInterval"] && l > -Infinity :=
	l
	
IntegerInterval$TM /: max$TM[ IntegerInterval$TM[ _?isRealOrInf, r_?isRealOrInf, True|False, rc:(True|False)]] /; buiActive["MaximumElementSet"] && buiActive["IntegerInterval"] && r < Infinity :=
	integerBoundary[ "right", r, rc]
RationalInterval$TM /: max$TM[ RationalInterval$TM[ _?isRealOrInf, r_?isInIntervalDomain[ RationalInterval$TM, #]&, True|False, True]] /; buiActive["MaximumElementSet"] && buiActive["RationalInterval"] :=
	r
RealInterval$TM /: max$TM[ RealInterval$TM[ _?isRealOrInf, r_?isRealOrInf, True|False, True]] /; buiActive["MaximumElementSet"] && buiActive["RealInterval"] && r < Infinity :=
	r


(* ::Subsection:: *)
(* auxiliary functions *)

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
isInIntervalDomain[ IntegerInterval$TM, a_] := isInteger[ a]
isInIntervalDomain[ RationalInterval$TM, a_] := isRational[ a]
isInIntervalDomain[ RealInterval$TM, a_] := isReal[ a]

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


Tuple$TM /: Insert$TM[ a_Tuple$TM?isSequenceFree, p_, q_] /; buiActive["Insert"] := Insert[ a, p, q /. Tuple$TM -> List]

(* Delete elements at one or more positions *)
Tuple$TM /: DeleteAt$TM[ a_Tuple$TM?isSequenceFree, b_] /; buiActive["DeleteAt"] := Delete[ a, b //. Tuple$TM -> List]

(* Delete elements of a certain shape. Multiple deletions are not possible, because it would need
	special syntax how to specify multiple shapes. Tuples cannot be used because for this *)
Tuple$TM /: Delete$TM[a_Tuple$TM?isGround, d__?isGround] /; buiActive["Delete"] := Fold[ DeleteCases[ #1, #2]&, a, {d}] 

Tuple$TM /: Equal$TM[a__Tuple$TM] /; buiActive["TupleEqual"] && SameQ[a ] := True
Tuple$TM /: Equal$TM[a__Tuple$TM?isSequenceFree] /; buiActive["TupleEqual"] :=
	Module[ {res},
		res /; (res = If[ Apply[ SameQ, Map[ Length, Hold[ a]]],
						Map[ Replace[#, {x__} :> Equal$TM[ x]] &, Apply[ And, Transpose[
							Map[ Replace[ #, Tuple$TM[ x__] :> {x}]&, {a}]]]
							],
						False
					];
				MatchQ[ res, True|False])
	]
Tuple$TM /: Annotated$TM[Equal$TM, SubScript$TM[ dom_]][a__Tuple$TM?isSequenceFree] /; buiActive["TupleEqual"] :=
	Module[ {res},
		res /; (res = If[ Apply[ SameQ, Map[ Length, Hold[ a]]],
						Map[ Replace[#, {x__} :> dom[Equal$TM][ x]] &, Apply[ And, Transpose[
							Map[ Replace[ #, Tuple$TM[ x__] :> {x}]&, {a}]]]
							],
						False
					];
				MatchQ[ res, True|False])
	]

Tuple$TM /: appendElem$TM[a_Tuple$TM, p_] /; buiActive["appendElem"] := Append[ a, p]
Tuple$TM /: prependElem$TM[a_Tuple$TM, p_] /; buiActive["prependElem"] := Prepend[ a, p]
Tuple$TM /: joinTuples$TM[a__Tuple$TM] /; buiActive["joinTuples"] := Join[ a]

Tuple$TM /: elemTuple$TM[ p_, a_Tuple$TM] /; buiActive["elemTuple"] :=
	Module[ {res},
		res /; (res = ElementOf[ p, a, Equal$TM]; MatchQ[ res, True|False])
	]
Tuple$TM /: Annotated$TM[ elemTuple$TM, SubScript$TM[ dom_]][ p_, a_Tuple$TM] /; buiActive["elemTuple"] :=
	Module[ {res},
		res /; (res = ElementOf[ p, a, dom[Equal$TM]]; MatchQ[ res, True|False])
	]

Tuple$TM /: max$TM[ Tuple$TM[ e__]] /; buiActive["Max"] :=
	Module[ {s},
		(s /. Max -> max$TM /. {max$TM[x_Tuple$TM] :> max$TM[x], max$TM[x___] :> max$TM[Tuple$TM[x]]}) /; (s = Max[ e]; Apply[ Hold, {s}] =!= Hold[ Max[ e]])
	]
Tuple$TM /: Subscript$TM[ max$TM, ord_][ Tuple$TM[ e__]] /; buiActive["Max"] :=
	Module[ {res},
		First[ res] /; (res = max[ {e}, ord]; Length[ res] === 1)
	]
Tuple$TM /: min$TM[ Tuple$TM[ e__]] /; buiActive["Min"] :=
	Module[ {s},
		(s /. Min -> min$TM /. {min$TM[x_Tuple$TM] :> min$TM[x], min$TM[x___] :> min$TM[Tuple$TM[x]]}) /; (s = Min[ e]; Apply[ Hold, {s}] =!= Hold[ Min[ e]])
	]
Tuple$TM /: Subscript$TM[ min$TM, ord_][ Tuple$TM[ e__]] /; buiActive["Min"] :=
	Module[ {res},
		First[ res] /; (res = min[ {e}, ord]; Length[ res] === 1)
	]

Tuple$TM /: BracketingBar$TM[ a_Tuple$TM?isSequenceFree] /; buiActive["Length"] := Length[ a]

Tuple$TM /: ReplacePart$TM[ a_Tuple$TM?isSequenceFree, p:Tuple$TM[_, _]..] /; buiActive["ReplacePart"] :=
	ReplacePart[ a, MapAt[# /. {Tuple$TM -> List}&, Replace[ {p}, Tuple$TM[ l_, r_] :> Rule[ l, r], {1}], Table[ {i, 1}, {i, Length[{p}]}]]]

Tuple$TM /: Replace$TM[ a_Tuple$TM?isGround, s:Tuple$TM[_?isGround, _]..] /; buiActive["Replace"] :=
	Fold[ ReplaceAll, a, Replace[ {s}, Tuple$TM[ l_, r_] :> Rule[ l, r], {1}]]

Tuple$TM /: Subscript$TM[ a_Tuple$TM, p__Integer] /; buiActive["Subscript"] := Subscript$TM[ a, Tuple$TM[ p]]
Tuple$TM /: Subscript$TM[ a_Tuple$TM?isSequenceFree, p_?isPositionSpec] /; buiActive["Subscript"] := Extract[ a, p /. Tuple$TM -> List] /. List -> Tuple$TM

isPositionSpec[ _Integer] := True
isPositionSpec[ Tuple$TM[ p__]] := Apply[ And, Map[ isPositionSpec, {p}]]
isPositionSpec[ _] := False
isPositionSpec[ args___] := unexpected[ isPositionSpec, {args}]



(* ::Section:: *)
(* Data Types *)

isInteger$TM[ a_] /; buiActive["isInteger"] := isInteger[ a]
isRational$TM[ a_] /; buiActive["isRational"] := isRational[ a]
isReal$TM[ a_] /; buiActive["isReal"] := isReal[ a]
isComplex$TM[ a_] /; buiActive["isComplex"] := isComplex[ a]
isComplexP$TM[ a_] /; buiActive["isComplexP"] := isComplexP[ a]
isSet$TM[ a_] /; buiActive["isSet"] := isSet[ a]
isTuple$TM[ a_] /; buiActive["isTuple"] := isTuple[ a]


isInteger[ _Integer] := True
isInteger[ _Rational|_Real|_Complex|_DirectedInfinity] := False
isInteger[ _Set$TM|_Tuple$TM] := False
isInteger[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___]] /; buiActive[StringDrop[SymbolName[h],-3]] := False
isInteger[ h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive[StringDrop[SymbolName[h],-3]] := False
(* isInteger[ built-in symbolic constant ] := False ... same also for isRational, isReal, etc., but don't simply enumerate all symbolic constants! *)

isRational[ _Integer|_Rational] := True
isRational[ _Real|_Complex|_DirectedInfinity] := False
isRational[ _Set$TM|_Tuple$TM] := False
isRational[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___]] /; buiActive[StringDrop[SymbolName[h],-3]] := False
isRational[ h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive[StringDrop[SymbolName[h],-3]] := False
(* it is not known whether Catalan is rational, therefore we leave "isRational[Catalan]" unevaluated *)
isRational[ a:Except[Catalan]] /; AtomQ[ a] && isGround[ a] := False

isReal[ _Integer|_Rational|_Real] := True
isReal[ Pi|Degree|GoldenRatio|E|EulerGamma|Catalan|Khinchin|Glaisher] := True
isReal[ _Complex|_DirectedInfinity] := False
isReal[ _Set$TM|_Tuple$TM] := False
isReal[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___]] /; buiActive[StringDrop[SymbolName[h],-3]] := False
(* isReal[ h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive[StringDrop[SymbolName[h],-3]] := False *)
isReal[ a_?AtomQ] /; isGround[ a] := False

isComplex[ _Integer|_Rational|_Real|_Complex] := True
isComplex[ I|Pi|Degree|GoldenRatio|E|EulerGamma|Catalan|Khinchin|Glaisher] := True
isComplex[ _Set$TM|_Tuple$TM|_DirectedInfinity] := False
isComplex[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___]] /; buiActive[StringDrop[SymbolName[h],-3]] := False
(* isComplex[ h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive[StringDrop[SymbolName[h],-3]] := False *)
isComplex[ a_?AtomQ] /; isGround[ a] := False

isComplexP[ Tuple$TM[ a_, b_]] := isReal[ a] && isReal[ b] && a >= 0
isComplexP[ _Integer|_Rational|_Real|_Complex|_Set$TM|_Tuple$TM|_DirectedInfinity] := False
isComplexP[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___]] /; buiActive[StringDrop[SymbolName[h],-3]] := False
(* isComplexP[ h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive[StringDrop[SymbolName[h],-3]] := False *)
isComplexP[ a_?AtomQ] /; isGround[ a] := False

isSet[ _Set$TM] := True
isSet[ _Integer|_Rational|_Real|_Complex|_DirectedInfinity] := False
isSet[ _Tuple$TM] := False
isSet[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___]] /; buiActive[StringDrop[SymbolName[h],-3]] := True
(* isSet[ h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive[StringDrop[SymbolName[h],-3]] := True *)
isSet[ a_?AtomQ] /; isGround[ a] := False

isTuple[ _Tuple$TM] := True
isTuple[ _Integer|_Rational|_Real|_Complex|_DirectedInfinity] := False
isTuple[ _Set$TM] := False
isTuple[ (h:(IntegerInterval$TM|RationalInterval$TM|RealInterval$TM|IntegerQuotientRing$TM|IntegerQuotientRingPM$TM))[ ___]] /; buiActive[StringDrop[SymbolName[h],-3]] := False
(* isTuple[ h:(\[DoubleStruckCapitalC]$TM|\[DoubleStruckCapitalC]P$TM)] /; buiActive[StringDrop[SymbolName[h],-3]] := False *)
isTuple[ a_?AtomQ] /; isGround[ a] := False


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
Piecewise$TM[ Tuple$TM[ Tuple$TM[ expr_, True], ___Tuple$TM]] := expr
Piecewise$TM[ Tuple$TM[ clauses__Tuple$TM]] :=
	Module[ {res},
		Replace[ res, {Hold[ c___]:>Piecewise$TM[ Tuple$TM[ c]]}] /; (res = pw[ Hold[ clauses], Hold[]]; res =!= Hold[ clauses])	
	]
	
pw[ Hold[ Tuple$TM[ expr_, cond_], clauses___Tuple$TM], unknown:Hold[ u___]] :=
	Module[ {c = cond},
		If[ c,
			(*True*)
			Hold[ u, Tuple$TM[ expr, True]],
			(*False*)
			pw[ Hold[ clauses], unknown],
			(*unknown*)
			pw[ Hold[ clauses], ReplacePart[ Hold[ u, Tuple$TM[ expr, Null]], {-1, 2} -> c]]
		]	
	]
pw[ Hold[], unknown_Hold] := unknown
	


(* We assume that all lists not treated by the above constructs should in fact be sets *)
SetAttributes[ List$TM, HoldAll]
List$TM[ l___] := makeSet[l]

cleanupComputation[]
    
End[]
EndPackage[]
