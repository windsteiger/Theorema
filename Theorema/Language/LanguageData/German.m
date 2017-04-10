(* Theorema 
    Copyright (C) 1995-2014 The Theorema Group

    This file is part of Theorema 2.0
    
    Theorema 2.0 is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Theorema 2.0 is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program. If not, see <http://www.gnu.org/licenses/>.
*)

(*
   *********************************************************************************************
   -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- 
   *********************************************************************************************
 
     If you modify this file, then a new entry must have been added to the file "English"
     in this directory already.

     In this file, either
      1) copy the english entry into the section named "UNTRANSLATED" at the end of this file 
	       or
      2) translate the english entry and add it in correct alphabetical order here 
         (case-insensitive).
      
   *********************************************************************************************
   -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- 
   *********************************************************************************************
 *)

With[ {lang = "German"},

(* TRANSLATED *)
	MessageName[ ABBRVRNG$, "usage", lang] = "ABBRVRNG$[ a, e] steht daf\[UDoubleDot]r, dass a als Abk\[UDoubleDot]rzung f\[UDoubleDot]r e steht (in einem where-Ausdruck).";
    MessageName[ appendElem$TM, "usage", lang] = "appendElem[ T, e] h\[ADoubleDot]ngt e in einem Tupel T am Ende an (geschrieben \!\(T \"\:293a\" e\))";	

	MessageName[ domainConstruct$TM, "usage", lang] = "domainConstruct$TM[ dom, rng] ist eine Datenstruktur f\[UDoubleDot]r einen Domain-Konstruktor f\[UDoubleDot]r einen Bereich dom, der f\[UDoubleDot]r jenen Bereich rng steht, f\[UDoubleDot]r den \[Ellipsis].";
	MessageName[ DOMEXTRNG$, "usage", lang] = "DOMEXTRNG$[ x, dom] ist ein Laufbereich f\[UDoubleDot]r eine Variable x die den Bereich dom erweitert (in einer domain-extension Definition).";

    MessageName[ elemTuple$TM, "usage", lang] = "elemTuple[ e, T] testet, ob e im Tupel T enthalten ist (geschrieben \!\(e \"\:22ff\" T\))";	

	MessageName[ globalAbbrev$TM, "usage", lang] = "globalWhere$TM[ rng, cond, decl] ist eine Datenstruktur f\[UDoubleDot]r globale Abk\[UDoubleDot]rzungen. decl kann weitere Globale enthalten.  globalWhere$TM[ rng, cond] ist eine einzige globale Abk\[UDoubleDot]rzung.";
	MessageName[ globalForall$TM, "usage", lang] = "globalForall$TM[ rng, cond, decl] ist eine Datenstruktur f\[UDoubleDot]r eine globale universal quantifizierte Variable. decl kann weitere Globale enthalten.  globalForall$TM[ rng, cond] ist eine einzige globale universal quantifizierte Variable.";
	MessageName[ globalImplies$TM, "usage", lang] = "globalImplies$TM[ cond, decl] ist eine Datenstruktur f\[UDoubleDot]r eine globale Bedingung. decl kann weitere Globale enthalten. globalImplies$TM[ cond] ist eine einzige globale Bedingung.";

    MessageName[ joinTuples$TM, "usage", lang] = "joinTuples[ T, S] verbindet die Tupel T und S (geschrieben \!\(T \"\:22c8\" S\))";	

	MessageName[ PREDRNG$, "usage", lang] = "PREDRNG$[ x, p] steht f\[UDoubleDot]r einen Laufbereich einer Variablen x, die das Pr\[ADoubleDot]dikat p erf\[UDoubleDot]llt.";
    MessageName[ prependElem$TM, "usage", lang] = "prependElem[ T, e] h\[ADoubleDot]ngt e in einem Tupel T am Beginn an (geschrieben \!\(T \"\:293b\" e\))";	

	MessageName[ QU$, "usage", lang] = "QU$[ expr] markiert zwischenzeitlich im Parsing eine quantifierte Variable im Ausdruck e.";

	MessageName[ SETRNG$, "usage", lang] = "SETRNG$[ x, s] steht f\[UDoubleDot]r einen Laufbereich einer Variablen x, die \[UDoubleDot]ber die Menge s reicht.";
	MessageName[ SIMPRNG$, "usage", lang] = "SIMPRNG$[ x] steht f\[UDoubleDot]r einen einfachen Laufbereich einer Variablen x, die \[UDoubleDot]ber das gesamte Universum reicht.";
	MessageName[ STEPRNG$, "usage", lang] = "STEPRNG$[ x, low, high, step] steht f\[UDoubleDot]r einen einfachen Laufbereich einer Variablen x, die von low bis high in Schritten von step reicht.";

(* UNTRANSLATED *)	
	MessageName[ Abbrev$TM, "usage", lang] = "";
	MessageName[ \[AE]$TM, "usage", lang] = "";
	MessageName[ And$TM, "usage", lang] = "";
	MessageName[ angleBracketted$TM, "usage", lang] = "";	
	MessageName[ Annotated$TM, "usage", lang] = "";
	MessageName[ ArgMax$TM, "usage", lang] = "";
	MessageName[ ArgMin$TM, "usage", lang] = "";
	MessageName[ Assign$TM, "usage", lang] = "";	

    MessageName[ Backslash$TM, "usage", lang] = "";
    MessageName[ barAngleBracketted$TM, "usage", lang] = "";
    MessageName[ barParenthesized$TM, "usage", lang] = "";
    MessageName[ barSlantBracketted$TM, "usage", lang] = "";
	MessageName[ braced$TM, "usage", lang] = "";
	MessageName[ BracketingBar$TM, "usage", lang] = "";

	MessageName[ Componentwise$TM, "usage", lang] = "";
	MessageName[ CompoundExpression$TM, "usage", lang] = "";
    MessageName[ Cross$TM, "usage", lang] = "";
    MessageName[ curveAngleBracketted$TM, "usage", lang] = "";

	MessageName[ DeleteAt$TM, "usage", lang] = "";
	MessageName[ Delete$TM, "usage", lang] = "";
	MessageName[ Divide$TM, "usage", lang] = "";
	MessageName[ Do$TM, "usage", lang] = "";
	MessageName[ dotAngleBracketted$TM, "usage", lang] = "";
	MessageName[ doubleAngleBracketted$TM, "usage", lang] = "";
	MessageName[ doubleBraced$TM, "usage", lang] = "";
	MessageName[ doubleParenthesized$TM, "usage", lang] = "";
	MessageName[ doubleSquareBracketted$TM, "usage", lang] = "";
	MessageName[ \[DoubleStruckCapitalC]P$TM, "usage", lang] = "";
	MessageName[ \[DoubleStruckCapitalC]$TM, "usage", lang] = "";	
	MessageName[ \[DoubleStruckCapitalN], "usage", lang] = "";	
	MessageName[ \[DoubleStruckCapitalQ], "usage", lang] = "";	
	MessageName[ \[DoubleStruckCapitalR], "usage", lang] = "";	
	MessageName[ \[DoubleStruckCapitalZ], "usage", lang] = "";	

	MessageName[ Element$TM, "usage", lang] = "";
    MessageName[ EmptyUpTriangle$TM, "usage", lang] = "";
	MessageName[ EqualDef$TM, "usage", lang] = "";
	MessageName[ Equal$TM, "usage", lang] = "";
	MessageName[ Exists$TM, "usage", lang] = "";
	MessageName[ ExistsUnique$TM, "usage", lang] = "";

	MessageName[ Factorial$TM, "usage", lang] = "";
	MessageName[ FIX$, "usage", lang] = "";
	MessageName[ Forall$TM, "usage", lang] = "";
	MessageName[ For$TM, "usage", lang] = "";	

	MessageName[ GreaterEqual$TM, "usage", lang] = "";
	MessageName[ Greater$TM, "usage", lang] = "";

	MessageName[ IffDef$TM, "usage", lang] = "";
	MessageName[ Iff$TM, "usage", lang] = "";
	MessageName[ If$TM, "usage", lang] = "";	
	MessageName[ Implies$TM, "usage", lang] = "";
	MessageName[ Insert$TM, "usage", lang] = "";
	MessageName[ IntegerInterval$TM, "usage", lang] = "";			
	MessageName[ IntegerQuotientRingPM$TM, "usage", lang] = "";
	MessageName[ IntegerQuotientRing$TM, "usage", lang] = "";
	MessageName[ IntegralOf$TM, "usage", lang] = "";
	MessageName[ IntersectionOf$TM, "usage", lang] = "";
    MessageName[ Intersection$TM, "usage", lang] = "";
	MessageName[ isComplexP$TM, "usage", lang] = "";
	MessageName[ isComplex$TM, "usage", lang] = "";
	MessageName[ isInteger$TM, "usage", lang] = "";
	MessageName[ isRational$TM, "usage", lang] = "";
	MessageName[ isReal$TM, "usage", lang] = "";
	MessageName[ isSet$TM, "usage", lang] = "";
	MessageName[ isTuple$TM, "usage", lang] = "";

	MessageName[ Lambda$TM, "usage", lang] = "";
	MessageName[ LessEqual$TM, "usage", lang] = "";
	MessageName[ Less$TM, "usage", lang] = "";
	MessageName[ List$TM, "usage", lang] = "";

	MessageName[ MaximumOf$TM, "usage", lang] = "";
    MessageName[ max$TM, "usage", lang] = "";
	MessageName[ META$, "usage", lang] = "";
	MessageName[ MinimumOf$TM, "usage", lang] = "";	
	MessageName[ min$TM, "usage", lang] = "";	
	MessageName[ Minus$TM, "usage", lang] = "";
	MessageName[ Module$TM, "usage", lang] = "";	

	MessageName[ Not$TM, "usage", lang] = "";

	MessageName[ opDefInDom, "usage", lang] = "opDefInDom[ d] ist eine Liste der in d definierten Operationen.";
	MessageName[ OperatorChain$TM, "usage", lang] = "";
	MessageName[ Or$TM, "usage", lang] = "";
	MessageName[ OverScript$TM, "usage", lang] = "";

	MessageName[ parenthesized$TM, "usage", lang] = "";	
	MessageName[ Piecewise$TM, "usage", lang] = "";
	MessageName[ Plus$TM, "usage", lang] = "";
	MessageName[ Power$TM, "usage", lang] = "";
	MessageName[ ProductOf$TM, "usage", lang] = "";
	MessageName[ Program, "usage", lang] = "";	

	MessageName[ Radical$TM, "usage", lang] = "";
	MessageName[ RationalInterval$TM, "usage", lang] = "";	
	MessageName[ RealInterval$TM, "usage", lang] = "";	
    MessageName[ ReplacePart$TM, "usage", lang] = "";	
    MessageName[ Replace$TM, "usage", lang] = "";	
	MessageName[ RNG$, "usage", lang] = "";

    MessageName[ \[ScriptCapitalP]$TM, "usage", lang] = "";
    MessageName[ SEQ$, "usage", lang] = "SEQ$[ exprs] represents a sequence of expressions, similar to \"Sequence\" in Mathematica.";
	MessageName[ SEQ0$, "usage", lang] = "";
	MessageName[ SEQ1$, "usage", lang] = "";
	MessageName[ SequenceOf$TM, "usage", lang] = "";	
	MessageName[ SetDelayed$TM, "usage", lang] = "";	
	MessageName[ SetEqual$TM, "usage", lang] = "";
	MessageName[ SetOf$TM, "usage", lang] = "";	
	MessageName[ Set$TM, "usage", lang] = "";	
	MessageName[ squareBracketted$TM, "usage", lang] = "";	
	MessageName[ SubScript$TM, "usage", lang] = "";
	MessageName[ Subscript$TM, "usage", lang] = "";	
    MessageName[ SubsetEqual$TM, "usage", lang] = "";
    MessageName[ Subset$TM, "usage", lang] = "";
	MessageName[ Subtract$TM, "usage", lang] = "";
	MessageName[ Such$TM, "usage", lang] = "";
	MessageName[ SuchUnique$TM, "usage", lang] = "";
	MessageName[ SumOf$TM, "usage", lang] = "";
	MessageName[ SuperScript$TM, "usage", lang] = "";
    MessageName[ SupersetEqual$TM, "usage", lang] = "";
    MessageName[ Superset$TM, "usage", lang] = "";
	MessageName[ Switch$TM, "usage", lang] = "";	

	MessageName[ TAG$, "usage", lang] = "";
	MessageName[ TheArgMax$TM, "usage", lang] = "";
	MessageName[ TheArgMin$TM, "usage", lang] = "";
	MessageName[ Times$TM, "usage", lang] = "";
	MessageName[ TupleOf$TM, "usage", lang] = "";	
	MessageName[ Tuple$TM, "usage", lang] = "";	

	MessageName[ UnderScript$TM, "usage", lang] = "";
    MessageName[ UnionOf$TM, "usage", lang] = "";
	MessageName[ Union$TM, "usage", lang] = "";

	MessageName[ VAR$, "usage", lang] = "";

	MessageName[ Which$TM, "usage", lang] = "";	
	MessageName[ While$TM, "usage", lang] = "";	
]

