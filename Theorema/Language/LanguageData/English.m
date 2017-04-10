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
 
     If you modify this file, then insert the new translation in correct alphabetical 
     order (case-insensitive).

     ALSO, YOU MUST add a corresponding entry for each other language, either
      1) in the section named "UNTRANSLATED" at the end of the language file 
         (in case you cannot or do not want to provide a translation) or
      2) in correct alphabetical order (case-insensitive) in case you immediately provide 
         a translation.
      
   *********************************************************************************************
   -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- 
   *********************************************************************************************
 *)
 
With[ {lang = "English"},
	
	MessageName[ Abbrev$TM, "usage", lang] = "";
	MessageName[ ABBRVRNG$, "usage", lang] = "ABBRVRNG$[ a, e] denotes that the variable a abbreviates expression e (in a where-expression).";
	MessageName[ \[AE]$TM, "usage", lang] = "";
	MessageName[ And$TM, "usage", lang] = "";
	MessageName[ angleBracketted$TM, "usage", lang] = "";	
	MessageName[ Annotated$TM, "usage", lang] = "";
    MessageName[ appendElem$TM, "usage", lang] = "appendElem[ T, e] appends to tuple T the element e (written \!\(T \"\:293a\" e\))";	
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
	MessageName[ domainConstruct$TM, "usage", lang] = "domainConstruct$TM[ dom, rng] is a datastructure representing a domain constructor for domain dom being 'the rng such that ...'.";
	MessageName[ DomainOperation$TM, "usage", lang] = "";
	MessageName[ DOMEXTRNG$, "usage", lang] = "DOMEXTRNG$[ x, dom] denotes that the variable x extends domain dom (in a domain extension definition).";
	MessageName[ Do$TM, "usage", lang] = "";
	MessageName[ dotAngleBracketted$TM, "usage", lang] = "";
	MessageName[ doubleAngleBracketted$TM, "usage", lang] = "";
	MessageName[ doubleBraced$TM, "usage", lang] = "";
	MessageName[ DoubleLeftArrow$TM, "usage", lang] = "";
	MessageName[ doubleParenthesized$TM, "usage", lang] = "";
	MessageName[ doubleSquareBracketted$TM, "usage", lang] = "";
	MessageName[ \[DoubleStruckCapitalC]P$TM, "usage", lang] = "";
	MessageName[ \[DoubleStruckCapitalC]$TM, "usage", lang] = "";	
	MessageName[ \[DoubleStruckCapitalN], "usage", lang] = "";	
	MessageName[ \[DoubleStruckCapitalQ], "usage", lang] = "";	
	MessageName[ \[DoubleStruckCapitalR], "usage", lang] = "";	
	MessageName[ \[DoubleStruckCapitalZ], "usage", lang] = "";	

	MessageName[ Element$TM, "usage", lang] = "";
    MessageName[ elemTuple$TM, "usage", lang] = "elemTuple[ e, T] tests whether e is contained in T (written \!\(e \"\:22ff\" T\))";	
    MessageName[ EmptyUpTriangle$TM, "usage", lang] = "";
	MessageName[ EqualDef$TM, "usage", lang] = "";
	MessageName[ Equal$TM, "usage", lang] = "";
	MessageName[ Exists$TM, "usage", lang] = "";
	MessageName[ ExistsUnique$TM, "usage", lang] = "";

	MessageName[ Factorial$TM, "usage", lang] = "";
	MessageName[ FIX$, "usage", lang] = "";
	MessageName[ Forall$TM, "usage", lang] = "";
	MessageName[ For$TM, "usage", lang] = "";	

	MessageName[ globalAbbrev$TM, "usage", lang] = "globalWhere$TM[ rng, cond, decl] is a datastructure representing a (nested) global abbreviation, where decl contains further global declarations. globalWhere$TM[ rng, cond] is a single global abbreviation.";
	MessageName[ globalForall$TM, "usage", lang] = "globalForall$TM[ rng, cond, decl] is a datastructure representing a (nested) global universal variable, where decl contains further global declarations. globalForall$TM[ rng, cond] is a single global universal variable.";
	MessageName[ globalImplies$TM, "usage", lang] = "globalImplies$TM[ cond, decl] is a datastructure representing a (nested) global condition, wheredecl contains further global declarations. globalImplies$TM[ cond] is a single global condition.";
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

    MessageName[ joinTuples$TM, "usage", lang] = "joinTuples[ T, S] joins the tuples T and S (written \!\(T \"\:22c8\" S\))";	

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

	MessageName[ Nand$TM, "usage", lang] = "";
	MessageName[ Nor$TM, "usage", lang] = "";
	MessageName[ NotElement$TM, "usage", lang] = "";
	MessageName[ NotExists$TM, "usage", lang] = "";
	MessageName[ NotGreaterEqual$TM, "usage", lang] = "";
	MessageName[ NotGreater$TM, "usage", lang] = "";
	MessageName[ NotLessEqual$TM, "usage", lang] = "";
	MessageName[ NotLess$TM, "usage", lang] = "";
	MessageName[ NotReverseElement$TM, "usage", lang] = "";
    MessageName[ NotSubsetEqual$TM, "usage", lang] = "";
    MessageName[ NotSubset$TM, "usage", lang] = "";
    MessageName[ NotSupersetEqual$TM, "usage", lang] = "";
    MessageName[ NotSuperset$TM, "usage", lang] = "";
	MessageName[ Not$TM, "usage", lang] = "";

	MessageName[ opDefInDom, "usage", lang] = "opDefInDom[ d] is a list of the operations defined in d.";
	MessageName[ OperatorChain$TM, "usage", lang] = "";
	MessageName[ Or$TM, "usage", lang] = "";
	MessageName[ OverScript$TM, "usage", lang] = "";

	MessageName[ parenthesized$TM, "usage", lang] = "";	
	MessageName[ Piecewise$TM, "usage", lang] = "";
	MessageName[ Plus$TM, "usage", lang] = "";
	MessageName[ Power$TM, "usage", lang] = "";
	MessageName[ PREDRNG$, "usage", lang] = "PREDRNG$[ x, p] denotes that the variable x satisfies the predicate p.";
    MessageName[ prependElem$TM, "usage", lang] = "prependElem[ T, e] prepends to tuple T the element e (written \!\(T \"\:293b\" e\))";	
	MessageName[ ProductOf$TM, "usage", lang] = "";
	MessageName[ Program, "usage", lang] = "";	

	MessageName[ QU$, "usage", lang] = "QU$[ expr] temporarily marks quantified variables in expr.";

	MessageName[ Radical$TM, "usage", lang] = "";
	MessageName[ RationalInterval$TM, "usage", lang] = "";	
	MessageName[ RealInterval$TM, "usage", lang] = "";	
    MessageName[ ReplacePart$TM, "usage", lang] = "";	
    MessageName[ Replace$TM, "usage", lang] = "";	
	MessageName[ ReverseElement$TM, "usage", lang] = "";
	MessageName[ RNG$, "usage", lang] = "";

    MessageName[ \[ScriptCapitalP]$TM, "usage", lang] = "";
    MessageName[ SEQ$, "usage", lang] = "SEQ$[ exprs] represents a sequence of expressions, similar to \"Sequence\" in Mathematica.";
	MessageName[ SEQ0$, "usage", lang] = "";
	MessageName[ SEQ1$, "usage", lang] = "";
	MessageName[ SequenceOf$TM, "usage", lang] = "";	
	MessageName[ SetDelayed$TM, "usage", lang] = "";	
	MessageName[ SetEqual$TM, "usage", lang] = "";
	MessageName[ SetOf$TM, "usage", lang] = "";	
	MessageName[ SETRNG$, "usage", lang] = "SETRNG$[ x, s] denotes that the variable x ranges over the set s.";
	MessageName[ Set$TM, "usage", lang] = "";	
	MessageName[ SIMPRNG$, "usage", lang] = "SIMPRNG$[ x] usually denotes that the variable x ranges over the universe.";
	MessageName[ squareBracketted$TM, "usage", lang] = "";	
	MessageName[ STEPRNG$, "usage", lang] = "STEPRNG$[ x, low, high, step] denotes that the variable x steps from low to high in steps of step.";
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
 	MessageName[ Unequal$TM, "usage", lang] = "";
	MessageName[ UnionOf$TM, "usage", lang] = "";
	MessageName[ Union$TM, "usage", lang] = "";

	MessageName[ VAR$, "usage", lang] = "";

	MessageName[ Which$TM, "usage", lang] = "";	
	MessageName[ While$TM, "usage", lang] = "";	

	MessageName[ Xnor$TM, "usage", lang] = "";
	MessageName[ Xor$TM, "usage", lang] = "";
]

