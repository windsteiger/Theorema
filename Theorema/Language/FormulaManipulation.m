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

BeginPackage["Theorema`Language`FormulaManipulation`"]

Needs[ "Theorema`Common`"]

Begin["`Private`"]

makeConjunction[ h_[ x___], a_] :=
    Switch[ Length[ {x}],
            0,
            True,
            1,
            If[ isIndividual[ x],
            	x,
            	a[ x]
            ],
            _,
            a[ x]
        ]
makeConjunction[ args___] := unexpected[ makeConjunction, {args}]

makeDisjunction[ h_[ x___], a_] :=
    Switch[ Length[ {x}],
            0,
            False,
            1,
            If[ isIndividual[ x],
            	x,
            	a[ x]
            ],
            _,
            a[ x]
        ]
makeDisjunction[ args___] := unexpected[ makeDisjunction, {args}]


(* ::Subsubsection:: *)
(* simplifiedAnd *)

simplifiedAnd[ expr:Hold[ True|False]] := expr
simplifiedAnd[ Hold[ h_[ True...]]] := Hold[ True]
simplifiedAnd[ Hold[ h_[ ___, False, ___]]] := Hold[ False]
simplifiedAnd[ expr_Hold] :=  
	Module[ {simp = expr //. {(h:(Theorema`Language`And$TM|Theorema`Computation`Language`And$TM))[pre___, True, post___] :> h[pre, post],
								(h:(Theorema`Language`And$TM|Theorema`Computation`Language`And$TM))[pre___, (Theorema`Language`And$TM|Theorema`Computation`Language`And$TM)[ mid___], post___] :> h[pre, mid, post],
								(Theorema`Language`And$TM|Theorema`Computation`Language`And$TM)[a_] /; isIndividual[ HoldComplete[ a]] :> a}},
		If[ MatchQ[ simp, Hold[ (Theorema`Language`And$TM|Theorema`Computation`Language`And$TM)[]]],
			Hold[ True],
			simp
		]
	]
(* If we simplify an non-Hold And, we wrap it in Hold and RealeaseHold afterwards *)
simplifiedAnd[ expr:Except[ _Hold]] := ReleaseHold[ simplifiedAnd[ Hold[ expr]]]
simplifiedAnd[ args___] := unexpected[ simplifiedAnd, {args}]

(* ::Subsubsection:: *)
(* simplifiedOr *)

simplifiedOr[ expr:Hold[ True|False]] := expr
simplifiedOr[ Hold[ h_[ False...]]] := Hold[ False]
simplifiedOr[ Hold[ h_[ ___, True, ___]]] := Hold[ True]
simplifiedOr[ expr_Hold] :=  
	Module[ {simp = expr //. {(h:(Theorema`Language`Or$TM|Theorema`Computation`Language`Or$TM))[pre___, False, post___] :> h[pre, post],
								(h:(Theorema`Language`Or$TM|Theorema`Computation`Language`Or$TMM))[pre___, (Theorema`Language`Or$TM|Theorema`Computation`Language`Or$TM)[ mid___], post___] :> h[pre, mid, post],
								(Theorema`Language`Or$TM|Theorema`Computation`Language`Or$TMM)[a_] /; isIndividual[ HoldComplete[ a]] :> a}},
		If[ MatchQ[ simp, Hold[ (Theorema`Language`Or$TM|Theorema`Computation`Language`Or$TM)[]]],
			Hold[ False],
			simp
		]
	]
(* If we simplify an non-Hold Or, we wrap it in Hold and RealeaseHold afterwards *)
simplifiedOr[ expr:Except[ _Hold]] := ReleaseHold[ simplifiedOr[ Hold[ expr]]]
simplifiedOr[ args___] := unexpected[ simplifiedOr, {args}]


(* ::Subsubsection:: *)
(* simplifiedImplies *)

(* amaletzk: None of the following 'simplified...' gets a 'Hold'-definition, because all of them are only
	defined for symbols in "Theorema`Language`" context, and not for "Theorema`Computation`Language`".
	If this changes, then they should also get 'Hold'-definitions. *)

simplifiedImplies[ Theorema`Language`Implies$TM[ True, A_?isIndividual]] := A
simplifiedImplies[ Theorema`Language`Implies$TM[ False, _?isIndividual]] := True
simplifiedImplies[ Theorema`Language`Implies$TM[ _?isIndividual, True]] := True
simplifiedImplies[ Theorema`Language`Implies$TM[ A_?isIndividual, Theorema`Language`Implies$TM[ B_?isIndividual, C_?isIndividual]]] :=
	simplifiedImplies[ Theorema`Language`Implies$TM[ simplifiedAnd[ Theorema`Language`And$TM[ A, B]], C]]
simplifiedImplies[ i_Theorema`Language`Implies$TM] := i
simplifiedImplies[ args___] := unexpected[ simplifiedImplies, {args}]

(* ::Subsubsection:: *)
(* simplifiedNot *)

simplifiedNot[ Theorema`Language`Not$TM[ Theorema`Language`Not$TM[ A_?isIndividual]]] := A
simplifiedNot[ Theorema`Language`Not$TM[ Theorema`Language`And$TM[ A__?isIndividual]]] := Apply[ Theorema`Language`Or$TM, Map[ Theorema`Language`Not$TM, {A}]]
simplifiedNot[ Theorema`Language`Not$TM[ Theorema`Language`Or$TM[ A__?isIndividual]]] := Apply[ Theorema`Language`And$TM, Map[ Theorema`Language`Not$TM, {A}]]
simplifiedNot[ Theorema`Language`Not$TM[ Theorema`Language`Implies$TM[ A_?isIndividual, B_?isIndividual]]] := Theorema`Language`And$TM[ A, Theorema`Language`Not$TM[ B]]
simplifiedNot[ Theorema`Language`Not$TM[ Theorema`Language`Iff$TM[ A_?isIndividual, B_?isIndividual]]] :=
	Theorema`Language`Or$TM[ Theorema`Language`And$TM[ A, Theorema`Language`Not$TM[ B]], Theorema`Language`And$TM[ B, Theorema`Language`Not$TM[ A]]]
simplifiedNot[ n_Theorema`Language`Not$TM] := n
simplifiedNot[ args___] := unexpected[ simplifiedNot, {args}]

(* ::Subsubsection:: *)
(* simplifiedForall *)

simplifiedForall[ Theorema`Language`Forall$TM[ Theorema`Language`RNG$[], C_?isIndividual, A_?isIndividual]] := simplifiedImplies[ Theorema`Language`Implies$TM[ C, A]]
simplifiedForall[ f_Theorema`Language`Forall$TM] := f
simplifiedForall[ args___] := unexpected[ simplifiedForall, {args}]


(* ::Subsubsection:: *)
(* standardForm *)

standardFormQuantifier[ Theorema`Language`Forall$TM[ r1_Theorema`Language`RNG$, C1_, Theorema`Language`Forall$TM[ r2_Theorema`Language`RNG$, C2_, body_]]] :=
	standardFormQuantifier[ Theorema`Language`Forall$TM[ Join[ r1, r2], simplifiedAnd[ Theorema`Language`And$TM[ C1, C2]], body]]
standardFormQuantifier[ Theorema`Language`Forall$TM[ r_Theorema`Language`RNG$, C_?isIndividual, body_?isIndividual]] :=
	Theorema`Language`Forall$TM[ r, True, simplifiedImplies[ Theorema`Language`Implies$TM[ C, body]]]
standardFormQuantifier[ f_] := f
standardFormQuantifier[ args___] := unexpected[ standardFormQuantifier, {args}]

(* ::Subsubsection:: *)
(* thinnedExpression *)

thinnedExpression[ e_, drop_List] := Fold[ thinnedExpression, e, drop]
thinnedExpression[ e_, v_] := DeleteCases[ e, _?(!FreeQ[ #, v]&)]
thinnedExpression[ args___] := unexpected[ thinnedExpression, {args}]


(* ::Subsubsection:: *)
(* analyzeVars *)


(* 'analyzeVars[ expr]' returns the list of all variables occurring in 'expr', together with their positions.
	More precisely, every element of the output is of the form 'x -> {fp, {bp1 -> bl1, bp2 -> bl2, ...}}',
	where
	- 'x' is a variable,
	- 'fp' is the list of positions of all free occurrences of 'x' in 'expr',
	- the 'bpi' are those positions of occurrences of 'x' that are bound in the range of a variable-binder, and
	- the 'bli' are the lists of positions of all bound occurrences of 'x' in the scope of the respective 'bpi' (without 'bpi' itself).
	If the optional parameter "FreeOnly" is set to 'True', only the positions of the free occurrences of the variables are returned, i.e.
	the elements in the output are of the form 'x -> fp'.
	The optional parameter "Pattern" specifies the pattern of variables to consider. By default, all variables are considered,
	but one can tell the function to only analyze the positions of a particular variable by simply adjusting the value of "Pattern".
*)
Options[ analyzeVars] = {"FreeOnly" -> False, "Pattern" -> (_Theorema`Language`VAR$|_Theorema`Computation`Language`VAR$)};
analyzeVars[ expr_, opts___?OptionQ] :=
	Module[ {freeOnly, patt, varpos, pos, bp, fp},
		{freeOnly, patt} = {"FreeOnly", "Pattern"} /. {opts} /. Options[ analyzeVars];
		varpos = Position[ expr, patt];
		Replace[
			GatherBy[ MapThread[ Rule, {Extract[ expr, varpos], varpos}], First],
			all:{x_ -> _, ___} :>
			(
				pos = all[[All, 2]];
				(* 'x' is a variable occurring in 'expr', and 'pos' is the list of the positions of all its occurrences. *)
				
				bp = Sort[ Cases[ pos, {p__, _, 1} /; MatchQ[ Extract[ expr, {p, 0}, Hold], Hold[ Theorema`Language`RNG$|Theorema`Computation`Language`RNG$]]], OrderedQ[ {#2, #1}]&];
				(* 'bp' is the list of all positions of occurrences of 'x' that are bound in the range of a variable-binder.
					Sorting the list in reverse order ensures that any element 'p1' of 'bp' appearing in the scope of
					another element 'p2' of 'bp' comes *before* 'p2' in 'bp'. *)
				
				pos = Select[ pos, (!MemberQ[ bp, #])&];
				(* All elements of 'bp' are removed from 'pos'. *)
				
				If[ TrueQ[ freeOnly],
					(* The free occurrences of 'x' are precisely those that are not in the scope of any element of 'bp'. *)
					x -> Select[ pos, (!MemberQ[ bp, p_ /; inScope[ #, p]])&],
					
					pos = Map[ (# -> Cases[ bp, p_ /; inScope[ #, p], {1}, 1])&, pos];
					(* The elements of 'pos' are now of the form 'p -> {bpi}' or 'p -> {}',
						where the 'p' are the original elements of 'pos' and the 'bpi' are the elements of 'bp' in whose scope 'p' appears. *)
						
					fp = Cases[ pos, (p_ -> {}) :> p];
					(* The positions of the free occurrences of 'x' are precisely those that are not in the scope of any element of 'bp'. *)
					
					pos = Replace[ GatherBy[ Cases[ pos, (p_ -> {p0_}) :> (p0 -> p)], First], all0:{p0_ -> _, ___} :> (p0 -> all0[[All, 2]]), {1}];
					(* 'pos' is now precisely the list of bound occurrences of 'x', as described in the specification of the function, with the
						only exception that positions of bindings that do not have any other bound occurrences in their scope are still missing. *)
						
					bp = Join[ Cases[ bp, p_ /; !MemberQ[ pos, p -> _] :> (p -> {})], pos];
					
					x -> {fp, bp}
				]
			),
			{1}
		]
	]
analyzeVars[ args___] := unexpected[ analyzeVars, {args}]


(* ::Subsubsection:: *)
(* Sequence-related functions *)


sequenceFlatten[ expr:(hld:(Hold|HoldComplete))[ _]] :=
	Module[ {out, myHold, head = Null, rem = False},
		SetAttributes[ myHold, HoldAllComplete];
		out = expr //. {
							(seq:(Theorema`Language`SEQ$|Theorema`Computation`Language`SEQ$))[ s___][ a___] :>
								With[ {new = (head = seq; rem = True; Replace[ myHold[ s], x_ :> x[ a], {1}])}, new /; True],
							f_[ pre___, (seq:(Theorema`Language`SEQ$|Theorema`Computation`Language`SEQ$))[ a___], post___] :>
								f[ pre, a, post] /; (head = seq; True)
						};
		If[ head =!= Null,
			With[ {h = head},
				If[ rem, out = out /. myHold -> h];
				Switch[ out,
					hld[],
					out = hld[ h[]],
					hld[ _, __],
					out = ReplacePart[ hld @@ {out}, {1, 0} -> h]
				]
			]
		];
		out
	]
sequenceFlatten[ expr_] :=
	ReleaseHold[ sequenceFlatten[ HoldComplete[ expr]]]
sequenceFlatten[ args___] := unexpected[ sequenceFlatten, {args}]

	
(* 'isIndividual[ expr]' checks whether the given expression is an individual. *)
isIndividual[ expr_] := (sequenceType[ expr] === {1, True})
isIndividual[ args___] := unexpected[ isIndividual, {args}]


(* 'isNonEmptySequence[ expr]' checks whether the given expression is a non-empty sequence. *)
isNonEmptySequence[ expr_] := MatchQ[ sequenceType[ expr], {Except[ 0], _}]
isNonEmptySequence[ args___] := unexpected[ isNonEmptySequence, {args}]

	
sequenceTypeEqual[ a_, b_] :=
	sequenceTypeEqual[ a, b, True]
sequenceTypeEqual[ a_, b_, True] :=
	sequenceTypeEqual[ sequenceType[ a], sequenceType[ b], False]
sequenceTypeEqual[ t_, t_, False] :=
	t =!= $Failed
sequenceTypeEqual[ _, _, _] :=
	False
sequenceTypeEqual[ args___] := unexpected[ sequenceTypeEqual, {args}]

	
(* Example: For checking whether variable 'v' can be instantiated by expression 'e', use 'sequenceTypeMatchQ[ e, v]'. *)
sequenceTypeMatchQ[ a_, b_] :=
	sequenceTypeMatchQ[ a, b, True]
sequenceTypeMatchQ[ a_, b_, True] :=
	sequenceTypeMatchQ[ sequenceType[ a], sequenceType[ b], False]
sequenceTypeMatchQ[ t_, t_, False] :=
	t =!= $Failed
sequenceTypeMatchQ[ {m_Integer, _}, {n_Integer, False}, False] :=
	m >= n
sequenceTypeMatchQ[ _, _, _] :=
	False
sequenceTypeMatchQ[ args___] := unexpected[ sequenceTypeMatchQ, {args}]


(* ::Subsubsection:: *)
(* Auxiliary functions (private) *)

	
(* 'inScope[ p1, p2]' checkes whether the expression at position 'p1' appears in the scope of the variable
	bound at position 'p2', i.e. 'p2' is supposed to refer to the position of some variable 'x' in
	'RNG$[ ___, (SOMERNG$)[ x, rc___], ___]', meaning that the last element of 'p2' must be '1'.
	Note that occurrences of 'x' in 'rc' are still regarded free! *)
inScope[ p_List, p_List] := True
inScope[ {a___, b_, c___}, {a___, 1}] := (b === 1 && {c} === {})
inScope[ {a___, b_, ___}, {a___, c_, 1}] := b > c
inScope[ {a___, b_, ___}, {a___, 1, _, 1}] := b =!= 1
inScope[ _, _] := False
inScope[ args___] := unexpected[ inScope, {args}]

(* Each of the two functions below is defined for seemingly strange arguments of the 'VAR$'-symbol.
	This is because in higher-order rewriting ("HORewriting.m"), names of variables are made unique
	by adding additional indices, tags, etc. Although higher-order rewriting is not yet integrated
	into the system, the extended definitions given below certainly do not do any harm. *)

(* 'varName[ v_VAR$]' returns the base name of the given variable as a plain symbol. *)
varName[ (Theorema`Language`VAR$|Theorema`Computation`Language`VAR$)[ (n_Symbol)|{___, n_Symbol}, ___]] := n
varName[ (Theorema`Language`VAR$|Theorema`Computation`Language`VAR$)[ ((Except[ List])[ n_Symbol, ___])|{___, _[ n_Symbol, ___]}, ___]] := n
varName[ _] := $Failed
varName[ args___] := unexpected[ varName, {args}]

(* 'renameVar[ v_VAR$, new_Symbol]' renames the given variable, taking care of any 'SEQ0$' or 'SEQ1$'. *)
renameVar[ (v:(Theorema`Language`VAR$|Theorema`Computation`Language`VAR$))[ _Symbol, rest___], new_Symbol] :=
	v[ new, rest]
renameVar[ (v:(Theorema`Language`VAR$|Theorema`Computation`Language`VAR$))[ {pre___, _Symbol}, rest___], new_Symbol] :=
	v[ {pre, new}, rest]
renameVar[ (v:(Theorema`Language`VAR$|Theorema`Computation`Language`VAR$))[ ((h:Except[ List])[ _Symbol, rest1___]), rest2___], new_Symbol] :=
	v[ h[ new, rest1], rest2]
renameVar[ (v:(Theorema`Language`VAR$|Theorema`Computation`Language`VAR$))[ {pre___, h_[ _Symbol, rest1___]}, rest2___], new_Symbol] :=
	v[ {pre, h[ new, rest1]}, rest2]
renameVar[ old_, _] := old
renameVar[ args___] := unexpected[ renameVar, {args}]


(* ::Subsubsection:: *)
(* freeVariables and isFree *)


(* 'freeVariables[ expr]' returns the list of all variables appearing free in 'expr'. If 'expr' is wrapped
	in 'Hold', no unwanted simplification happens.
	In multi-ranges, every bound variable appears only once (this is enforced when inputting formulas).
	However, we do not rely on that in 'alphaEquivalent', 'freeVariables' and 'substituteFree'.
	In a variable-range '(SOMERNG$)[ x_VAR$, rest___]', the variable 'x' is still regarded free in 'rest';
	only afterward, in subsequent ranges and subsequent arguments of the enclosing binder (condition, matrix, ...)
	it is regarded bounded. *)
freeVariables[ expr_] :=
	Cases[ analyzeVars[ expr, "FreeOnly" -> True], (x_ -> {__}) :> x]
freeVariables[ args___] := unexpected[ freeVariables, {args}]

(* 'isFree[ var, expr]' is equivalent to, but in general more efficient than, 'MemberQ[ freeVars[ expr], var]'. *)
isFree[ var_, expr_] :=
	MemberQ[ analyzeVars[ expr, "FreeOnly" -> True, "Pattern" -> var], var -> {__}]
isFree[ args___] := unexpected[ isFree, {args}]


(* ::Subsubsection:: *)
(* alphaEquivalent *)


(* 'alphaEquivalent[ a, b]' checks whether the two given expressions 'a' and 'b' are alpha-equivalent
	to each other, i.e. identical up to renaming bound variables. No unwanted simplification happens.
	As in 'freeVariables', we do not rely on bound variables occurring only once in multi-ranges. *)
alphaEquivalent[ Theorema`Common`FML$[ _, a_, __], Theorema`Common`FML$[ _, b_, __]] :=
	alphaEquivalent[ Hold[ a], Hold[ b], {}]
alphaEquivalent[ a_Hold, b_Hold] :=
	alphaEquivalent[ a, b, {}]
alphaEquivalent[ a_, b_] :=
	alphaEquivalent[ Hold[ a], Hold[ b], {}]
alphaEquivalent[ Hold[ v1:(_Theorema`Language`VAR$|_Theorema`Computation`Language`VAR$)], b_, repl_List] :=
	MatchQ[ b, Hold[ _Theorema`Language`VAR$|_Theorema`Computation`Language`VAR$]] && Replace[ v1, repl] === First[ b]
alphaEquivalent[ _Hold, Hold[ _Theorema`Language`VAR$|_Theorema`Computation`Language`VAR$], _] :=
	False
alphaEquivalent[ Hold[ q1_[ (Theorema`Language`RNG$|Theorema`Computation`Language`RNG$)[ r___], a___]], b_Hold, repl_List] :=
	Switch[ b,
		Hold[ _[ _Theorema`Language`RNG$|_Theorema`Computation`Language`RNG$, ___]],
		With[ {a0 = Hold[ a], b0 = Rest[ First[ Hold @@@ b]]},
			If[ Length[ a0] === Length[ b0] && alphaEquivalent[ Hold[ q1], Extract[ b, {1, 0}, Hold], repl],
				With[ {r0 = List @@ Hold /@ Hold[ r], s0 = List @@ Hold /@ Extract[ ReplacePart[ b, {1, 1, 0} -> Hold], {1, 1}]},
					If[ Length[ r0] === Length[ s0],
						Module[ {newRules = repl},
							Catch[
								MapThread[
									Function[ {r1, s1},
										With[ {x = r1[[1, 1]], y = s1[[1, 1]]},
											(* We rely on the fact that EVERY variable-range is of the form '(SIMPRNG$|SETRNG$|...)[ _VAR$, ___]'. *)
											If[ sequenceTypeEqual[ x, y] && alphaEquivalent[ Delete[ r1, {1, 1}], Delete[ s1, {1, 1}], newRules],
												PrependTo[ newRules, x -> y];
												Null,
											(*else*)
												Throw[ False]
											]
										]
									],
									{r0, s0}
								];
								MapThread[
									If[ alphaEquivalent[ #1, #2, newRules], Null, Throw[ False]]&,
									{List @@ Hold /@ a0, List @@ Hold /@ b0}
								];
								True
							]
						],
					(*else*)
						False
					]
				],
			(*else*)
				False
			]
		],
		_,
		False
	]
alphaEquivalent[ _Hold, Hold[ _[ _Theorema`Language`RNG$|_Theorema`Computation`Language`RNG$, ___]], _List] :=
	False
alphaEquivalent[ Hold[ g_[ a___]], b_Hold, repl_List] :=
	Switch[ b,
		Hold[ _[ ___]],
		With[ {a0 = Hold[ a], b0 = First[ Hold @@@ b]},
			Length[ a0] === Length[ b0] &&
			alphaEquivalent[ Hold[ g], Extract[ b, {1, 0}, Hold], repl] &&
			Catch[ MapThread[ If[ alphaEquivalent[ #1, #2, repl], Null, Throw[ False]]&, {List @@ Hold /@ a0, List @@ Hold /@ b0}]; True]
		],
		_,
		False
	]
alphaEquivalent[ a_Hold, b_Hold, _List] :=
	a === b
alphaEquivalent[ _, _, _] :=
	False
alphaEquivalent[ args___] := unexpected[ alphaEquivalent, {args}]


(* ::Subsubsection:: *)
(* rngVariables *)

rngVariables[ Hold[(Theorema`Language`RNG$|Theorema`Computation`Language`RNG$)[r___]]] := Apply[ List, Hold[ r][[All, 1]]]
rngVariables[ (Theorema`Language`RNG$|Theorema`Computation`Language`RNG$)[r___]] := Map[ First, {r}]
rngVariables[ args___] := unexpected[ rngVariables, {args}]

(* ::Subsubsection:: *)
(* rngConstants *)

rngConstants[ Hold[(Theorema`Language`RNG$|Theorema`Computation`Language`RNG$)[r___]]] := Apply[ List, Hold[ r][[All, 1]]]
rngConstants[ (Theorema`Language`RNG$|Theorema`Computation`Language`RNG$)[r___]] := Map[ First, {r}]
rngConstants[ args___] := unexpected[ rngConstants, {args}]


(* ::Subsubsection:: *)
(* specifiedVariables *)

specifiedVariables[ Hold[ (Theorema`Language`RNG$|Theorema`Computation`Language`RNG$)[r___]]] := Map[ extractVar, Apply[ List, Map[ Hold, Hold[ r]]]]
specifiedVariables[ (Theorema`Language`RNG$|Theorema`Computation`Language`RNG$)[r___]] := Map[ extractVar, {r}]
specifiedVariables[ args___] := unexpected[ specifiedVariables, {args}]

extractVar[ Hold[ _[ (Theorema`Language`VAR$|Theorema`Computation`Language`VAR$)[ v_], ___]]] := v
extractVar[ Hold[ _[ v_, ___]]] := v
extractVar[ expr:Except[_Hold]] := extractVar[ Hold[ expr]]
extractVar[ args___] := unexpected[ extractVar, {args}]


(* ::Subsubsection:: *)
(* boundVariables *)

boundVariables[ expr_] :=
		Apply[ Union, Map[ rngVariables, Cases[ expr, _Theorema`Language`RNG$|_Theorema`Computation`Language`RNG$, Infinity, Heads -> True]]]
boundVariables[ args___] := unexpected[ boundVariables, {args}]


(* ::Subsubsection:: *)
(* freshName *)


(* 'freshName[ x, ex]' returns a fresh name for variable 'x', which is guaranteed to be distinct from all names in 'ex'.
	If 'x' is a list of variables, a fresh name for each of the elements in 'x' is returned; all new names are distinct from each other.
	NOTE: 'x' (or its elements) may be a variable with head 'VAR$' (possibly sequence variables) *or* a plain symbol *or* a string,
	whereas the elements of 'ex' may be plain symbols or strings, but no variables. *)
freshName[ x_List, ex_List] :=
	Module[ {ex0 = Replace[ ex, s_Symbol :> SymbolName[ s], {1}], tmp},
		Replace[ x,
			{
				v:(_Theorema`Language`VAR$|_Theorema`Computation`Language`VAR$) :>
				With[ {n = varName[ v]},
					tmp = freshName[ SymbolName[ n], ex0];
					AppendTo[ ex0, tmp];
					renameVar[ v, Symbol[ Context[ n] <> tmp]]
				],
				s_Symbol :>
				(
					tmp = freshName[ SymbolName[ s], ex0];
					AppendTo[ ex0, tmp];
					Symbol[ Context[ s] <> tmp]
				),
				s_String :>
				(
					tmp = freshName[ s, ex0];
					AppendTo[ ex0, tmp];
					tmp
				)
			},
			{1}
		]
	]
freshName[ x_Symbol, ex:{___Symbol}] :=
	If[ MemberQ[ ex, x],
		Symbol[ Context[ x] <> freshName[ SymbolName[ x], SymbolName /@ ex]],
		x
	]
freshName[ x_Symbol, ex:{___String}] :=
	Symbol[ Context[ x] <> freshName[ SymbolName[ x], ex]]
freshName[ x_Symbol, ex_List] :=
	Symbol[ Context[ x] <> freshName[ SymbolName[ x], Replace[ ex, s_Symbol :> SymbolName[ s], {1}]]]
freshName[ x_String, ex:{___, _Symbol, ___}] :=
	freshName[ x, Replace[ ex, s_Symbol :> SymbolName[ s], {1}]]
freshName[ x_String, ln:{___String}] :=
	Module[ {xn = x, tmp, all, lxn, suffix = "", lsx},
		If[ MemberQ[ ln, x],
			lxn = StringLength[ xn];
			If[ lxn > 1,
				Which[
					lxn > 3 && StringTake[ xn, -3] === "$TM",
					suffix = "$TM";
					xn = StringDrop[ xn, -3],
					
					StringTake[ xn, -1] === "$",
					suffix = "$";
					xn = StringDrop[ xn, -1]
				]
			];
			lsx = StringLength[ suffix];
			tmp = StringCases[ xn, Longest[ DigitCharacter..]~~EndOfString, 1];
			xn = Switch[ tmp,
				{},
				xn,
				{_},
				StringDrop[ xn, -StringLength[ First[ tmp]]]
			];
			lxn = StringLength[ xn];
			all = If[ lsx > 0,
				Cases[ ln, n_String :>
							Module[ {n0},
								ToExpression[n0] /;
								(
									StringLength[ n] > lxn + lsx &&
									StringTake[ n, lxn] === xn &&
									StringTake[ n, -lsx] === suffix &&
									(
										n0 = StringTake[ n, {lxn + 1, StringLength[ n] - lsx}];
										StringMatchQ[ n0, DigitCharacter..]
									)
								)
							]
				],
				Cases[ ln, n_String :>
							Module[ {n0},
								ToExpression[ n0] /;
								(
									StringLength[ n] > lxn &&
									StringTake[ n, lxn] === xn &&
									(
										n0 = StringDrop[ n, lxn];
										StringMatchQ[ n0, DigitCharacter..]
									)
								)
							]
				]
			];
			xn <> Switch[ all,
				{},
				"0",
				_,
				ToString[ Max[ all] + 1]
				] <> suffix,
			
			x
		]
	]
freshName[ x:Except[ _List|_Symbol|_String], ex_] := First[ freshName[ {x}, ex]]
freshName[ args___] := unexpected[ freshName, {args}]


(* ::Subsubsection:: *)
(* substituteBound *)

(* We assume that we don't have nested quantifiers binding the same variable *)
Clear[ substituteBound]
substituteBound[ expr_Hold, {}] := expr
substituteBound[ Hold[], _] := Hold[]
(* Some quantifiers (e.g. "Sum") can be used together with subscripts. *)
substituteBound[ Hold[ q_[ r:(Theorema`Language`RNG$|Theorema`Computation`Language`RNG$)[ rng__], rest__]], rules_List] :=
	Module[ {qvars = rngVariables[ Hold[ r]], vars},
		vars = Select[ rules, !MemberQ[ qvars, #[[1]]]&];
		Hold[ q[ r, rest]] /. rules
	]
substituteBound[ Hold[ f_[ x___]], rules_List] :=
	Module[ { sx = Map[ substituteBound[ #, rules]&, Map[ Hold, Hold[ x]]]},
		sx = Fold[ joinHold, Hold[], {ReleaseHold[ sx]}];
		applyHold[ substituteBound[ Hold[ f], rules], sx]
	]
substituteBound[ x:Hold[_], rules_List] := x
substituteBound[ expr_, rule_?OptionQ] := substituteBound[ expr, {rule}]
substituteBound[ expr_, rules_List] := ReleaseHold[ substituteBound[ Hold[ expr], rules]]
substituteBound[ args___] := unexpected[ substituteBound, {args}]


(* ::Subsubsection:: *)
(* substituteFree *)


(* 'substituteFree[ expr, rules]' substitutes every free occurrence of a variable appearing as the LHS of a rule
	in 'rules' in 'expr' by the corresponding RHS, renaming bound variables to avoid variable capture if necessary.
	If 'expr' is wrapped in 'Hold', no unwanted simplification happens (and the result is wrapped in 'Hold' as well);
	this also applies to the RHSs of the given rules.
	As in 'freeVariables', we do not rely on bound variables occurring only once in multi-ranges.
	Option "checkTypes" specifies whether the sequence-types of the instances shall be checked to match the types of the respective variables.
	Option "postprocessing" specifies a function that is called on the result after substitution (typically either 'sequenceFlatten' or 'Identity'). *)
Options[ substituteFree] = {"checkTypes" -> True, "postprocessing" -> sequenceFlatten};
substituteFree[ expr_, {}, ___] := expr
substituteFree[ expr_, rule:(_Rule|_RuleDelayed), opts___] := substituteFree[ expr, {rule}, opts]
substituteFree[ expr_, rules_List, opts___?OptionQ] :=
	Module[ {newRules, varStruct, varNames, rename = {}, rn = {}, bp, check, post},
		{check, post} = {"checkTypes", "postprocessing"} /. {opts} /. Options[ substituteFree];
		Catch[
			If[ TrueQ[ check],
				Scan[
					If[ !sequenceTypeMatchQ[ Last[ #], First[ #]],
						Throw[ $Failed]
					]&,
					rules
				]
			];
			varStruct = analyzeVars[ expr];
			varNames = varStruct[[All, 1]];
			newRules = DeleteCases[
				Replace[ rules,
					_[ l_, r_] :>
					With[ {fp = First[ Replace[ Replace[ l, varStruct], l -> {{}, {}}]],
							rhs = Switch[ Hold[ r], Hold[ _Hold|_HoldComplete], r, _, Hold[ r]],
							fv = freeVariables[ Hold[ r]]},
						varNames = Join[ varNames, Cases[ Hold[ r], _Theorema`Language`VAR$|_Theorema`Language`VAR$, {0, Infinity}, Heads -> True]];
						If[ fp === {},
							Null,
							
							Scan[
								Function[ x,
									bp = Last[ Replace[ Replace[ x, varStruct], x -> {{}, {}}]];
									bp = Select[ bp, With[ {q = First[ #]}, MemberQ[ fp, p_ /; inScope[ p, q]]]&];
									(* 'bp' is the list of all binding-positions of variable 'x' that need to be
										renamed in order to avoid variable capture. *)
									If[ bp =!= {},
										rename = Join[ rename, (x -> Prepend[ Last[ #], First[ #]])& /@ bp];
										AppendTo[ rn, x]
									]
								],
								fv
							];
							RuleDelayed @@ Prepend[ rhs, fp]
						]
					],
					{1}
				],
				Null
			];
			rn = DeleteDuplicates[ rn];
			rn = MapThread[ Rule, {rn, freshName[ rn, varName /@ DeleteDuplicates[ varNames]]}];
			rename =
				Replace[
					GatherBy[ rename, First],
					all:{x_ -> _, ___} :>
					With[ {xn = Replace[ x, rn]},
						DeleteDuplicates[ Flatten[ all[[All, 2]], 1]] :> xn
					],
					{1}
				];
			post[ ReplacePart[ expr, Join[ newRules, rename]]]
		]
	]
substituteFree[ args___] := unexpected[ substituteFree, {args}]

(* In contrast to 'substituteFree', 'instantiateMeta' has option "checkValidity" which specifies whether the validity of the instantiation
	shall be checked as a whole. In addition to checking the sequence-types of the meta-variables and their instances, this also includes
	checking that the instance of no variable depends on illegal abf constants. *)
Options[ instantiateMeta] = {"checkValidity" -> True, "postprocessing" -> sequenceFlatten};
instantiateMeta[ expr_, rules:{((Rule|RuleDelayed)[ (Theorema`Language`META$|Theorema`Computation`Language`META$)[ _, __], _])...}, opts___?OptionQ] :=
	Module[ {check, post},
		{check, post} = {"checkValidity", "postprocessing"} /. {opts} /. Options[ instantiateMeta];
		Catch[
			If[ TrueQ[ check],
				Scan[
					With[ {fix = #[[1, -1]]},
						If[ !(
								FreeQ[ Last[ #], c:(_Theorema`Language`FIX$|_Theorema`Computation`Language`FIX$) /; !MemberQ[ fix, c]] &&
								sequenceTypeMatchQ[ Last[ #], First[ #]]
							),
							Throw[ $Failed]
						]
					]&,
					rules
				]
			];
			post[ expr /. rules]
		]
	]
instantiateMeta[ args___] := unexpected[ instantiateMeta, {args}]


(* ::Subsubsection:: *)
(* renameBound *)

renameBound[ q_[ (rh:(Theorema`Language`RNG$|Theorema`Computation`Language`RNG$))[ rng___], form___], new_List, opts___?OptionQ] /; Length[ Hold[ rng]] === Length[ new] :=
	With[ {pairs = Thread[ {Hold[ rng], Hold @@ new}, Hold]},
		Module[ {repl = {}, newRng, check, post},
			{check, post} = {"checkTypes", "postprocessing"} /. {opts} /. Options[ substituteFree];
			Catch[
				If[ TrueQ[ check],
					Scan[
						With[ {tmp = HoldComplete /@ #},
							If[ !sequenceTypeEqual[ First[ tmp], Last[ tmp]],
								Throw[ $Failed]
							]
						]&,
						List @@ (Hold @@@ pairs)
					]
				];
				newRng =
					ReplacePart[
						Hold @@ {
							Flatten[
								Replace[
									pairs,
									{all:(r_[ x_, rest___]), v_} :>
										With[ {tmp =
													If[ repl === {} && x === v,
														Hold[ all],
													(*else*)
														With[ {old = repl},
															repl = DeleteCases[ repl, x -> _];
															If[ x =!= v, PrependTo[ repl, x -> v]];
															ReplacePart[ Hold @@ {Prepend[ substituteFree[ Hold[ rest], old, "checkTypes" -> False, "postprocessing" -> post], v]}, {1, 0} -> r]
														]
													]
												},
											tmp /; True
										],
									{1}
								],
								1,
								Hold
							]
						},
						{1, 0} -> rh
					];
				q @@ Join[ newRng, substituteFree[ Hold[ form], repl, "checkTypes" -> False, "postprocessing" -> post]]
			]
		]
	]
renameBound[ args___] := unexpected[ renameBound, {args}]


(* ::Section:: *)
(* Expression categories *)

isQuantifierFormula[ e_] := MatchQ[ e, 
	_Theorema`Language`Forall$TM|_Theorema`Computation`Language`Forall$TM|
	_Theorema`Language`Exists$TM|_Theorema`Computation`Language`Exists$TM|
	_Theorema`Language`NotExists$TM|_Theorema`Computation`Language`NotExists$TM|
	_Theorema`Language`ExistsUnique$TM|_Theorema`Computation`Language`ExistsUnique$TM]
isQuantifierFormula[ args___] := unexpected[ isQuantifierFormula, {args}]

isConnectiveFormula[ e_] := MatchQ[ e, 
	_Theorema`Language`Not$TM|_Theorema`Computation`Language`Not$TM|
	_Theorema`Language`And$TM|_Theorema`Computation`Language`And$TM|
	_Theorema`Language`Or$TM|_Theorema`Computation`Language`Or$TM|
	_Theorema`Language`Implies$TM|_Theorema`Computation`Language`Implies$TM|
	_Theorema`Language`Iff$TM|_Theorema`Computation`Language`Iff$TM|
	_Theorema`Language`IffDef$TM|_Theorema`Computation`Language`IffDef$TM]
isConnectiveFormula[ args___] := unexpected[ isConnectiveFormula, {args}]

isAtomicExpression[ e_] := !isQuantifierFormula[ e] && !isConnectiveFormula[ e]
isAtomicExpression[ args___] := unexpected[ isAtomicExpression, {args}]

isLiteralExpression[ Theorema`Language`Not$TM[ e_]|Theorema`Computation`Language`Not$TM[ e_]] := isAtomicExpression[ e]
isLiteralExpression[ e_] := isAtomicExpression[ e]
isLiteralExpression[ args___] := unexpected[ isLiteralExpression, {args}]

isAtomicTerm[ _?isNonNumberAtomicTerm] := True
isAtomicTerm[ _?NumberQ] := True
isAtomicTerm[ _] := False
isAtomicTerm[ args___] := unexpected[ isAtomicTerm, {args}]

isNonNumberAtomicTerm[ _Theorema`Language`VAR$|_Theorema`Language`FIX$|_Symbol] := True
isNonNumberAtomicTerm[ _] := False
isNonNumberAtomicTerm[ args___] := unexpected[ isNonNumberAtomicTerm, {args}]


(* ::Subsubsection:: *)
(* isQuantifierFree *)

isQuantifierFree[ expr_] :=
	FreeQ[ expr,
		_Theorema`Language`RNG$|
		_Theorema`Computation`Language`RNG$]
isQuantifierFree[ args___] := unexpected[ isQuantifierFree, {args}]

(* ::Subsubsection:: *)
(* isLogQuantifierFree *)

isLogQuantifierFree[ expr_] := FreeQ[ expr, _Theorema`Language`Forall$TM|_Theorema`Language`Exists$TM|_Theorema`Language`NotExists$TM|_Theorema`Language`ExistsUnique$TM]
isLogQuantifierFree[ args___] := unexpected[ isLogQuantifierFree, {args}]

(* ::Subsubsection:: *)
(* variableFree *)

isVariableFree[ expr_, level_:{1}] := 
	FreeQ[ expr,
		_Theorema`Language`VAR$|_Theorema`Computation`Language`VAR$, level]
isVariableFree[ args___] := unexpected[ isVariableFree, {args}]

(* ::Subsubsection:: *)
(* ground expressions *)

isGround[ expr_, level_:Infinity] := 
	FreeQ[ expr,
		_Theorema`Language`VAR$|_Theorema`Computation`Language`VAR$|
		_Theorema`Language`FIX$|_Theorema`Computation`Language`FIX$|
		_Theorema`Language`META$|_Theorema`Computation`Language`META$, level]
isGround[ args___] := unexpected[ isGround, {args}]


(* ::Subsubsection:: *)
(* getInstances *)

(* def is a formula, maybe quantified, which contains an implicit def as innermost part
	returns:
	l ... a list of instances of the left side without free variables
	r ... a transformation rule that can be used to generate appropriate instances of the right side *)
getDefInstances[ expr_, def_] :=
	Module[{strip, mmaPatt, defRule, l},
		strip = stripUniversalQuantifiers[ def];
		{mmaPatt, defRule} = makePatternRule[ strip];
		If[ mmaPatt =!= $Failed && defRule =!= $Failed,
			l = Select[ Cases[ expr, mmaPatt, Infinity], freeVariables[#] === {}&];
			{l, defRule},
		(*else*)
			{$Failed, $Failed}
		]
	]
getDefInstances[ args___] := unexpected[ getDefInstances, {args}]

(* makePatternRule[ ...] returns a list {l, r}, where
	l is a Mma pattern for the Left side of the definition
	r is a rule of the form {l, dummyTMAKB$_} :> ..., 
	which can be applied to {instance of l, K} and returns
	{} if the required conditions of the implicit definition are not satisfied by the instance of l or
	{rng, body, pos} where 
		rng is the range of the such-quantifier,
		body is the instanciated body of the definition, and
		pos is a list of positions, where the conditions of the implicit definition occur in K
*)
makePatternRule[ {Theorema`Language`EqualDef$TM[ l_, (Theorema`Language`Such$TM|Theorema`Language`SuchUnique$TM)[ rng_, cond_, body_]], c_List, var_List}] :=
    With[ {left = execLeft[ Hold[l], var],
           newBody = simplifiedAnd[ makeConjunction[ Join[ rngToCondition[ rng], {cond, body}], Theorema`Language`And$TM]]},
		If[ left =!= $Failed,
	        {ToExpression[ left],
	        ToExpression[
	            "RuleDelayed[{" <> left <> ", dummyTMAKB$_}," <>
	            "Module[ {pos}, If[ (pos=Theorema`Common`checkAllConds[" <> execRight[ Hold[ c], var] <> ", dummyTMAKB$])=!=False, {" <>
	            ToString[ rng] <> "," <>  execRight[ Hold[ newBody], var] <> ",pos}, {}]]]"
	        ]},
	    (*else*)
	    	{$Failed, $Failed}
		]
    ]
makePatternRule[ args___] := unexpected[ makePatternRule, {args}]

(* Checks whether all c_i are contained in K and returns
	{} if c is empty (can be interpreted as True, since ALL c_i of empty list are contained in K) or
	a list of positions where the c_i occur in K
	False if at least one of the c_i is not in K 
	*)
checkAllConds[ c_List, K_List] :=
	Module[{pos},
		pos = Map[ Position[ K, #, {1}]&, c];
		If[ MemberQ[ pos, {}],
			False,
			Apply[ Join, pos]
		]
	]
checkAllConds[ args___] := unexpected[ checkAllConds, {args}]

(* ::Subsubsection:: *)
(* transferToComputation *)

transferToComputation[ f_FML$] :=
	Module[{stripUniv, exec},
		stripUniv = stripUniversalQuantifiers[ formula@f];
		(* if we have a definition in a domain, we need to register the operation, otherwise extension domains will not work *)
		registerDomainDefinitionSymbol[ stripUniv];
		exec = executableForm[ stripUniv, f];
		(* Certain equalities cannot be made executable and generate an error when translated to Mma.
		   Since this operation is part of the preprocesing, we catch the error,
		   otherwise preprocessing would end in a premature state. *)
		Quiet[ Check[ ToExpression[ exec], Null], {SetDelayed::nosym, SetDelayed::write}]
	]
transferToComputation[ args___] := unexpected[ transferToComputation, {args}]

(*
	stripUniversalQuantifiers[ form] transforms form into a list {f, c, v}, where
		f is the innermost formula being neither a universal quantified formula nor an implication
		c is a list of conditions being applicable to f
		v is a list of universally quantified variables contained in f 
*)
Clear[ stripUniversalQuantifiers]

(*
  To be done: stripUniversalQuantifiers should produce alternatives, e.g. P=>Q=>R could produce
  1) P :> Q=>R
  2) Q /; P :> R
  
  (see AuctionTheory: the proof using assumtion (2): allocation[] => forall i,j: ... => i=j
*)

stripUniversalQuantifiers[ Theorema`Language`Forall$TM[ r_, c_, f_]] :=
	Module[ {rc, vars, cond, inner},
		rc = rngToCondition[ r];
		{inner, cond, vars} = stripUniversalQuantifiers[ f];
		cond = Join[ rc, cond];
		{inner, If[ !TrueQ[ c], joinConditions[ cond, c], cond], Join[ rngVariables[ r], vars]}
	]
(* 
stripUniversalQuantifiers[ Theorema`Language`Implies$TM[ l_, r_ /; Head[ r] =!= Theorema`Language`Forall$TM]] :=
*)
stripUniversalQuantifiers[ Theorema`Language`Implies$TM[ l_, r_]] :=
	Module[ {vars, cond, inner},
		{inner, cond, vars} = stripUniversalQuantifiers[ r];
		{inner, joinConditions[ cond, l], vars}
	]
stripUniversalQuantifiers[ expr_] := {expr, {}, {}}
stripUniversalQuantifiers[ args___] := unexpected[ stripUniversalQuantifiers, {args}]

joinConditions[ c_List, newCond_Theorema`Language`And$TM] := 
	Module[ {simp = simplifiedAnd[ newCond]}, 
		Switch[ simp,
			True,
			c,
			_Theorema`Language`And$TM,
			Join[ Apply[ List, simp], c],
			_,
			Prepend[ c, simp]
		]
	]
joinConditions[ c_List, newCond_] := Prepend[ c, newCond]
joinConditions[ args___] := unexpected[ joinConditions, {args}]

(* If it is not of the form of a domain definition then do nothing, no unexpected[...] must be there
   we store ops in the appropriate contexts for proving and computing, respectively. *)
registerDomainDefinitionSymbol[ {(Theorema`Language`EqualDef$TM|Theorema`Language`IffDef$TM)[ 
	(Theorema`Language`DomainOperation$TM[ dom_, o_][___])|Theorema`Language`DomainOperation$TM[ dom_, o_], _], c_, var_}] :=
	Block[ {$ContextPath = {"System`"}, $Context = "Global`", dl, dr, assignString}, 
		dl = execLeft[ Hold[ dom], var];
		If[ dl =!= $Failed,
			dr = execRight[ Hold[ dom], var];
			assignString = "Theorema`Language`opDefInDom[" <> dl <> "] = Union[ Theorema`Language`opDefInDom[" <> dr <> "],{" <>
				ToString[ o] <> "}]";
			(* update Theorema`Language`opDefInDom *)
			ToExpression[ assignString];
			(* update Theorema`Computation`Language`opDefInDom *)
			ToExpression[ StringReplace[ assignString,
				{"Theorema`Language`" -> "Theorema`Computation`Language`",
	     		 "Theorema`Knowledge`" -> "Theorema`Computation`Knowledge`"}]]
		];
	]


(*
was used in stripUniversalQuantifiers: turned out that rngToCondition does the same.


rangeToCondition[ Theorema`Language`RNG$[ rng__]] := Map[ singleRangeToCondition, {rng}]
rangeToCondition[ args___] := unexpected[ rangeToCondition, {args}]

singleRangeToCondition[ Theorema`Language`SETRNG$[ x_, A_]] := Theorema`Language`Element$TM[ x, A]
singleRangeToCondition[ Theorema`Language`PREDRNG$[ x_, P_]] := P[ x]
singleRangeToCondition[ Theorema`Language`STEPRNG$[ x_, l_, h_, 1]] := 
	Theorema`Language`And$TM[ Theorema`Language`isInteger$TM[x], Theorema`Language`LessEqual$TM[ l, x], Theorema`Language`LessEqual$TM[ x, h]]
singleRangeToCondition[ _] := Sequence[]
singleRangeToCondition[ args___] := unexpected[ singleRangeToCondition, {args}]
*)

Clear[ executableForm]
(* The condition must not contain variables other than the variables in the left hand side, since they would not get instanciated *)
executableForm[ {(Theorema`Language`Iff$TM|Theorema`Language`IffDef$TM|Theorema`Language`Equal$TM|Theorema`Language`EqualDef$TM)[ l_, r_], c_List, var_List}, f_FML$] :=
    Block[ { $ContextPath = {"System`"}, $Context = "Global`", form = ToString[ f, InputForm], formKey = ToString[ key@f, InputForm]},
        With[ {left = execLeft[ Hold[ l], var], right = execRight[ Hold[ r], var]},
        	If[ left =!= $Failed && right =!= $Failed,
	        	(* The complicated DUMMY$COND... construction is necessary because the key itself contains strings,
	        	   and we need to get the escaped strings into the Hold *)
	            StringReplace[ left <> "/; DUMMY$COND && " <> execCondition[ Hold[ trackCondition[ c, l]], var] <> ":= Theorema`Common`trackResult[" <> right <> "," <> form <> "]",
	            	{"DUMMY$COND" -> "Theorema`Common`kbSelectCompute[" <> formKey <> "]",
	            		"Theorema`Language`" -> "Theorema`Computation`Language`",
	            		"Theorema`Knowledge`" -> "Theorema`Computation`Knowledge`"}
	            ],
	        (*else*)
	        	"$Failed"
        	]
        ]
    ] /; Complement[ Intersection[ freeVariables[ c], var], Intersection[ freeVariables[ l], var]] === {}


(* An atomic formula asserts truth *)
executableForm[ {atom_ /; Head[ atom] =!= Theorema`Language`Equal$TM && isAtomicExpression[ atom], c_List, var_List}, f_FML$] :=
    executableForm[ {Theorema`Language`Equal$TM[ atom, True], c, var}, f]   
    
(* We return a string "$Failed", because when returning the expression $Failed (or also Null) the 
   ToExpression[...] in the calling transferToComputation calls $PreRead and $Pre, resulting in messing up the contexts.
   With the string "$Failed" this does not happen *)
executableForm[ expr_, f_FML$] := "$Failed"
executableForm[ args___] := unexpected[ executableForm, {args}]

execLeft[ e_Hold, var_List] := 
	Module[ {s, bound},
		If[ isIndividual[ e],
			s = substituteFree[ e, Map[ varToPattern, var], "checkTypes" -> False, "postprocessing" -> Identity];
			(* All remaining variables are clearly bound. *)
			bound = DeleteDuplicates[ Cases[ s, (_Theorema`Language`VAR$|_Theorema`Computation`Language`VAR$), Infinity]];
			(* We assume that there are no nested binders binding the same variables. *)
			s = s /. Map[ bvarToPattern, bound];
			ReleaseHold[ Map[ Function[ expr, toInputString[ Hold[ expr], True], {HoldAll}], s]],
		(*else*)
			$Failed
		]
	]
execLeft[ args___] := unexpected[ execLeft, {args}]

(* Since "\[Wolf]"-symbols are renamed everywhere, 'execCondition' and 'execRight' do now precisely the same.
	Therefore, one of them could in principle be removed. *)
execCondition[ e_Hold, var_List] := 
	Module[ {s},
		If[ isIndividual[ e],
			s = substituteFree[ e, Map[ stripVar, var], "checkTypes" -> False, "postprocessing" -> Identity] /. {Theorema`Language`Assign$TM -> Set,
				Theorema`Language`SetDelayed$TM -> SetDelayed, 
				Theorema`Language`CompoundExpression$TM -> CompoundExpression,
				Theorema`Language`List$TM -> List};
			ReleaseHold[ Map[ Function[ expr, toInputString[ Hold[ expr], True], {HoldAll}], s]],
		(*else*)
			$Failed
		]
	]
execCondition[ args___] := unexpected[ execCondition, {args}]

execRight[ e_Hold, var_List] := 
	Module[ {s},
		If[ isIndividual[ e],
			s = substituteFree[ e, Map[ stripVar, var], "checkTypes" -> False, "postprocessing" -> Identity] /. {Theorema`Language`Assign$TM -> Set,
				Theorema`Language`SetDelayed$TM -> SetDelayed, 
				Theorema`Language`CompoundExpression$TM -> CompoundExpression,
				Theorema`Language`List$TM -> List};
			ReleaseHold[ Map[ Function[ expr, toInputString[ Hold[ expr], True], {HoldAll}], s]],
		(*else*)
			$Failed
		]
	]
execRight[ args___] := unexpected[ execRight, {args}]

toInputString[ x_Hold, dropWolf_] := First[ toInputStringAux[ x, dropWolf]]
toInputStringAux[ Hold[ s_Symbol], True] :=
	Module[ {name},
		{StringTake[ name, {2, -4}]} /; StringLength[ name = SymbolName[ Unevaluated[ s]]] >= 5 && StringTake[ name, 1] === "\[Wolf]" && StringTake[ name, -3] === "$TM"
	]
toInputStringAux[ Hold[ s_Symbol], False] := {ToString[ Unevaluated[ s]]}
toInputStringAux[ Hold[ head_[ args___]], dropWolf_] :=
	{StringJoin[ toInputStringAux[ Hold[ head], dropWolf], "[", StringJoin[ Riffle[ toInputStringAux[ Hold[ args], dropWolf], ","]], "]"]}
toInputStringAux[ Hold[ s_String], _] := {ToString[ s, InputForm]}
toInputStringAux[ Hold[ s_], _] := {ToString[ Unevaluated[ s]]}
toInputStringAux[ Hold[ first_, rest__], dropWolf_] := Join[ toInputStringAux[ Hold[ first], dropWolf], toInputStringAux[ Hold[ rest], dropWolf]]
toInputStringAux[ Hold[ ], _] := {}

(* We use 'SymbolName', because 'ToString' also returns the context. *)
(* The reason for adding "PATT$" is to distinguish free- from bound variables. *)
stripVar[ v:Theorema`Language`VAR$[ Theorema`Language`SEQ0$[ a_Symbol]]] :=
	v -> ToExpression[ "Theorema`Knowledge`PATT$SEQ0$" <> SymbolName[ a]]
stripVar[ v:Theorema`Language`VAR$[ Theorema`Language`SEQ1$[ a_Symbol]]] :=
	v -> ToExpression[ "Theorema`Knowledge`PATT$SEQ1$" <> SymbolName[ a]]
stripVar[ v:Theorema`Language`VAR$[ a_Symbol]] :=
	v -> ToExpression[ "Theorema`Knowledge`PATT$" <> SymbolName[ a]]
stripVar[ v:Theorema`Language`META$[ Theorema`Language`SEQ0$[ a_Symbol], n_, ___]] :=
	v -> ToExpression[ "Theorema`Knowledge`SEQ0$META$" <> SymbolName[ a] <> ToString[ n]]
stripVar[ v:Theorema`Language`META$[ Theorema`Language`SEQ1$[ a_Symbol], n_, ___]] :=
	v -> ToExpression[ "Theorema`Knowledge`SEQ1$META$" <> SymbolName[ a] <> ToString[ n]]
stripVar[ v:Theorema`Language`META$[ a_Symbol, n_, ___]] :=
	v -> ToExpression[ "Theorema`Knowledge`META$" <> SymbolName[ a] <> ToString[ n]]
stripVar[ args___] := unexpected[ stripVar, {args}]

varToPattern[ v:Theorema`Language`VAR$[ Theorema`Language`SEQ0$[ a_Symbol]]] :=
	With[ {new = ToExpression[ "Theorema`Knowledge`PATT$SEQ0$" <> SymbolName[ a], InputForm, Hold]},
		v -> Pattern@@Append[ new, BlankNullSequence[]]
	]
varToPattern[ v:Theorema`Language`VAR$[ Theorema`Language`SEQ1$[ a_Symbol]]] :=
	With[ {new = ToExpression[ "Theorema`Knowledge`PATT$SEQ1$" <> SymbolName[ a], InputForm, Hold]},
		With[ {tmp1 = Pattern@@Append[ new, BlankSequence[]]},
			v -> Condition[ tmp1, isNonEmptySequence[ new]]
		]
	]
varToPattern[ v:Theorema`Language`VAR$[ a_Symbol]] :=
	With[ {new = ToExpression[ "Theorema`Knowledge`PATT$" <> SymbolName[ a], InputForm, Hold]},
		v -> PatternTest[ Pattern@@Append[ new, Blank[]], isIndividual]
	]
varToPattern[ v:Theorema`Language`META$[ Theorema`Language`SEQ0$[ a_Symbol], n_, ___]] :=
	With[ {new = ToExpression[ "Theorema`Knowledge`SEQ0$META$" <> SymbolName[ a] <> ToString[ n], InputForm, Hold]},
		v -> Pattern@@Append[ new, BlankNullSequence[]]
	]
varToPattern[ v:Theorema`Language`META$[ Theorema`Language`SEQ1$[ a_Symbol], n_, ___]] :=
	With[ {new = ToExpression[ "Theorema`Knowledge`SEQ1$META$" <> SymbolName[ a] <> ToString[ n], InputForm, Hold]},
		With[ {tmp1 = Pattern@@Append[ new, BlankSequence[]]},
			v -> Condition[ tmp1, isNonEmptySequence[ new]]
		]
	]
varToPattern[ v:Theorema`Language`META$[ a_Symbol, n_, ___]] :=
	With[ {new = ToExpression[ "Theorema`Knowledge`META$" <> SymbolName[ a] <> ToString[ n], InputForm, Hold]},
		v -> PatternTest[ Pattern@@Append[ new, Blank[]], isIndividual]
	]
varToPattern[ args___] := unexpected[ varToPattern, {args}]

bvarToPattern[ v:Theorema`Language`VAR$[ Theorema`Language`SEQ0$[ a_Symbol]]] :=
	With[ {new = ToExpression[ "Theorema`Knowledge`SEQ0$" <> SymbolName[ a], InputForm, Hold]},
		v -> Pattern@@Append[ new, Theorema`Language`VAR$[ Blank[ Theorema`Language`SEQ0$]]]
		(* A bound sequence variable may only be "instantiated" by a sequence variable, but not by an individual variable. *)
	]
bvarToPattern[ v:Theorema`Language`VAR$[ Theorema`Language`SEQ1$[ a_Symbol]]] :=
	With[ {new = ToExpression[ "Theorema`Knowledge`SEQ1$" <> SymbolName[ a], InputForm, Hold]},
		v -> Pattern@@Append[ new, Theorema`Language`VAR$[ Blank[ Theorema`Language`SEQ1$]]]
	]
bvarToPattern[ v:Theorema`Language`VAR$[ a_Symbol]] :=
	With[ {rhs = Hold[ a, Theorema`Language`VAR$[ Blank[ Symbol]]]},
		v -> Pattern@@rhs
	]
(* There are no bound meta-variables ... *)
bvarToPattern[ args___] := unexpected[ bvarToPattern, {args}]

(* ::Subsubsection:: *)
(* formulaListToRules *)

(*
	formulaListToRules[ l_List] converts l into a list {f, b, e}, where 
	f is a list of forward rewrite rules (for rewriting the kb) and
	b is a list of backward rewrite rules (for rewriting the goal).
	e is a list of elementary substitution.
*)
formulaListToRules[ l_List] := MapThread[ Join, Map[ formulaToRules, l]]
formulaListToRules[ args___] := unexpected[ formulaListToRules, {args}]


(* ::Subsubsection:: *)
(* formulaToRules *)

(*
	Convert a formula to a list of reasonable rewrite rules.
*)
formulaToRules[ orig:FML$[ _, form_, __]] :=
	Module[{stripUniv, ruleList},
		stripUniv = stripUniversalQuantifiers[ form];
		ruleList = makeRules[ stripUniv, orig]
	]
formulaToRules[ args___] := unexpected[ formulaToRules, {args}]

(*
	We expect the list at pos. 1 to be the result of stripUniversalQuantifiers, i.e. all universal quantifiers are stripped, implications are processed.
	It is of the form {form, c, var}, where form is neither forall nor implies, c is a list of conditions, and var is a list of (universally quantified) variables.
	Result is a list of forward rules, a list of backward rules, and a list of elementary substitutions and/or definition rules.
*)
Clear[ makeRules]

makeRules[ {(Theorema`Language`IffDef$TM|Theorema`Language`EqualDef$TM)[ l_, r_], c_List, var_List}, ref_] := 
	{{}, {}, {makeSingleRule[ {l, r, c, var}, ref]}}
makeRules[ {Theorema`Language`Iff$TM[ l_, r_], c_List, var_List}, ref_] := 
	MapThread[ Join, {makeRules[ {r, joinConditions[ c, l], var}, ref], makeRules[ {l, joinConditions[ c, r], var}, ref]}]
(* Special case equality: we can rewrite left to right and right to left, but we can also rewrite the equality as a whole. *)
makeRules[ {form:Theorema`Language`Equal$TM[ l_, r_], c_List, var_List}, ref_] :=
    Module[ {forward = MapIndexed[ makeSingleRule[ {#1, form, Drop[ c, #2], var}, ref]&, c], backward = {}},
        If[ c =!= {},
        	(* in this case, forward is also empty, we need not do anything *)
            backward = {makeSingleRule[ {form, makeConjunction[ c, Theorema`Language`And$TM], {}, var}, ref, "backward"]}
        ];
        {forward, backward, {If[ isNonNumberAtomicTerm[ r], makeSingleRule[ {r, l, c, var}, ref], makeSingleRule[ {l, r, c, var}, ref]]}}
    ]
(* We do not introduce backward rules for the negated implications *)
(*
	For (A & B) => C we could generate forward rules:
		1) A => C (under condition B)
		2) B => C (under condition A)
	When we augment the KB, in order to apply 1) we need A in the KB and check whether B is fulfilled, i.e. B is in the KB.
	Similarly, for 2) we also need both A and B in the KB.
	Thus, there is no benefit in generating both 1) and 2), we just use one of them.
	If possible, we choose one, where the formula to be rewritten contains all variables, such that they can be instanciated when the rewrite
	rule is applied. If we choose one with some variables missing, then makeSingleRule will not generate a forward rule but maybe still a useful backward rule!
*)
makeRules[ {form:Theorema`Language`And$TM[ f__], c:{c0___, c1_, c2___}, var_List} /; Complement[ var, freeVariables[ c1]] === {}, ref_] := 
	{Join[ (* amaletzk: We cannot use "Append" here, because the second argument could be "Sequence[]" *)
		Map[ makeSingleRule[ 
				{simplifiedNot[ Theorema`Language`Not$TM[ #]], makeDisjunction[ Map[ simplifiedNot[ Theorema`Language`Not$TM[ #]]&, c], Theorema`Language`Or$TM], {}, var}, 
				ref]&, {f}],
		{makeSingleRule[ {c1, form, {c0, c2}, var}, ref]}
	], 
	Map[ makeSingleRule[ {#, makeConjunction[ c, Theorema`Language`And$TM], {}, var}, ref, "backward"]&, {f}],
	{}}
makeRules[ {form:Theorema`Language`And$TM[ f__], c:{c1_, c2___}, var_List}, ref_] := 
	{Join[ 
		Map[ makeSingleRule[ 
				{simplifiedNot[ Theorema`Language`Not$TM[ #]], makeDisjunction[ Map[ simplifiedNot[ Theorema`Language`Not$TM[ #]]&, c], Theorema`Language`Or$TM], {}, var}, 
				ref]&, {f}],
		{makeSingleRule[ {c1, form, {c2}, var}, ref]}
	], 
	Map[ makeSingleRule[ {#, makeConjunction[ c, Theorema`Language`And$TM], {}, var}, ref, "backward"]&, {f}],
	{}}
makeRules[ {form_, c:{c0___, c1_, c2___}, var_List} /; Complement[ var, freeVariables[ c1]] === {}, ref_] := 
	{{makeSingleRule[ {c1, form, {c0, c2}, var}, ref],
	  makeSingleRule[ {simplifiedNot[ Theorema`Language`Not$TM[ form]], makeDisjunction[ Map[ simplifiedNot[ Theorema`Language`Not$TM[ #]]&, c], Theorema`Language`Or$TM], {}, var}, ref]}, 
	{makeSingleRule[ {form, makeConjunction[ c, Theorema`Language`And$TM], {}, var}, ref, "backward"]},
	{}}
makeRules[ {form_, c:{c1_, c2___}, var_List}, ref_] := 
	{{makeSingleRule[ {c1, form, {c2}, var}, ref],
	  makeSingleRule[ {simplifiedNot[ Theorema`Language`Not$TM[ form]], makeDisjunction[ Map[ simplifiedNot[ Theorema`Language`Not$TM[ #]]&, c], Theorema`Language`Or$TM], {}, var}, ref]}, 
	{makeSingleRule[ {form, makeConjunction[ c, Theorema`Language`And$TM], {}, var}, ref, "backward"]},
	{}}
makeRules[ {form_, c_List, var_List}, ref_] := {{}, {}, {}}
makeRules[ args___] := unexpected[ makeRules, {args}]

(*
	A "rewrite rule" is stored as {key, r}, where
	key ... is the key of the formula from which the rule has been derived,
	r   ... is the actual rule lhs:>rhs.
	
	We can use the key to filter rules before applying them to a formula with that key.
*)
(* Do not rewrite numbers and logical combinations *)
makeSingleRule[ {l_?NumberQ, r_, c_List, var_List}, ref_] := Sequence[]
makeSingleRule[ {_Theorema`Language`And$TM|_Theorema`Language`Or$TM|_Theorema`Language`Implies$TM|_Theorema`Language`Iff$TM, r_, c_List, var_List}, ref_] := Sequence[]
makeSingleRule[ {_Theorema`Language`Forall$TM|_Theorema`Language`Exists$TM, r_, c_List, var_List}, ref_] := Sequence[]
(* If the free variables left/right do not coincide, then do not generate a rewrite rule *)
makeSingleRule[ {l_, r_, c_List, var_List}, ref_] /; With[ {fr = freeVariables[ r], fl = freeVariables[ l]}, Complement[ fr, fl] =!= {} || Complement[ fl, var] =!= {}] := 
	Sequence[]
(* If the condition has additional variables, they can be existentially quantified:
	forall x,y: P[x,y] => (f[x]=g[x])  <=>  forall x: (exists y: P[x,y]) => (f[x]=g[x]) *)
makeSingleRule[ {l_, r_, c_List, var_List}, ref_] := 
	Module[ {addVars = Complement[ freeVariables[ c], freeVariables[ l]], newC, out},
		{key@ref, out} /;
			(
				If[ addVars === {},
					newC = c,
					(* else *)
					newC = {Theorema`Language`Exists$TM[ Apply[ Theorema`Language`RNG$, Map[ Theorema`Language`SIMPRNG$, addVars]], True,
						makeConjunction[ c, Theorema`Language`And$TM]]}
				];
				(out = mmaTransRule[ {l, r, newC, var}, ref]) =!= $Failed
			)
	]
makeSingleRule[ {_, _, _List, _List}, _] := Sequence[]
(*
makeSingleRule[ all:{l_, r_, c_List, var_List}, ref_] := {key@ref, mmaTransRule[ all, ref]}
*)

(*
	For backward rules we allow to introduce an existential quantifier if additional free variables occur.
	The corresponding thing for forward rules is not done by rewriting, it should be achieved by instantiation.
*)
makeSingleRule[ {l_, r_, {}, var_List}, ref_, "backward"] := 
	Module[ {addVars = Complement[ freeVariables[ r], freeVariables[ l]], newF},
		If[ addVars === {},
			newF = r,
			(* else *)
			newF = Theorema`Language`Exists$TM[ Apply[ Theorema`Language`RNG$, Map[ Theorema`Language`SIMPRNG$, addVars]], True, r]
		];
		makeSingleRule[ {l, newF, {}, var}, ref]
	]
makeSingleRule[ {l_, r_, c_List, var_List}, ref_, "backward"] := 
	makeSingleRule[ { l, makeConjunction[ Append[ c, r], Theorema`Language`And$TM], {}, var}, ref, "backward"]

makeSingleRule[ args___] := unexpected[ makeSingleRule, {args}]

mmaTransRule[ {l_, r_, c_List, var_List}, ref_] :=
(*
	mmaTransRule[ {left, right, cond, var}, ref] translates left/right into a rewrite rule.
	cond, var are assumed to be come from 'stripUniversalQuantifiers' translating a universally quantified equality/equivalence into
	eq ... the pure equality/equivalence,
	cond ... the conditions on the variables contained in eq, and
	var ... the variables contained in eq.
	ref is the original (universally quantified) equality/equivalence formula. 
	When the resulting rewrite rule is applied, it will Sow[ref, "ref"] and Sow[cond, "cond"], which must be caught by an appropriate Reap, 
	see replace...AndTrack.
*)
    With[ {left = execLeft[ Hold[l], var], 
               cond = makeConjunction[ c, Theorema`Language`And$TM],
               right = execRight[ Hold[r], var]},
            If[ left =!= $Failed && right =!= $Failed,
	            ToExpression[
	            	"RuleDelayed[" <> left <> "," <>
	            	"Sow[" <> ToString[ ref, InputForm] <> ",\"ref\"]; Sow[" <> execCondition[ Hold[ cond], var] <> ",\"cond\"];" <> right <> "]"
	            ],
	        (*else*)
	        	$Failed
            ]
        ]
        
mmaTransRule[ args___] := unexpected[ mmaTransRule, {args}]


(* ::Subsubsection:: *)
(* replace...AndTrack *)

(*
	All these functions return a list {e, form, cond}, where
	e is the resulting expression after replacement,
	form is a list of formulas used for replacement, i.e. the formulas from which the rewrite rules have been derived,
	cond is a condition, under which the replacement is allowed.
*)
replaceAndTrack[ expr:_Theorema`Language`VAR$|_Theorema`Language`SEQ0$|_Theorema`Language`SEQ1$|_Theorema`Language`FIX$, _List] := {expr, {}, True}

replaceAndTrack[ expr_, repl_List] :=
	Module[ {e, uc},
		{e, uc} = Reap[ Replace[ expr, repl], {"ref", "cond"}];
		If[ uc === {{}, {}},
			{e, {}, True},
			(* else *)
			{e, uc[[1,1]], simplifiedAnd[ makeConjunction[ uc[[2,1]], Theorema`Language`And$TM]]}
		]
	]
replaceAndTrack[ args___] := unexpected[ replaceAndTrack, {args}]

replaceListAndTrack[ expr_, repl_List] := 
	Module[ {all},
		all = DeleteCases[ Map[ replaceAndTrack[ expr, {#}]&, repl], {expr, _, _}];
		If[ all === {},
			{{}, {}, {}},
			Transpose[ all]
		]
	]
replaceListAndTrack[ args___] := unexpected[ replaceListAndTrack, {args}]

replaceAllAndTrack[ expr_, repl_List] := 
(* BUGFIX amaletzk: repl might not be a plain list of rewrite rules, but instead consist of 2-element-lists
	originating from "makeSingleRule[]". Hence, we need to make it plain, if necessary.
	Same in "replaceRepeatedAndTrack[]". *)
(* WW Let's look into this: I think the calling program should pass a flat list. If so, use "plain" instead of "plainRepl" *)
	Module[ {e, uc, plainRepl = Switch[ repl, {{_, _}..}, Map[ Last, repl], _, repl]},
		{e, uc} = Reap[ replaceAllExcept[ expr, plainRepl, {}, Heads -> {Theorema`Language`VAR$, Theorema`Language`SEQ0$, Theorema`Language`SEQ1$, Theorema`Language`FIX$}], {"ref", "cond"}];
		If[ uc === {{}, {}},
			{e, {}, True},
			(* else *)
			{e, uc[[1,1]], simplifiedAnd[ makeConjunction[ uc[[2,1]], Theorema`Language`And$TM]]}
		]
	]
replaceAllAndTrack[ args___] := unexpected[ replaceAllAndTrack, {args}]

Clear[ replaceRepeatedAndTrack]
replaceRepeatedAndTrack[ expr_, repl:{___, a_ :> b_, ___} /; Not[ FreeQ[ b, a]]] := replaceAllAndTrack[ expr, repl]
replaceRepeatedAndTrack[ expr_, repl_List] := 
(* We take care that no infinite rewritings occur using "MaxIterations" *)
	Module[ {e, uc, plainRepl = Switch[ repl, {{_, _}..}, Map[ Last, repl], _, repl]},
		{e, uc} = Reap[ 
			Quiet[ replaceRepeatedExcept[expr, plainRepl, {}, Heads -> {Theorema`Language`VAR$, Theorema`Language`SEQ0$, Theorema`Language`SEQ1$, Theorema`Language`FIX$}, MaxIterations -> 5], 
					ReplaceRepeated::rrlim],
				{"ref", "cond"}];
		If[ uc === {{}, {}},
			{e, {}, True},
			(* else *)
			{e, uc[[1,1]], simplifiedAnd[ makeConjunction[ uc[[2,1]], Theorema`Language`And$TM]]}
		]
	]
replaceRepeatedAndTrack[ args___] := unexpected[ replaceRepeatedAndTrack, {args}]

(* ::Subsubsection:: *)
(* filterRules *)

(*
	rules is a list of rewrite rules of the form {k, l:>r} as generated by makeSingleRule above.
	key is the key of the formula, to which the rules are intended to be applied.
	filterRules[ rules_List, key_] filters rules and returns the plain Mathematica rewrite rules that are applicable to the formula with key 'key'.
		It deletes rules where k=key because they are derived from the formula to which they should now be applied.
	filterRules[ rules_List, None] filters none of the rules and returns the plain Mathematica rewrite rules.
	filterRules[ rules_List, keyList_] deletes rules with k in the keyList. It returns a list of rules of the form {k, l:>r}, not the plain Mma rules.
*)
filterRules[ rules_List, key:{_, _}] := Cases[ rules, {Except[ key], r_} -> r]
filterRules[ rules_List, None] := Map[ Part[ #, 2]&, rules]
filterRules[ rules_List, {keys:{_, _}..}] := DeleteCases[ rules, {Alternatives[ keys], _}]
filterRules[ args___] := unexpected[ filterRules, {args}]


(* ::Section:: *)
(* FML$ datastructure *)

defaultFmlPre[ form_, lbl_, simp_, tags_List, _, _] :=
	{sequenceFlatten[ form], lbl, simp, If[ tags === {}, {}, {"tags" -> tags}]}
defaultFmlPre[ args___] := unexpected[ defaultFmlPre, {args}]

Options[ makeFML] = {key :> defKey[], formula -> True, label :> defLabel[], simplify -> True, preprocess -> defaultFmlPre, cellPosition -> Null, formulaTags -> {}};

makeFML[ data___?OptionQ] :=
	Module[{k, forig, lorig, sorig, pp, fs, cp, torig},
		{k, forig, lorig, sorig, pp, cp, torig} = {key, formula, label, simplify, preprocess, cellPosition, formulaTags} /. {data} /. Options[ makeFML];
		Replace[ pp[ forig, lorig, sorig, torig, k, cp],
			{
				{f:Except[ $Failed], l_String, s_, t:{(Except[ "origForm", _String] -> _)...}} :>
					(
						Switch[ s,
							True,
							fs = computeInProof[ f],
							False,
							fs = f,
							_,
							fs = s[ f];
							If[ Head[ fs] === s, fs = f];	(* Security check: If the head of the new formula is still 's', no simplification happened. *)
						];
						If[ isIndividual[ fs],
							Join[ makeTmaFml[ k, fs, l, f], FML$ @@ t],
						(*else*)
							$Failed
						]
					),
				Except[ Null] -> $Failed
			}
		]
	]
makeFML[ args___] := unexpected[ makeFML, {args}]

makeTmaFml[ key_List, fml_, label_String, fml_] := FML$[ key, fml, label]
makeTmaFml[ key_List, fmlSimp_, label_String, fml_] := FML$[ key, fmlSimp, label, "origForm" -> fml]
makeTmaFml[ args___] := unexpected[ makeTmaFml, {args}]

defKey[ ] := {"ID" <> $cellTagKeySeparator <> ToString[ Unique[ "formula"]], "Source" <> $cellTagKeySeparator <> "none"}
defKey[ args___] := unexpected[ defKey, {args}]

defLabel[ ] := ToString[ $formulaLabel++]
defLabel[ args___] := unexpected[ defLabel, {args}]

initFormulaLabel[ ] := $formulaLabel = 0;
initFormulaLabel[ args___] := unexpected[ initFormulaLabel, {args}]

key[ FML$[ k_, _, __]] := k
key[ args___] := unexpected[ key, {args}]

formula[ FML$[ _, fml_, __]] := fml
formula[ args___] := unexpected[ formula, {args}]

label[ FML$[ _, _, l_, ___]] := l
label[ args___] := unexpected[ label, {args}]

id[ FML$[ k_, _, __]] := k[[1]]
(* default case implemented elsewhere *)

source[ FML$[ k_, _, __]] := k[[2]]
source[ args___] := unexpected[ source, {args}]

sourceFile[ FML$[ k_, _, __]] := StringReplace[ k[[2]], StartOfString ~~ "Source" ~~ $cellTagKeySeparator  -> ""]
sourceFile[ args___] := unexpected[ sourceFile, {args}]


formulaReference[ fml_FML$] :=
    With[ { tag = id@fml, labelDisp = makeLabel[ label@fml], fmlDisp = theoremaDisplay[ formula@fml]},
        Cell[ BoxData[ ToBoxes[
            Button[ Tooltip[ Mouseover[ Style[ labelDisp, "FormReference"], Style[ labelDisp, "FormReferenceHover"]], fmlDisp],
               NotebookLocate[ tag], Appearance -> None]
        ]]]
       ]
formulaReference[ args___] := unexpected[ formulaReference, {args}]

(*
	We provide different constructors for goal and assumptions -> allows to generate different labels
*)
makeGoalFML[ data___?OptionQ] :=
	Module[ {l, form, newLabel},
		l = label /. {data} /. Options[ makeFML];
		newLabel = If[ StringMatchQ[ l, "G"~~"\[NumberSign]"|"\[SpaceIndicator]"~~__],
			(* If label already has the goal marker, then don't add it once more *)
			l,
			(* else: add goal marker *) 
			With[ {sep = If[ StringMatchQ[ l, NumberString], "\[NumberSign]", "\[SpaceIndicator]"]}, "G" <> sep <> l]
		];
		form = makeFML[ label -> newLabel, data];
		(* 'makeGoalFML' and 'makeAssumptionFML' are used only in inference rules, i.e. inside 'performProofStep' ==>
			if the formula is not well-formed, we simply throw '$Failed', which is caught in 'performProofStep'.
			Only make sure that these constructors are not called inside another 'Catch'! *)
		If[ form === $Failed,
			Throw[ $Failed],
		(*else*)
			AppendTo[ $generated, form];
			form
		]
	]
makeGoalFML[ args___] := unexpected[ makeGoalFML, {args}]

makeAssumptionFML[ data___?OptionQ] :=
	Module[ {l, form, newLabel},
		l = label /. {data} /. Options[ makeFML];
		newLabel = If[ StringMatchQ[ l, "A"~~"\[NumberSign]"|"\[SpaceIndicator]"~~__],
			(* If label already has the assumption marker, then don't add it once more *)
			l,
			(* else: add assumption marker *) 
			With[ {sep = If[ StringMatchQ[ l, NumberString], "\[NumberSign]", "\[SpaceIndicator]"]}, "A" <> sep <> l]
		];		
		form = makeFML[ label -> newLabel, data];
		If[ form === $Failed,
			Throw[ $Failed],
		(*else*)
			AppendTo[ $generated, form];
			form
		]
	]
makeAssumptionFML[ args___] := unexpected[ makeAssumptionFML, {args}]


(* ::Section:: *)
(* ranges *)


(* ::Subsection:: *)
(* arbitraryButFixed *)


arbitraryButFixed[ expr_, rng_Theorema`Language`RNG$, kb_List:{}] :=
	(*
		Select all variable symbols from rng, then (for each v of them) find all FIX$[ v, n] constants in kb and take the maximal n, say n'.
		A new constant then has the form FIX$[ v, n'+1], hence, we substitute all free VAR$[v] by FIX$[ v, n'+1].
		If no FIX$[ v, n] occurs in kb, then n'+1 is -Infinity, we take 0 instead to create the first new constant FIX$[ v, 0]. 
		We return the expression with variables substituted by abf constants and a range expression expressing the ranges,
		from which the constants have been derived. 
	*)
	Module[{vars = specifiedVariables[ rng], subs},
		subs = Map[ Theorema`Language`VAR$[ #] -> Theorema`Language`FIX$[ #, Max[ Cases[ kb, Theorema`Language`FIX$[ #, n_] -> n, Infinity, Heads -> True]] + 1]&, vars] /. -Infinity -> 0;
		{substituteFree[ expr, subs, "checkTypes" -> False, "postprocessing" -> Identity], rng /. subs}
	]
arbitraryButFixed[ args___] := unexpected[ arbitraryButFixed, {args}]



(* ::Subsection:: *)
(* introduceMeta *)


introduceMeta[ expr_, rng_Theorema`Language`RNG$, forms_List:{}] :=
	(*
		Select all variable symbols from rng, then (for each v of them) find all META$[ v, n, ...] in kb and take the maximal n, say n'.
		A new meta variable then has the form META$[ v, n'+1, c], hence, we substitute all free VAR$[v] by META$[ v, n'+1, c].
		If no META$[ v, n, ...] occurs in kb, then n'+1 is -Infinity, we take 0 instead to create the first new meta variable META$[ v, 0, c]. *)
	Module[{vars = specifiedVariables[ rng], const, subs},
		const = Union[ Cases[ forms, _Theorema`Language`FIX$, Infinity, Heads -> True]];
		subs = Map[ Theorema`Language`VAR$[ #] -> Theorema`Language`META$[ #, Max[ Cases[ forms, Theorema`Language`META$[ #, n_, ___] -> n, Infinity, Heads -> True]] + 1, const]&, vars] /. -Infinity -> 0;
		{substituteFree[ expr, subs, "checkTypes" -> False, "postprocessing" -> Identity], Map[ Part[ #, 2]&, subs]}
	]
introduceMeta[ args___] := unexpected[ introduceMeta, {args}]


(* ::Subsection:: *)
(* instantiateExistGoalInteractive *)

instantiateExistGoalInteractive[ g:FML$[ _, Theorema`Language`Exists$TM[ rng_, __], ___], const_List, K_List] :=
	Module[{vars = rngVariables[ rng], inst, nn},
		inst = getExistGoalInstanceDialog[ vars, const, {g, K}];
		If[ inst === $Failed,
			Return[ $Failed],
			(* else *)
			nn = Position[ inst, Except[ Null], {1}, Heads -> False];
			(* Ignore Null in inst, these come from empty input fields -> these vars should not be instantiated *)
			inst = Map[ makeTmaExpression, Extract[ inst, nn]];
			Thread[ Extract[ vars, nn] -> inst]
		]
	]
instantiateExistGoalInteractive[ args___] := unexpected[ instantiateExistGoalInteractive, {args}]


(* ::Subsection:: *)
(* instantiateUnivKnowInteractive *)

instantiateUnivKnowInteractive[ K_List] :=
	Module[{},
		K
	]
instantiateUnivKnowInteractive[ args___] := unexpected[ instantiateUnivKnowInteractive, {args}]



(* ::Subsection:: *)
(* rngToCondition *)

(*
	rngToCondition[ r] converts the range r into a LIST of conditions.
*)
rngToCondition[ Theorema`Language`RNG$[ r__]] := Apply[ Join, Map[ singleRngToCondition, {r}]]
rngToCondition[ args___] := unexpected[ rngToCondition, {args}]

singleRngToCondition[ Theorema`Language`SIMPRNG$[ v_]] := {}
singleRngToCondition[ Theorema`Language`SETRNG$[ v_, S_]] := {Theorema`Language`Element$TM[ v, S]}
singleRngToCondition[ Theorema`Language`STEPRNG$[ v_, l_Integer, h_, 1]] := 
	{Theorema`Language`Element$TM[ v, Theorema`Language`IntegerInterval$TM[ l, h, True, True]]}
singleRngToCondition[ Theorema`Language`STEPRNG$[ v_, l_, h_, s_]] := 
	Module[ {new, step},
		With[ {n = Theorema`Language`VAR$[ new]},
			step = If[ s === 1, n, Theorema`Language`Times$TM[ n, s]];
			{Theorema`Language`Exists$TM[ Theorema`Language`RNG$[ Theorema`Language`SETRNG$[ n, Theorema`Language`IntegerInterval$TM[ 0, Infinity, True, False]]], True, 
				Theorema`Language`And$TM[ Theorema`Language`Equal$TM[ v, Theorema`Language`Plus$TM[ l, step]],
					If[ TrueQ[ Negative[ s]], Theorema`Language`GreaterEqual$TM, Theorema`Language`LessEqual$TM][ v, h]]]}
		]
	]
singleRngToCondition[ Theorema`Language`PREDRNG$[ v_, P_]] := {P[ v]}
singleRngToCondition[ u_] :=
	With[ {c = Replace[ u, $tmaUserRangeToCondition]},
		If[ ListQ[ c],
			c,
		(*else*)
			{$Failed}
		]
	]
singleRngToCondition[ args___] := unexpected[ singleRngToCondition, {args}]


(* ::Subsubsection:: *)
(* KB operations *)

(*
	The kb operations put the rewrite rules for appropriate formulas into a global variable $rewriteRules. When we
	create a new proof sit (makePRFSIT) we put what has accumulated in $rewriteRules into the approriate places. This means
	that an inference rule MUST use the kb operations provided here to modify the kb and that a rule
	will typically run inside a Block[ {$rewriteRules = {}}, ...], when it enriches the kb.
	
	There is a switch $autoGenerateRules, which can be used to turn off this feature, i.e. with $autoGenerateRules=False the
	kb operations are just the list operations with the additional feature to avoid duplicate entries in the kb.
*)

(*
	joinKB can only join 2 KBs.
	kb1 are new formula, where we need to check for rewrite rules and duplicates.
	kb2 contains no duplicates and rewrite rules have already been generated.
*)
joinKB[ kb1:{___FML$}, kb2:{___FML$}] /; $autoGenerateRules := Fold[ prependKB, kb2, Reverse[ kb1]]
(* When we don't need rewrite rules, it is more efficient using built-in ops instead of folding prependKB *)
joinKB[ kb1:{___FML$}, kb2:{___FML$}] := DeleteDuplicates[ Join[ kb1, kb2], formula[ #1] === formula[ #2]&]
joinKB[ args___] := unexpected[ joinKB, {args}]

appendKB[ kb:{___FML$}, fml_FML$] /; $autoGenerateRules := 
	Module[ {member, trimmed},
		member = Catch[ Scan[ If[ formula@fml === formula@#, Throw[ True]]&, kb]; False];
		If[ member,
			(* fml is already in kb, we leave kb unchanged *)
			kb,
			(* else: do the op and generate rewrite rules *)
			trimmed = trimFormulaForRewriting[ fml];
			(* put rewrite rules to global variable, even if all are empty *)
			AppendTo[ $rewriteRules, Rest[ trimmed]];
			(* First[ trimmed] can be empty or {fml}, in either case Join does the right thing *)
			Join[ kb, First[ trimmed]]
		]
	]
appendKB[ kb:{___FML$}, fml_FML$] := DeleteDuplicates[ Append[ kb, fml], formula[ #1] === formula[ #2]&]
appendKB[ args___] := unexpected[ appendKB, {args}]

prependKB[ kb:{___FML$}, fml_FML$] /; $autoGenerateRules := 
	Module[ {member, trimmed},
		member = Catch[ Scan[ If[ formula@fml === formula@#, Throw[ True]]&, kb]; False];
		If[ member,
			(* fml is already in kb, we leave kb unchanged *)
			kb,
			(* else: do the op and generate rewrite rules*)
			trimmed = trimFormulaForRewriting[ fml];
			(* put rewrite rules to global variable, even if all are empty *)
			AppendTo[ $rewriteRules, Rest[ trimmed]];
			(* First[ trimmed] can be empty or {fml}, in either case Join does the right thing *)
			Join[ First[ trimmed], kb]
		]
	]
prependKB[ kb:{___FML$}, fml_FML$] := DeleteDuplicates[ Prepend[ kb, fml], formula[ #1] === formula[ #2]&]
prependKB[ args___] := unexpected[ prependKB, {args}]

SetAttributes[ appendToKB, HoldFirst]
appendToKB[ kb_, fml_FML$] := (kb = appendKB[ kb, fml])
appendToKB[ args___] := unexpected[ appendToKB, {args}]

SetAttributes[ prependToKB, HoldFirst]
prependToKB[ kb_, fml_FML$] := (kb = prependKB[ kb, fml])
prependToKB[ args___] := unexpected[ prependToKB, {args}]

trimKBforRewriting[ k_List] :=
	Module[{sRules = {}, dRules = {}, kbRules = {}, goalRules = {}, thinnedKB = {}},
		Do[
        	{thinnedKB, kbRules, goalRules, sRules, dRules} = 
        		MapThread[ Join, {{thinnedKB, kbRules, goalRules, sRules, dRules}, trimFormulaForRewriting[ k[[i]]]}];
        	,
        	{i, Length[k]}
        ];
        {thinnedKB, kbRules, goalRules, sRules, dRules}
	]
trimKBforRewriting[ args___] := unexpected[ trimKBforRewriting, {args}]


trimFormulaForRewriting[ form_FML$] :=
    Module[ {sRules = {}, dRules = {}, kbRules = {}, goalRules = {}, kbForm = {}},
        Switch[ form,
            FML$[ _, (Theorema`Language`EqualDef$TM|Theorema`Language`Equal$TM)[ lhs_, rhs_], __]|FML$[ _, (Theorema`Language`IffDef$TM|Theorema`Language`Iff$TM)[ lhs_?isLogQuantifierFree, rhs_?isLogQuantifierFree], __],
            (* these are substitutions that we want to perform immediately -> elemSubstRules 
               subst coming from equalities are in pos 3, equivalences produce identical forward and backward rules, hence we take only the forward in pos 1
               and join them *)
            sRules = Apply[ Join, Delete[ formulaToRules[ form], 2]];
            AppendTo[ kbForm, form],
            (* explicit definitions -> rewrite rules *)
            FML$[ _, _?(!FreeQ[ #, _Theorema`Language`IffDef$TM|Theorema`Language`EqualDef$TM[ _, Except[ _Theorema`Language`Such$TM|_Theorema`Language`SuchUnique$TM]]]&), __],
            (* definition rules come in pos 3 *)
            dRules = formulaToRules[ form][[3]],
            (* implicit definitions -> stay untouched *)
            FML$[ _, _?(!FreeQ[ #, Theorema`Language`EqualDef$TM[ _, _Theorema`Language`Such$TM|_Theorema`Language`SuchUnique$TM]]&), __],
            AppendTo[ kbForm, form],
            _,
            {kbRules, goalRules, sRules} = formulaToRules[ form];
            AppendTo[ kbForm, form]
            ];
        {kbForm, kbRules, goalRules, sRules, dRules}
    ]
trimFormulaForRewriting[ args___] := unexpected[ trimFormulaForRewriting, {args}]


End[]

EndPackage[]
