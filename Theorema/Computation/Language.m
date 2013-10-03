(* ::Package:: *)

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


   
Plus$TM[ a___] /; buiActive["Plus"] := Plus[ a]
Times$TM[ a___] /; buiActive["Times"] := Times[ a]
Power$TM[ a_, b_] /; buiActive["Power"] := Power[ a, b]
Equal$TM[ a_, b_] /; buiActive["Equal"] := a == b
Less$TM[ a__] /; buiActive["Less"] := Less[ a]
LessEqual$TM[ a__] /; buiActive["LessEqual"] := LessEqual[ a]
Greater$TM[ a__] /; buiActive["Greater"] := Greater[ a]
GreaterEqual$TM[ a__] /; buiActive["GreaterEqual"] := GreaterEqual[ a]
BracketingBar$TM[ a:(_Integer|_Rational|_Real|_Complex|_DirectedInfinity)] /; buiActive["AbsValue"] := Abs[ a]
BracketingBar$TM[ a:(Pi|E|Degree|EulerGamma|GoldenRatio|Catalan|Khinchin|Glaisher)] /; buiActive["AbsValue"] := a



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

(* We replace the free variables one after the other, because some might depend on others, and a
	single "substitueFree" doesn't work properly then. This could also be good for global abbreviations ... *)
SetAttributes[ Abbrev$TM, HoldRest]
Abbrev$TM[ RNG$[ f_ABBRVRNG$, r__ABBRVRNG$], expr_] /; buiActive["Let"] :=
	Abbrev$TM[ RNG$[ f], Abbrev$TM[ RNG$[ r], expr]]
Abbrev$TM[ rng:RNG$[ ABBRVRNG$[ l_, r_]], expr_] /; buiActive["Let"] :=
	ReleaseHold[ substituteFree[ Hold[ expr], {l -> r}]]

rangeToIterator[ SETRNG$[ x_, A_Set$TM]] := { x, Apply[ List, A]}
rangeToIterator[ 
  STEPRNG$[ x_, l_Integer, h_Integer, s_Integer]] := {x, l, h, s}
rangeToIterator[ _] := $Failed
rangeToIterator[ args___] := unexpected[ rangeToIterator, {args}]

ClearAll[ Forall$TM, Exists$TM, SequenceOf$TM, SumOf$TM, ProductOf$TM]
Scan[ SetAttributes[ #, HoldRest] &, {Forall$TM, Exists$TM, 
  SequenceOf$TM, SumOf$TM, ProductOf$TM}]
Scan[ SetAttributes[ #, HoldFirst] &, {SETRNG$, STEPRNG$}]

Forall$TM[ RNG$[ r_, s__], cond_, form_] /; buiActive["Forall"] := 
 	Module[ {splitC},
  		splitC = splitAnd[ cond, {r[[1]]}];
  		With[ {rc = splitC[[1]], sc = splitC[[2]]},
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
  		splitC = splitAnd[ cond, {r[[1]]}];
  		With[ {rc = splitC[[1]], sc = splitC[[2]]},
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
			Do[ If[ TrueQ[ cond],
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
sequenceOfIteration[ iter_List, cond_, form_] := $Failed
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
  	
SumOf$TM[ RNG$[ r_, s__], cond_, form_] /; buiActive["SumOf"] :=
 	Module[ {splitC},
 		splitC = splitAnd[ cond, {r[[1]]}];
 		With[ {rc = splitC[[1]], sc = splitC[[2]]},
 			SumOf$TM[ RNG$[r], rc, SumOf$TM[ RNG$[s], sc, form]]
 		]
	]
SumOf$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["SumOf"] :=
	Module[ {v},
		(Apply[ Plus$TM, v]) /; (v = valueIteration[ rangeToIterator[ r], cond, form]) =!= $Failed
	]
SumOf$TM[ RNG$[ r_, s__], cond_, dom_, form_] /; buiActive["SumOf"] :=
 	Module[ {splitC},
 		splitC = splitAnd[ cond, {r[[1]]}];
 		With[ {rc = splitC[[1]], sc = splitC[[2]]},
 			SumOf$TM[ RNG$[r], rc, dom, SumOf$TM[ RNG$[s], sc, dom, form]]
 		]
	]
SumOf$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, dom_, form_] /; buiActive["SumOf"] :=
	Module[ {v},
		(* amaletz: The reason why it's done in that 'complicated' way is the following:
		   The 0-element might not be defined in "dom", which is no problem, but if it's not
		   defined and one just folds the function using it as the initial element, it will
		   always appear as a symbolic expression in the final result. However, if there is at
		   least 1 value in "v", then the 0-element is not needed at all.
		   Also, "Apply" cannot be used, because the domain functions can only deal with EXACTLY
		   2 arguments (in addition to that, we cannot even rely on associativity).
		*)
		Switch[ Length[ v],
			0, Theorema`Computation`Knowledge`Underscript$TM[0, dom],
			1, First[ v],
			_, Fold[ dom[Plus$TM], First[ v], Rest[ v]]
		] /; (v = valueIteration[ rangeToIterator[ r], cond, form]) =!= $Failed
	]
	
ProductOf$TM[ RNG$[ r_, s__], cond_, form_] /; buiActive["ProductOf"] :=
 	Module[ {splitC},
 		splitC = splitAnd[ cond, {r[[1]]}];
 		With[ {rc = splitC[[1]], sc = splitC[[2]]},
 			ProductOf$TM[ RNG$[r], rc, ProductOf$TM[ RNG$[s], sc, form]]
 		]
	]
ProductOf$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, form_] /; buiActive["ProductOf"] :=
	Module[ {v},
		(Apply[ Times$TM, v]) /; (v = valueIteration[ rangeToIterator[ r], cond, form]) =!= $Failed
	]
ProductOf$TM[ RNG$[ r_, s__], cond_, dom_, form_] /; buiActive["ProductOf"] :=
 	Module[ {splitC},
 		splitC = splitAnd[ cond, {r[[1]]}];
 		With[ {rc = splitC[[1]], sc = splitC[[2]]},
 			ProductOf$TM[ RNG$[r], rc, dom, ProductOf$TM[ RNG$[s], sc, dom, form]]
 		]
	]
ProductOf$TM[ RNG$[ r : _SETRNG$ | _STEPRNG$], cond_, dom_, form_] /; buiActive["ProductOf"] :=
	Module[ {v},
		(* See comment in function "SumOf$TM" *)
		Switch[ Length[ v],
			0, Theorema`Computation`Knowledge`Underscript$TM[1, dom],
			1, First[ v],
			_, Fold[ dom[Times$TM], First[ v], Rest[ v]]
		] /; (v = valueIteration[ rangeToIterator[ r], cond, form]) =!= $Failed
	]
	
SetAttributes[ valueIteration, HoldRest]
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
				AppendTo[val, comp],
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
valueIteration[ iter_List, cond_, form_] := $Failed
valueIteration[ args___] := unexpected[ valueIteration, {args}]



(* ::Section:: *)
(* Sets *)

Set$TM /: Equal$TM[a__Set$TM] /; buiActive["SetEqual"] := SameQ[a]
Set$TM /: SubsetEqual$TM[a_Set$TM, b_Set$TM] /; buiActive["SubsetEqual"] := Equal$TM[Intersection[a, b],a]
Set$TM /: Subset$TM[a_Set$TM, b_Set$TM] /; buiActive["Subset"] := And[SubsetEqual$TM[a,b],Not[Equal$TM[a, b]]]
Set$TM /: SupersetEqual$TM[a_Set$TM, b_Set$TM] /; buiActive["SupersetEqual"] := SubsetEqual$TM[b, a]
Set$TM /: Superset$TM[a_Set$TM, b_Set$TM] /; buiActive["Superset"] := Subset$TM[b, a]
Set$TM /: Union$TM[ a__Set$TM] /; buiActive["Union"] := Union[ a] /. List -> Set$TM
Set$TM /: Intersection$TM[ a__Set$TM] /; buiActive["Intersection"] := Intersection[ a] /. List -> Set$TM
Set$TM /: Backslash$TM[ a_Set$TM,b_Set$TM] /; buiActive["Difference"] := Complement[a, b] /. List -> Set$TM
Set$TM /: EmptyUpTriangle$TM[ a_Set$TM,b_Set$TM] /; buiActive["SymmetricDifference"] := Union[Complement[a, b], Complement[b, a]] /. List -> Set$TM
Set$TM /: Cross$TM[ a__Set$TM] /; buiActive["CartesianProduct"] := Apply[Set$TM, Replace[Tuples[{a}],List[x__]:> Tuple$TM[x] ,{1}]]
Set$TM /: Element$TM[ p_,a_Set$TM] /; buiActive["IsElement"] && MemberQ[ a, p] := True
Set$TM /: Element$TM[ p_,a_Set$TM] /; buiActive["IsElement"] && isVariableFree[a] := False
Set$TM /: \[ScriptCapitalP]$TM[ a_Set$TM] /; buiActive["PowerSet"] := Subsets[ a] /. List -> Set$TM
Set$TM /: BracketingBar$TM[ a_Set$TM] /; buiActive["Cardinality"] && isSequenceFree[a] := Length[ a]
Set$TM /: max$TM[ Set$TM[ e___]] /; buiActive["MaximumElementSet"] :=
	Module[ {s},
		(s /. Max -> max$TM /. {max$TM[x_Set$TM] :> max$TM[x], max$TM[x___] :> max$TM[Set$TM[x]]}) /; (s = Max[ e]; Apply[ Hold, {s}] =!= Hold[ Max[ e]])
	]
Set$TM /: min$TM[ Set$TM[ e___]] /; buiActive["MinimumElementSet"] :=
	Module[ {s},
		(s /. Min -> min$TM /. {min$TM[x_Set$TM] :> min$TM[x], min$TM[x___] :> min$TM[Set$TM[x]]}) /; (s = Min[ e]; Apply[ Hold, {s}] =!= Hold[ Min[ e]])
	]
	




(* ::Section:: *)
(* Number Ranges *)

IntegerRange$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)] /; buiActive["IntegerRange"] && rangeSize[ IntegerRange$TM, l, r, lc, rc] === 0 := Set$TM[ ]
RationalRange$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)] /; buiActive["RationalRange"] && rangeSize[ RationalRange$TM, l, r, lc, rc] === 0 := Set$TM[ ]
RealRange$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)] /; buiActive["RealRange"] && rangeSize[ RealRange$TM, l, r, lc, rc] === 0 := Set$TM[ ]

Set$TM /: Equal$TM[ a:(h:(IntegerRange$TM|RationalRange$TM|RealRange$TM))[ al_?isRealOrInf, ar_?isRealOrInf, alc:(True|False), arc:(True|False)],
		b:Set$TM[ e___?isNumericQuantity]] :=
	Module[ {rs},
		SameQ[ rs, Length[ b], Length[ Select[ b, isInRange[ #, a]&]]] /; buiActive["SetEqual"] && buiActive[StringDrop[SymbolName[h], -3]] && ((rs = rangeSize[h, al, ar, alc, arc]) =!= $Failed)
	]
Set$TM /: Equal$TM[ a_Set$TM, b:(_IntegerRange$TM|_RationalRange$TM|_RealRange$TM)] /; buiActive["SetEqual"] := Equal$TM[ b, a]
	
IntegerRange$TM /: Equal$TM[ IntegerRange$TM[ al_?isRealOrInf, ar_?isRealOrInf, alc:(True|False), arc:(True|False)],
		IntegerRange$TM[ bl_?isRealOrInf, br_?isRealOrInf, blc:(True|False), brc:(True|False)]] /; buiActive["SetEqual"] && buiActive["IntegerRange"] :=
	And[ integerBoundary["left", al, alc] == integerBoundary["left", bl, blc], integerBoundary["right", ar, arc] == integerBoundary["right", br, brc]]
IntegerRange$TM /: Equal$TM[ IntegerRange$TM[ al_?isRealOrInf, ar_?isRealOrInf, alc:(True|False), arc:(True|False)],
		(b:(RationalRange$TM|RealRange$TM))[ bl_?isRealOrInf, br_?isRealOrInf, blc:(True|False), brc:(True|False)]] /; buiActive["SetEqual"] && buiActive["IntegerRange"] && buiActive[StringDrop[SymbolName[b],-3]] :=
	And[ SameQ[ 1, rangeSize[IntegerRange$TM, al, ar, alc, arc], rangeSize[b, bl, br, blc, brc]], integerBoundary["left", al, alc] == bl]
IntegerRange$TM /: Equal$TM[ a:(_RationalRange$TM|_RealRange$TM), b_IntegerRange$TM] /; buiActive["SetEqual"] := Equal$TM[ b, a]

RationalRange$TM /: Equal$TM[ RationalRange$TM[ al_?isRealOrInf, ar_?isRealOrInf, alc:(True|False), arc:(True|False)],
		RationalRange$TM[ bl_?isRealOrInf, br_?isRealOrInf, blc:(True|False), brc:(True|False)]] /; buiActive["SetEqual"] && buiActive["RationalRange"] :=
	Module[ {alcc, arcc, blcc, brcc},
		(al === bl && ar === br && alcc === blcc && arcc === brcc) /;
				(alcc = If[ alc && isInRangeDomain[ RationalRange$TM, al], True, False, $Failed];
				arcc = If[ arc && isInRangeDomain[ RationalRange$TM, ar], True, False, $Failed];
				blcc = If[ blc && isInRangeDomain[ RationalRange$TM, bl], True, False, $Failed];
				brcc = If[ brc && isInRangeDomain[ RationalRange$TM, br], True, False, $Failed];
				Xor[ alcc =!= $Failed, blcc === $Failed] && Xor[ arcc =!= $Failed, brcc === $Failed])
	]
RationalRange$TM /: Equal$TM[ RationalRange$TM[ al_?isRealOrInf, ar_?isRealOrInf, alc:(True|False), arc:(True|False)],
		RealRange$TM[ bl_?isRealOrInf, br_?isRealOrInf, blc:(True|False), brc:(True|False)]] :=
	Module[ {rs},
		And[ SameQ[ 1, rs, rangeSize[RealRange$TM, bl, br, blc, brc]], al == bl] /;
				buiActive["SetEqual"] && buiActive["RationalRange"] && buiActive["RealRange"] && ((rs = rangeSize[RationalRange$TM, al, ar, alc, arc]) =!= $Failed)
	]
RationalRange$TM /: Equal$TM[ a_RealRange$TM, b_RationalRange$TM] /; buiActive["SetEqual"] := Equal$TM[ b, a]

RealRange$TM /: Equal$TM[ RealRange$TM[ al_?isRealOrInf, ar_?isRealOrInf, alc:(True|False), arc:(True|False)],
		RealRange$TM[ bl_?isRealOrInf, br_?isRealOrInf, blc:(True|False), brc:(True|False)]] /; buiActive["SetEqual"] && buiActive["RealRange"] :=
	With[ {alcc = Switch[ al, _DirectedInfinity, False, _, alc],
			arcc = Switch[ ar, _DirectedInfinity, False, _, arc],
			blcc = Switch[ bl, _DirectedInfinity, False, _, blc],
			brcc = Switch[ br, _DirectedInfinity, False, _, brc]},
		And[ al == bl, ar == br, alcc === blcc, arcc === brcc]
	]

Set$TM /: Intersection$TM[ a:(h:(IntegerRange$TM|RationalRange$TM|RealRange$TM))[ _?isRealOrInf, _?isRealOrInf, True|False, True|False],
		b:Set$TM[ ___?isNumericQuantity]] /; buiActive["Intersection"] && buiActive[StringDrop[SymbolName[h],-3]] :=
	Select[ b, isInRange[ #, a]&]
Set$TM /: Intersection$TM[ a_Set$TM, b:(_IntegerRange$TM|_RationalRange$TM|_RealRange$TM)] /; buiActive["Intersection"] := Intersection$TM[ b, a]
		
IntegerRange$TM /: Intersection$TM[ a:IntegerRange$TM[ _?isRealOrInf, _?isRealOrInf, True|False, True|False],
		b:(h:(IntegerRange$TM|RationalRange$TM|RealRange$TM))[ _?isRealOrInf, _?isRealOrInf, True|False, True|False]] /;
			buiActive["Intersection"] && buiActive["IntegerRange"] && buiActive[StringDrop[SymbolName[h],-3]] :=
	IntegerRange$TM[ intersectRanges[ a, b]]
IntegerRange$TM /: Intersection$TM[ a:(_RationalRange$TM|_RealRange$TM), b_IntegerRange$TM] /; buiActive["Intersection"] := Intersection$TM[ b, a]

RationalRange$TM /: Intersection$TM[ a:RationalRange$TM[ _?isRealOrInf, _?isRealOrInf, True|False, True|False],
		b:(h:(RationalRange$TM|RealRange$TM))[ _?isRealOrInf, _?isRealOrInf, True|False, True|False]] /;
			buiActive["Intersection"] && buiActive["RationalRange"] && buiActive[StringDrop[SymbolName[h],-3]] :=
	RationalRange$TM[ intersectRanges[ a, b]]
RationalRange$TM /: Intersection$TM[ a_RationalRange$TM, b_RealRange$TM] /; buiActive["Intersection"] := Intersection$TM[ b, a]

RealRange$TM /: Intersection$TM[ a:RealRange$TM[ _?isRealOrInf, _?isRealOrInf, True|False, True|False],
		b:RealRange$TM[ _?isRealOrInf, _?isRealOrInf, True|False, True|False]] /; buiActive["Intersection"] && buiActive["RealRange"] :=
	RealRange$TM[ intersectRanges[ a, b]]

Element$TM[ p_, h:(_IntegerRange$TM|_RationalRange$TM|_RealRange$TM)] /; buiActive["IsElement"] && buiActive[StringDrop[SymbolName[Head[h]],-3]] := isInRange[ p, h]

IntegerRange$TM /: BracketingBar$TM[ IntegerRange$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)]] /; buiActive["Cardinality"] && buiActive["IntegerRange"] :=
	rangeSize[ IntegerRange$TM, l, r, lc, rc]
RationalRange$TM /: BracketingBar$TM[ RationalRange$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)]] :=
	Module[ {rs},
		rs /; buiActive["Cardinality"] && buiActive["RationalRange"] && ((rs = rangeSize[ RationalRange$TM, l, r, lc, rc]) =!= $Failed)
	]
RealRange$TM /: BracketingBar$TM[ RealRange$TM[ l_?isRealOrInf, r_?isRealOrInf, lc:(True|False), rc:(True|False)]] /; buiActive["Cardinality"] && buiActive["RealRange"] :=
	rangeSize[ RealRange$TM, l, r, lc, rc]
	
IntegerRange$TM /: min$TM[ IntegerRange$TM[ l_?isRealOrInf, _?isRealOrInf, lc:(True|False), True|False]] /; buiActive["MinimumElementSet"] && buiActive["IntegerRange"] && l > -Infinity :=
	integerBoundary[ "left", l, lc]
RationalRange$TM /: min$TM[ RationalRange$TM[ l_?isInRangeDomain[ RationalRange$TM, #]&, _?isRealOrInf, True, True|False]] /; buiActive["MinimumElementSet"] && buiActive["RationalRange"] :=
	l
RealRange$TM /: min$TM[ RealRange$TM[ l_?isRealOrInf, _?isRealOrInf, True, True|False]] /; buiActive["MinimumElementSet"] && buiActive["RealRange"] && l > -Infinity :=
	l
	
IntegerRange$TM /: max$TM[ IntegerRange$TM[ _?isRealOrInf, r_?isRealOrInf, True|False, rc:(True|False)]] /; buiActive["MaximumElementSet"] && buiActive["IntegerRange"] && r < Infinity :=
	integerBoundary[ "right", r, rc]
RationalRange$TM /: max$TM[ RationalRange$TM[ _?isRealOrInf, r_?isInRangeDomain[ RationalRange$TM, #]&, True|False, True]] /; buiActive["MaximumElementSet"] && buiActive["RationalRange"] :=
	r
RealRange$TM /: max$TM[ RealRange$TM[ _?isRealOrInf, r_?isRealOrInf, True|False, True]] /; buiActive["MaximumElementSet"] && buiActive["RealRange"] && r < Infinity :=
	r

isInRange[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[DirectedInfinity[-1], DirectedInfinity[1], _, _]] :=
	isInRangeDomain[ h, p]
isInRange[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[DirectedInfinity[-1], u_, _, True]] :=
	And[ isInRangeDomain[ h, p], LessEqual[ p, u]]
isInRange[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[DirectedInfinity[-1], u_, _, False]] :=
	And[ isInRangeDomain[ h, p], Less[ p, u]]
isInRange[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[l_, DirectedInfinity[1], True, _]] :=
	And[ isInRangeDomain[ h, p], GreaterEqual[ p, l]]
isInRange[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[l_, DirectedInfinity[1], False, _]] :=
	And[ isInRangeDomain[ h, p], Greater[ p, l]]
isInRange[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[l_, u_, True, True]] :=
	And[ isInRangeDomain[ h, p], GreaterEqual[ p, l], LessEqual[ p, u]]
isInRange[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[l_, u_, False, True]] :=
	And[ isInRangeDomain[ h, p], Greater[ p, l], LessEqual[ p, u]]
isInRange[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[l_, u_, True, False]] :=
	And[ isInRangeDomain[ h, p], GreaterEqual[ p, l], Less[ p, u]]
isInRange[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[l_, u_, False, False]] :=
	And[ isInRangeDomain[ h, p], Greater[ p, l], Less[ p, u]]
(* The following functions do precisely the same as isInteger$TM, isRational$TM, isReal$TM,
	except that they work independent of "buiActive", which is needed for ranges.
	isInteger$TM etc. is only called if membership cannot be decided, such that finally the
	symbolic expression "isInteger[...]" results.
	*)
isInRangeDomain[ IntegerRange$TM, _Integer] := True
isInRangeDomain[ IntegerRange$TM, True|False|I|DirectedInfinity[_]|Pi|Degree|GoldenRatio|E|EulerGamma|Catalan|Khinchin|Glaisher] := False
isInRangeDomain[ IntegerRange$TM, _Rational|_Real|_Complex] := False
isInRangeDomain[ IntegerRange$TM, _Set$TM|_Tuple$TM] := False
isInRangeDomain[ IntegerRange$TM, x_] := isInteger$TM[ x]
isInRangeDomain[ RationalRange$TM, _Integer|_Rational] := True
isInRangeDomain[ RationalRange$TM, True|False|I|DirectedInfinity[_]|Pi|Degree|GoldenRatio|E|EulerGamma|Khinchin|Glaisher] := False
isInRangeDomain[ RationalRange$TM, _Real|_Complex] := False
isInRangeDomain[ RationalRange$TM, _Set$TM|_Tuple$TM] := False
isInRangeDomain[ RationalRange$TM, x_] := isRational$TM[ x]
isInRangeDomain[ RealRange$TM, _Integer|_Rational|_Real] := True
isInRangeDomain[ RealRange$TM, True|False|I|DirectedInfinity[_]] := False
isInRangeDomain[ RealRange$TM, Pi|Degree|GoldenRatio|E|EulerGamma|Catalan|Khinchin|Glaisher] := True
isInRangeDomain[ RealRange$TM, _Complex] := False
isInRangeDomain[ RealRange$TM, _Set$TM|_Tuple$TM] := False
isInRangeDomain[ RealRange$TM, x_] := isReal$TM[ x]

(* isRealOrInf returns True iff its argument is either a real number or real infinity. These are the only
	values that make sense as range boundaries. *)
isRealOrInf[ _Integer|_Rational|_Real] := True
isRealOrInf[ DirectedInfinity[1|-1]] := True
isRealOrInf[ Pi|E|EulerGamma|GoldenRatio|Degree|Catalan|Khinchin|Glaisher] := True
isRealOrInf[ _] := False
(* isNumericQuantity yields True whenever its argument is either a number (real or complex) or infinity (real or complex) *)
isNumericQuantity[ x_?isRealOrInf] := True
isNumericQuantity[ _Complex|I|_DirectedInfinity] := True
isNumericQuantity[ _] := False

(* Since we allow arbitrary real numbers as boundaries, we need to compute the actual integer boundaries
	of the range, also taking into account open/closed ranges. *)
integerBoundary[ "left", b_, c_] := With[ {bb = Ceiling[ b]}, If[ c || bb > b, bb, bb + 1]]
integerBoundary[ "right", b_, c_] := With[ {bb = Floor[ b]}, If[ c || bb < b, bb, bb - 1]]

(* rangeSize[] returns $Failed if the cardinality of RationalRange$TM[Catalan, Catalan, True, True]
	should be determined. If Catalan is rational, the cardinality is 1, otherwise it is 0. *)
rangeSize[ IntegerRange$TM, l_, r_, lc_, rc_] :=
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
rangeSize[ ran:(RealRange$TM|RationalRange$TM), l_, r_, lc_, rc_] :=
	If[ lc && rc,
		Which[
			l == r, If[ isInRangeDomain[ ran, l], 1, 0, $Failed],
			l > r, 0,
			True, Infinity
		],
		(*else*)
		If[ l >= r,
			0,
			Infinity
		]
	]

intersectRanges[ _[ al_, ar_, alc_, arc_], _[ bl_, br_, blc_, brc_]] :=
	Module[ {l = Max[ al, bl], r = Min[ ar, br]},
		Apply[ Sequence, {l, r, (al < l || alc) && (bl < l || blc), (ar > r || arc) && (br > r || brc)}]
	]


(* ::Section:: *)
(* Tuples *)


Tuple$TM /: Subscript$TM[ a_Tuple$TM, Rule$TM[ p_, q_]] /; buiActive["Insert"] && isSequenceFree[a] := Insert[ a, p, q /. Tuple$TM -> List]

(* Delete elements at one or more positions *)
Tuple$TM /: Subscript$TM[ a_Tuple$TM, LeftArrow$TM[ b_]] /; buiActive["DeleteAt"] && isSequenceFree[a] := Delete[ a, b //. Tuple$TM -> List]

(* Delete elements of a certain shape. Multiple deletions are not possible, because it would need
	special syntax how to specify multiple shapes. Tuples cannot be used because for this *)
Tuple$TM /: Subscript$TM[a_Tuple$TM, d:(LeftArrowBar$TM[_]..)] /; buiActive["Delete"] := Fold[ DeleteCases[ #1, #2[[1]]]&, a, {d}] 

Tuple$TM /: Equal$TM[a__Tuple$TM] /; buiActive["TupleEqual"] && SameQ[a ] := True
Tuple$TM /: Equal$TM[a__Tuple$TM] /; buiActive["TupleEqual"] && isVariableFree[{a},{2}] := False

Tuple$TM /: Cup$TM[a_Tuple$TM,p_] /; buiActive["Append"] := Append[ a,p]
Tuple$TM /: Cap$TM[p_,a_Tuple$TM] /; buiActive["Prepend"] := Prepend[ a,p]
Tuple$TM /: CupCap$TM[a__Tuple$TM] /; buiActive["Join"] := Join[ a]

Tuple$TM /: Element$TM[p_,a_Tuple$TM] /; buiActive["IsElement"] && MemberQ[a,p] := True
Tuple$TM /: Element$TM[p_,a_Tuple$TM] /; buiActive["IsElement"] && isVariableFree[a] := False

Tuple$TM /: max$TM[ Tuple$TM[ e___]] /; buiActive["Max"] :=
	Module[ {s},
		(s /. Max -> max$TM /. {max$TM[x_Tuple$TM] :> max$TM[x], max$TM[x___] :> max$TM[Tuple$TM[x]]}) /; (s = Max[ e]; Apply[ Hold, {s}] =!= Hold[ Max[ e]])
	]
Tuple$TM /: min$TM[ Tuple$TM[ e___]] /; buiActive["Min"] :=
	Module[ {s},
		(s /. Min -> min$TM /. {min$TM[x_Tuple$TM] :> min$TM[x], min$TM[x___] :> min$TM[Tuple$TM[x]]}) /; (s = Min[ e]; Apply[ Hold, {s}] =!= Hold[ Min[ e]])
	]

Tuple$TM /: BracketingBar$TM[ a_Tuple$TM] /; buiActive["Length"] && isSequenceFree[a] := Length[ a]

Tuple$TM /: Subscript$TM[ a_Tuple$TM, p:LeftArrow$TM[_, _]..] /; buiActive["ReplacePart"] && isSequenceFree[a] :=
	ReplacePart[ a, MapAt[# /. {Tuple$TM -> List}&, {p} /. LeftArrow$TM -> Rule, Table[ {i, 1}, {i, Length[{p}]}]]]

Tuple$TM /: Subscript$TM[ a_Tuple$TM, s:LeftArrowBar$TM[_, _]..] /; buiActive["Replace"] := Fold[ ReplaceAll, a, {s} /. LeftArrowBar$TM -> Rule]

Tuple$TM /: Subscript$TM[ a_Tuple$TM, p__Integer] /; buiActive["Subscript"] := Subscript$TM[ a, Tuple$TM[ p]]
Tuple$TM /: Subscript$TM[ a_Tuple$TM, p_?isPositionSpec] /; buiActive["Subscript"] && isSequenceFree[a] := Extract[ a, p /. Tuple$TM -> List] /. List -> Tuple$TM

isPositionSpec[ _Integer] := True
isPositionSpec[ Tuple$TM[ p__]] := Apply[ And, Map[ isPositionSpec, {p}]]
isPositionSpec[ _] := False
isPositionSpec[ args___] := unexpected[ isPositionSpec, {args}]



(* ::Section:: *)
(* Domains and Data Types *)

isInteger$TM[ _Integer] /; buiActive["isInteger"] := True
isInteger$TM[ True|False|I|DirectedInfinity[_]|Pi|Degree|GoldenRatio|E|EulerGamma|Catalan|Khinchin|Glaisher] /; buiActive["isInteger"] := False
isInteger$TM[ _Rational|_Real|_Complex] /; buiActive["isInteger"] := False
isInteger$TM[ _Set$TM|_Tuple$TM] /; buiActive["isInteger"] := False
isInteger$TM[ (h:(IntegerRange$TM|RationalRange$TM|RealRange$TM))[ ___]] /; buiActive["isInteger"] && buiActive[StringDrop[SymbolName[h],-3]] := False

isRational$TM[ _Integer|_Rational] /; buiActive["isRational"] := True
(* it is not known whether Catalan is rational, therefore we leave "isRational[Catalan]" unevaluated *)
isRational$TM[ True|False|I|DirectedInfinity[_]|Pi|Degree|GoldenRatio|E|EulerGamma|Khinchin|Glaisher] /; buiActive["isRational"] := False
isRational$TM[ _Real|_Complex] /; buiActive["isRational"] := False
isRational$TM[ _Set$TM|_Tuple$TM] /; buiActive["isRational"] := False
isRational$TM[ (h:(IntegerRange$TM|RationalRange$TM|RealRange$TM))[ ___]] /; buiActive["isRational"] && buiActive[StringDrop[SymbolName[h],-3]] := False

isReal$TM[ _Integer|_Rational|_Real] /; buiActive["isReal"] := True
isReal$TM[ True|False|I|DirectedInfinity[_]] /; buiActive["isReal"] := False
isReal$TM[ Pi|Degree|GoldenRatio|E|EulerGamma|Catalan|Khinchin|Glaisher] /; buiActive["isReal"] := True
isReal$TM[ _Complex] /; buiActive["isReal"] := False
isReal$TM[ _Set$TM|_Tuple$TM] /; buiActive["isReal"] := False
isReal$TM[ (h:(IntegerRange$TM|RationalRange$TM|RealRange$TM))[ ___]] /; buiActive["isReal"] && buiActive[StringDrop[SymbolName[h],-3]] := False

Element$TM[ p_, \[DoubleStruckCapitalC]$TM] /; buiActive["IsElement"] && buiActive["isComplex"] := isComplex$TM[ p]
isComplex$TM[ _Integer|_Rational|_Real|_Complex] /; buiActive["isComplex"] := True
isComplex$TM[ True|False|DirectedInfinity[_]] /; buiActive["isComplex"] := False
isComplex$TM[ I|Pi|Degree|GoldenRatio|E|EulerGamma|Catalan|Khinchin|Glaisher] /; buiActive["isComplex"] := True
isComplex$TM[ _Set$TM|_Tuple$TM] /; buiActive["isComplex"] := False
isComplex$TM[ (h:(IntegerRange$TM|RationalRange$TM|RealRange$TM))[ ___]] /; buiActive["isComplex"] && buiActive[StringDrop[SymbolName[h],-3]] := False

isSet$TM[ _Set$TM] /; buiActive["isSet"] := True
isSet$TM[ True|False|I|DirectedInfinity[_]|Pi|Degree|GoldenRatio|E|EulerGamma|Catalan|Khinchin|Glaisher] /; buiActive["isSet"] := False
isSet$TM[ _Integer|_Rational|_Real|_Complex] /; buiActive["isSet"] := False
isSet$TM[ _Tuple$TM] /; buiActive["isSet"] := False
isSet$TM[ (h:(IntegerRange$TM|RationalRange$TM|RealRange$TM))[ ___]] /; buiActive["isSet"] && buiActive[StringDrop[SymbolName[h],-3]] := True

isTuple$TM[ _Tuple$TM] /; buiActive["isTuple"] := True
isTuple$TM[ True|False|I|DirectedInfinity[_]|Pi|Degree|GoldenRatio|E|EulerGamma|Catalan|Khinchin|Glaisher] /; buiActive["isTuple"] := False
isTuple$TM[ _Integer|_Rational|_Real|_Complex] /; buiActive["isTuple"] := False
isTuple$TM[ _Set$TM] /; buiActive["isTuple"] := False
isTuple$TM[ (h:(IntegerRange$TM|RationalRange$TM|RealRange$TM))[ ___]] /; buiActive["isTuple"] && buiActive[StringDrop[SymbolName[h],-3]] := False


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
Do$TM[ body_, l_[v___]] /; buiActive["Do"] := Do[ body, {v}]

SetAttributes[ CaseDistinction$TM, HoldAll]
CaseDistinction$TM[ c:Clause$TM[ _, _]..] /; buiActive["CaseDistinction"] :=
	Apply[Piecewise, Hold[{c}] /. Clause$TM[cond_, expr_] -> {expr, cond}]



(* We assume that all lists not treated by the above constructs should in fact be sets *)
SetAttributes[ List$TM, HoldAll]
List$TM[ l___] := makeSet[l]

cleanupComputation[]
    
End[]
EndPackage[]
