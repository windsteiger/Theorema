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

Element$TM[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[DirectedInfinity[-1], DirectedInfinity[1], _, _]] /; buiActive["IsElement"] && buiActive[StringDrop[SymbolName[h],-3]] :=
	isInRangeDomain[ h, p]
Element$TM[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[DirectedInfinity[-1], u_, _, True]] /; buiActive["IsElement"] && buiActive[StringDrop[SymbolName[h],-3]] :=
	And[ isInRangeDomain[ h, p], LessEqual[ p, u]]
Element$TM[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[DirectedInfinity[-1], u_, _, False]] /; buiActive["IsElement"] && buiActive[StringDrop[SymbolName[h],-3]] :=
	And[ isInRangeDomain[ h, p], Less[ p, u]]
Element$TM[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[l_, DirectedInfinity[1], True, _]] /; buiActive["IsElement"] && buiActive[StringDrop[SymbolName[h],-3]] :=
	And[ isInRangeDomain[ h, p], GreaterEqual[ p, l]]
Element$TM[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[l_, DirectedInfinity[1], False, _]] /; buiActive["IsElement"] && buiActive[StringDrop[SymbolName[h],-3]] :=
	And[ isInRangeDomain[ h, p], Greater[ p, l]]
Element$TM[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[l_, u_, True, True]] /; buiActive["IsElement"] && buiActive[StringDrop[SymbolName[h],-3]] :=
	And[ isInRangeDomain[ h, p], GreaterEqual[ p, l], LessEqual[ p, u]]
Element$TM[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[l_, u_, False, True]] /; buiActive["IsElement"] && buiActive[StringDrop[SymbolName[h],-3]] :=
	And[ isInRangeDomain[ h, p], Greater[ p, l], LessEqual[ p, u]]
Element$TM[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[l_, u_, True, False]] /; buiActive["IsElement"] && buiActive[StringDrop[SymbolName[h],-3]] :=
	And[ isInRangeDomain[ h, p], GreaterEqual[ p, l], Less[ p, u]]
Element$TM[ p_, (h:IntegerRange$TM|RationalRange$TM|RealRange$TM)[l_, u_, False, False]] /; buiActive["IsElement"] && buiActive[StringDrop[SymbolName[h],-3]] :=
	And[ isInRangeDomain[ h, p], Greater[ p, l], Less[ p, u]]

Set$TM /: \[ScriptCapitalP]$TM[ a_Set$TM] /; buiActive["PowerSet"] := Subsets[ a] /. List -> Set$TM
Set$TM /: BracketingBar$TM[ a_Set$TM] /; buiActive["Cardinality"] && isSequenceFree[a] := Length[ a]
Set$TM /: max$TM[ a_Set$TM] /; buiActive["MaximumElementSet"] := Max[a /. Set$TM -> List] /. Max -> max$TM
Set$TM /: min$TM[ a_Set$TM] /; buiActive["MinimumElementSet"] := Min[ a/. Set$TM -> List] /. Min -> min$TM
	
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

Tuple$TM /: max$TM[a_Tuple$TM] /; buiActive["Max"] && isVariableFree[a] := Max[a /. Tuple$TM -> List] /. Max -> max$TM
Tuple$TM /: min$TM[a_Tuple$TM] /; buiActive["Min"] && isVariableFree[a] := Min[a /. Tuple$TM -> List] /. Min -> min$TM

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

(* If max$TM is applied to sets or tuples and built-in Max doesn't completely evaluate, max$TM[x___] remains (where
	x___ is just a sequence of elements). Hence, we also have to deal with that case, but, in order not to get into
	an infinite loop, we have to check whether Max[x___] really simplifies. This has to be done with max$TM, because
	the corresponding Mma function does not have the same name (lower-case vs. upper-case)! Same with min$TM. *)
max$TM[ x___] :=
	Module[{e},
		(e /. Max -> max$TM) /; (e = Max[ x]; Not[ Hold[ Max[ x]] === Apply[ Hold, {e}]])
	]
min$TM[ x___] :=
	Module[{e},
		(e /. Min -> min$TM) /; (e = Min[ x]; Not[ Hold[ Min[ x]] === Apply[ Hold, {e}]])
	]


(* ::Section:: *)
(* Domains and Data Types *)

isInteger$TM[ _Integer] /; buiActive["isInteger"] := True
isInteger$TM[ True|False|I|DirectedInfinity[_]|Pi|Degree|GoldenRatio|E|EulerGamma|Catalan|Khinchin|Glaisher] /; buiActive["isInteger"] := False
isInteger$TM[ _Rational|_Real|_Complex] /; buiActive["isInteger"] := False
isInteger$TM[ _Set$TM|_Tuple$TM] /; buiActive["isInteger"] := False

isRational$TM[ _Integer|_Rational] /; buiActive["isRational"] := True
(* it is not known whether Catalan is rationl, therefore we leave "isRational[Catalan]" unevaluated *)
isRational$TM[ True|False|I|DirectedInfinity[_]|Pi|Degree|GoldenRatio|E|EulerGamma|Khinchin|Glaisher] /; buiActive["isRational"] := False
isRational$TM[ _Real|_Complex] /; buiActive["isRational"] := False
isRational$TM[ _Set$TM|_Tuple$TM] /; buiActive["isRational"] := False

isReal$TM[ _Integer|_Rational|_Real] /; buiActive["isReal"] := True
isReal$TM[ True|False|I|DirectedInfinity[_]] /; buiActive["isReal"] := False
isReal$TM[ Pi|Degree|GoldenRatio|E|EulerGamma|Catalan|Khinchin|Glaisher] /; buiActive["isReal"] := True
isReal$TM[ _Complex] /; buiActive["isReal"] := False
isReal$TM[ _Set$TM|_Tuple$TM] /; buiActive["isReal"] := False

Element$TM[ p_, \[DoubleStruckCapitalC]$TM] /; buiActive["IsElement"] && buiActive["isComplex"] := isComplex$TM[ p]
isComplex$TM[ _Integer|_Rational|_Real|_Complex] /; buiActive["isComplex"] := True
isComplex$TM[ True|False|DirectedInfinity[_]] /; buiActive["isComplex"] := False
isComplex$TM[ I|Pi|Degree|GoldenRatio|E|EulerGamma|Catalan|Khinchin|Glaisher] /; buiActive["isComplex"] := True
isComplex$TM[ _Set$TM|_Tuple$TM] /; buiActive["isComplex"] := False

isSet$TM[ _Set$TM] /; buiActive["isSet"] := True
isSet$TM[ True|False|I|DirectedInfinity[_]|Pi|Degree|GoldenRatio|E|EulerGamma|Catalan|Khinchin|Glaisher] /; buiActive["isSet"] := False
isSet$TM[ _Integer|_Rational|_Real|_Complex] /; buiActive["isSet"] := False
isSet$TM[ _Tuple$TM] /; buiActive["isSet"] := False

isTuple$TM[ _Tuple$TM] /; buiActive["isTuple"] := True
isTuple$TM[ True|False|I|DirectedInfinity[_]|Pi|Degree|GoldenRatio|E|EulerGamma|Catalan|Khinchin|Glaisher] /; buiActive["isTuple"] := False
isTuple$TM[ _Integer|_Rational|_Real|_Complex] /; buiActive["isTuple"] := False
isTuple$TM[ _Set$TM] /; buiActive["isTuple"] := False


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
