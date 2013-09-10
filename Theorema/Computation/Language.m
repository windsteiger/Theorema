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



(* ::Section:: *)
(* Logic *)


Not$TM[ a_] /; buiActive["Not"] := Not[ a]
And$TM[ a___] /; buiActive["And"] := And[ a]
Or$TM[ a___] /; buiActive["Or"] := Or[ a]
Implies$TM[ a__] /; buiActive["Implies"] := Implies[ a]
Iff$TM[ a__] /; buiActive["Iff"] := Equivalent[ a]
Abbrev$TM[ RNG$[ r__ABBRVRNG$], expr_] /; buiActive["Let"] := expr //. Map[ Apply[ Rule, #]&, {r}]

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
			_, Fold[ dom[Plus$TM], dom[Plus$TM][First[v], v[[2]]], Drop[v, 2]]
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
			_, Fold[ dom[Times$TM], dom[Times$TM][First[v], v[[2]]], Drop[v, 2]]
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
Set$TM /: Cross$TM[ a__Set$TM] /; buiActive["CartesianProduct"] := Flatten[List[Tuples[{a}//. Set$TM -> List]],1] /. List -> Set$TM
Set$TM /: Element$TM[ p_,a_Set$TM] /; buiActive["IsElement"] := MemberQ[ a, p]
Set$TM /: \[ScriptCapitalP]$TM[ a_Set$TM] /; buiActive["PowerSet"] := Subsets[ a] /. List -> Set$TM
Set$TM /: BracketingBar$TM[ a_Set$TM] /; buiActive["Cardinality"] && isSequenceFree[a] := Length[ a]
Set$TM /: max$TM[ a_Set$TM] /; buiActive["MaximumElementSet"] := Max[a /. Set$TM -> List]
Set$TM /: min$TM[ a_Set$TM] /; buiActive["MinimumElementSet"] := Min[ a/. Set$TM -> List]


(* ::Section:: *)
(* Tuples *)


Tuple$TM /: Subscript$TM[a_Tuple$TM,Rule$TM[p_,q_]] /; buiActive["Insert"] && isSequenceFree[a] := Insert[ a,p,q /. Tuple$TM -> List]

Tuple$TM /: Subscript$TM[a_Tuple$TM,LeftArrow$TM[b_]] /; buiActive["DeleteAt"] && isSequenceFree[a] := Delete[ a, b //. Tuple$TM -> List]
forDelete[a_, p_] := 
  Module[{anew := a, pnew}, 
   If[ Length[p] <= 0, pnew = {p}, pnew = p]; 
   For[i = 1, i <= Length[pnew], i++,  
     anew = DeleteCases[anew, pnew[[i]], Infinity]];
	anew]
Tuple$TM /: Subscript$TM[a_Tuple$TM, LeftArrowBar$TM[p_]] /; buiActive["Delete"] := forDelete[a, p] 

Tuple$TM /: Equal$TM[a__Tuple$TM] /; buiActive["TupleEqual"] && SameQ[a ] := True
Tuple$TM /: Equal$TM[a__Tuple$TM] /; buiActive["TupleEqual"] && isVariableFree[{a},{2}] := SameQ[a ]

Tuple$TM /: Cup$TM[a_Tuple$TM,p_] /; buiActive["Append"] := Append[ a,p]
Tuple$TM /: Cap$TM[p_,a_Tuple$TM] /; buiActive["Prepend"] := Prepend[ a,p]
Tuple$TM /: CupCap$TM[a__Tuple$TM] /; buiActive["Join"] := Join[ a]

Tuple$TM /: Element$TM[p_,a_Tuple$TM] /; buiActive["IsElement"] && MemberQ[a,p] := True
Tuple$TM /: Element$TM[p_,a_Tuple$TM] /; buiActive["IsElement"] && isVariableFree[a] := MemberQ[a,p]

Tuple$TM /: max$TM[a_Tuple$TM] /; buiActive["Max"] && Max[a /. Tuple$TM -> List] := True
Tuple$TM /: max$TM[a_Tuple$TM] /; buiActive["Max"] && isVariableFree[a,Infinity] := Max[a /. Tuple$TM -> List]
Tuple$TM /: min$TM[a_Tuple$TM] /; buiActive["Min"] && Min[a /. Tuple$TM -> List] := True
Tuple$TM /: min$TM[a_Tuple$TM] /; buiActive["Min"] && isVariableFree[a,Infinity] := Min[a /. Tuple$TM -> List]

Tuple$TM /: BracketingBar$TM[ a_Tuple$TM] /; buiActive["Length"] && isSequenceFree[a] := Length[ a]

Tuple$TM /: Subscript$TM[ a_Tuple$TM, p:LeftArrow$TM[_, _]..] /; buiActive["ReplacePart"] && isSequenceFree[a] :=
	ReplacePart[ a, MapAt[# /. { Tuple$TM -> List}&, {p} /. LeftArrow$TM -> Rule, Table[{i,1},{i,Length[{p}]}]]]
forReplace[a_, s_] := Module[{anew := a, pnew},
  For[j = Length[s], j >= 1, j--,
   If[Length[s[[j]][[1]]] <= 0, pnew = {s[[j]][[1]]}, 
    pnew = s[[j]][[1]]];
   For[i = 1, i <= Length[pnew], i++, 
    anew = Replace[anew, pnew[[i]] -> s[[j]][[2]], Infinity]]];
  anew]
Tuple$TM /: Subscript$TM[ a_Tuple$TM, s:LeftArrowBar$TM[__,_]..] /; buiActive["Replace"] := forReplace[ a , {s}]

Tuple$TM /: Subscript$TM[ a_Tuple$TM, p__Integer] /; buiActive["Subscript"] := Subscript$TM[ a, Tuple$TM[ p]]
Tuple$TM /: Subscript$TM[ a_Tuple$TM, p_?isPositionSpec] /; buiActive["Subscript"] && isSequenceFree[a] := Extract[ a, p /. Tuple$TM -> List] /. List -> Tuple$TM

isPositionSpec[ _Integer] := True
isPositionSpec[ Tuple$TM[ p__]] := Apply[ And, Map[ isPositionSpec, {p}]]
isPositionSpec[ _] := False
isPositionSpec[ args___] := unexpected[ isPositionSpec, {args}]



(* ::Section:: *)
(* Domains and Data Types *)


(* amaletzk: Although buiActive is checked twice, I don't want to convert the pretty-printable
   Element$TM[] into isInteger[], unless there is a chance it gets simplified *)
\[DoubleStruckCapitalZ]$TM /: Element$TM[ x_, \[DoubleStruckCapitalZ]$TM] /; buiActive["IsElement"] && buiActive["isInteger"] := isInteger$TM[ x]
isInteger$TM[ _Integer] /; buiActive["isInteger"] := True
isInteger$TM[ True|False] /; buiActive["isInteger"] := False
isInteger$TM[ _Rational|_Real|_Complex] /; buiActive["isInteger"] := False
isInteger$TM[ _Set$TM|_Tuple$TM] /; buiActive["isInteger"] := False

\[DoubleStruckCapitalQ]$TM /: Element$TM[ x_, \[DoubleStruckCapitalQ]$TM] /; buiActive["IsElement"] && buiActive["isRational"] := isRational$TM[ x]
isRational$TM[ _Integer|_Rational] /; buiActive["isRational"] := True
isRational$TM[ True|False] /; buiActive["isRational"] := False
isRational$TM[ _Real|_Complex] /; buiActive["isRational"] := False
isRational$TM[ _Set$TM|_Tuple$TM] /; buiActive["isRational"] := False

\[DoubleStruckCapitalR]$TM /: Element$TM[ x_, \[DoubleStruckCapitalR]$TM] /; buiActive["IsElement"] && buiActive["isReal"] := isReal$TM[ x]
isReal$TM[ _Integer|_Rational|_Real] /; buiActive["isReal"] := True
isReal$TM[ True|False] /; buiActive["isReal"] := False
isReal$TM[ _Complex] /; buiActive["isReal"] := False
isReal$TM[ _Set$TM|_Tuple$TM] /; buiActive["isReal"] := False

isSet$TM[ _Set$TM] /; buiActive["isSet"] := True
isSet$TM[ True|False] /; buiActive["isSet"] := False
isSet$TM[ _Integer|_Rational|_Real|_Complex] /; buiActive["isSet"] := False
isSet$TM[ _Tuple$TM] /; buiActive["isSet"] := False

isTuple$TM[ _Tuple$TM] /; buiActive["isTuple"] := True
isTuple$TM[ True|False] /; buiActive["isTuple"] := False
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

CaseDistinction$TM[ c:Clause$TM[ _, _]..] /; buiActive["CaseDistinction"] := Piecewise[ Map[ clause2pw, {c}]]
clause2pw[ Clause$TM[ cond_, expr_]] := {expr, cond}



(* We assume that all lists not treated by the above constructs should in fact be sets *)
SetAttributes[ List$TM, HoldAll]
List$TM[ l___] := makeSet[l]

cleanupComputation[]
    
End[]
EndPackage[]
