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

activeComputationKB[_] := False;

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


   
Plus$TM[ a__] /; buiActive["Plus"] := Plus[ a]
Times$TM[ a__] /; buiActive["Times"] := Times[ a]
Equal$TM[ a_, b_] /; buiActive["Equal"] := a == b
Less$TM[ a__] /; buiActive["Less"] := Less[ a]
LessEqual$TM[ a__] /; buiActive["LessEqual"] := LessEqual[ a]
Greater$TM[ a__] /; buiActive["Greater"] := Greater[ a]
GreaterEqual$TM[ a__] /; buiActive["GreaterEqual"] := GreaterEqual[ a]



(* ::Section:: *)
(* Logic *)


Not$TM[ a_] /; buiActive["Not"] := Not[ a]
And$TM[ a__] /; buiActive["And"] := And[ a]
Or$TM[ a__] /; buiActive["Or"] := Or[ a]
Implies$TM[ a__] /; buiActive["Implies"] := Implies[ a]
Iff$TM[ a__] /; buiActive["Iff"] := Equivalent[ a]

rangeToIterator[ SETRNG$[ x_, A_Set$TM]] := { x, Apply[ List, A]}
rangeToIterator[ STEPRNG$[ x_, l_Integer, h_Integer, s_Integer]] := {x, l, h, s}
rangeToIterator[ _] := $Failed
rangeToIterator[ args___] := unexpected[ rangeToIterator, {args}]

ClearAll[ Forall$TM, Exists$TM, SequenceOf$TM]
Scan[ SetAttributes[ #, HoldRest]&, {Forall$TM, Exists$TM, SequenceOf$TM}]
Scan[ SetAttributes[ #, HoldFirst]&, {SETRNG$, STEPRNG$}]

Forall$TM[ RNG$[ r_, s__], cond_, form_]/; buiActive["Forall"] := 
	Module[ {splitC},
		splitC = splitAnd[ cond, {r[[1]]}];
		With[ {rc = splitC[[1]], sc = splitC[[2]]},
			Forall$TM[ RNG$[r], rc, Forall$TM[ RNG$[s], sc, form]]
		]
	]

Forall$TM[ RNG$[ r:_SETRNG$|_STEPRNG$], cond_, form_]/; buiActive["Forall"] :=
	Module[ {iter},
   		forallIteration[ iter, cond, form] /; (iter = rangeToIterator[ r]) =!= $Failed
	]

(* We introduce local variables for the iteration so that we can substitute only for free occurrences.
   Technically, Mathematica coulf iterate the VAR$[..] directly, but it would substitute ALL occurrences then *)
SetAttributes[ forallIteration, HoldRest]
forallIteration[ {x_, iter__}, cond_, form_] :=
    Module[ {uneval = {}, ci, sub},
        Catch[
            Do[ If[ TrueQ[ cond],
                    ci = True,
                    ci = ReleaseHold[ substituteFree[ Hold[ cond], {x -> i}]]
                ];
                If[ ci,
                    sub = ReleaseHold[ substituteFree[ Hold[ form], {x -> i}]];
                    If[ sub,
                        Continue[],
                        Throw[ False],
                        AppendTo[ uneval, sub]
                    ],
                    Continue[],
                    AppendTo[ uneval, Implies$TM[ ci, ReleaseHold[ substituteFree[ Hold[ form], {x -> i}]]]]
                ],
                { i, iter}
            ];
            makeConjunction[ uneval, And$TM]
        ]
    ]
    
Exists$TM[ RNG$[ r_, s__], cond_, form_]/; buiActive["Exists"] := 
	Module[ {splitC},
		splitC = splitAnd[ cond, {r[[1]]}];
		With[ {rc = splitC[[1]], sc = splitC[[2]]},
			Exists$TM[ RNG$[r], rc, Exists$TM[ RNG$[s], sc, form]]
		]
	]

Exists$TM[ RNG$[ r:_SETRNG$|_STEPRNG$], cond_, form_]/; buiActive["Exists"] :=
	Module[ {iter},
   		existsIteration[ iter, cond, form] /; (iter = rangeToIterator[ r]) =!= $Failed
	]

SetAttributes[ existsIteration, HoldRest]
existsIteration[ {x_, iter__}, cond_, form_] :=
    Module[ {uneval = {}, ci, sub},
        Catch[
            Do[ If[ TrueQ[ cond],
                    ci = True,
                    ci = ReleaseHold[ substituteFree[ Hold[ cond], {x -> i}]]
                ];
                If[ ci,
                    sub = ReleaseHold[ substituteFree[ Hold[ form], {x -> i}]];
                    If[ sub,
                        Throw[ True],
                        Continue[],
                        AppendTo[ uneval, sub]
                    ],
                    Continue[],
                    AppendTo[ uneval, And$TM[ ci, ReleaseHold[ substituteFree[ Hold[ form], {x -> i}]]]]
                ],
                 {i, iter}
             ];
            makeDisjunction[ uneval, Or$TM]
        ]
    ]

(* Instead of nesting SequenceOf expressions and then concatenating the sequences, we construct a multi-iterator from the given ranges *)
SequenceOf$TM[ RNG$[ r__], cond_, form_] :=
	Module[ {s},
		s /; buiActive["SequenceOf"] && (s = sequenceOfIteration[ Map[ rangeToIterator, {r}], cond, form]) =!= $Failed
	]

(* The multi-iterator is used in a Do-loop. Local variables have to be introduced to be substituted during the iteration *)   	
SetAttributes[ sequenceOfIteration, HoldRest]
sequenceOfIteration[ iter:{__List}, cond_, form_] :=
    Module[ {seq = {}, ci, comp, tmpVar = Table[ Unique[], {Length[ iter]}], iVar = Map[ First, iter]},
        Catch[
            With[ {locIter = Apply[ Sequence, MapThread[ ReplacePart[ #1, 1 -> #2]&, {iter, tmpVar}]], locSubs = Thread[ Rule[ iVar, tmpVar]]},
                Do[ If[ TrueQ[ cond],
                        ci = True,
                        ci = ReleaseHold[ substituteFree[ Hold[ cond], locSubs]]
                    ];
                    If[ ci,
                        comp = ReleaseHold[ substituteFree[ Hold[ form], locSubs]];
                        AppendTo[ seq, comp],
                        Continue[],
                        Throw[ $Failed]
                    ],
                    locIter
                ]
            ];
            Apply[ Sequence, seq]
        ]
    ]
sequenceOfIteration[ iter_List, cond_, form_] := $Failed
sequenceOfIteration[ args___] := unexpected[ sequenceOfIteration, {args}]


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
Set$TM /: ScriptCapitalP$TM[ a_Set$TM] /; buiActive["PowerSet"] := Subsets[ a ] /. List -> Set$TM
Set$TM /: BracketingBar$TM[ a_Set$TM] /; buiActive["Cardinality"] && isSequenceFree[a] := Length[ a]
Set$TM /: max$TM[ a_Set$TM] /; buiActive["MaximumElementSet"] := Max[a /. Set$TM -> List]
Set$TM /: min$TM[ a_Set$TM] /; buiActive["MinimumElementSet"] := Min[ a/. Set$TM -> List]


(* ::Section:: *)
(* Tuples *)


Tuple$TM /: BracketingBar$TM[ a_Tuple$TM] /; buiActive["Length"] && isSequenceFree[a] := Length[ a]
Tuple$TM /: Subscript$TM[ a_Tuple$TM, p__Integer] /; buiActive["Subscript"] && isSequenceFree[a] := Part[ a, p]
Tuple$TM /: Subscript$TM[ a_Tuple$TM, p__LeftArrow$TM] /; buiActive["ReplacePart"] && isSequenceFree[a] :=
	ReplacePart[ a, {p /. {LeftArrow$TM -> Rule, Tuple$TM -> List}}]



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

(* We assume that all lists not treated by the above constructs should in fact be sets *)
SetAttributes[ List$TM, HoldAll]
List$TM[ l___] := makeSet[l]

cleanupComputation[]
    
End[]
EndPackage[]
