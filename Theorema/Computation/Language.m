BeginPackage["Theorema`Computation`Language`"]

(*
   Load the same symbols like in Theorema`Language` so that all language constructs will be
   available in Computation context as well *)

Needs[ "Theorema`Common`"]
   
Map[ Get, FileNames[ "*.m", ToFileName[{$TheoremaDirectory, "Theorema", "Language", "LanguageData"}]]];

Begin[ "`Private`"]

activeComputationKB[_] := False

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

   
Plus$TM[ a__] /; buiActive["Plus"] := Plus[ a]
Times$TM[ a__] /; buiActive["Times"] := Times[ a]
Equal$TM[ a_, b_] /; buiActive["Equal"] := a == b
Less$TM[ a__] /; buiActive["Less"] := Less[ a]
LessEqual$TM[ a__] /; buiActive["LessEqual"] := LessEqual[ a]
Greater$TM[ a__] /; buiActive["Greater"] := Greater[ a]
GreaterEqual$TM[ a__] /; buiActive["GreaterEqual"] := GreaterEqual[ a]

Not$TM[ a_] /; buiActive["Not"] := Not[ a]
And$TM[ a__] /; buiActive["And"] := And[ a]
Or$TM[ a__] /; buiActive["Or"] := Or[ a]
Implies$TM[ a__] /; buiActive["Implies"] := Implies[ a]
Iff$TM[ a__] /; buiActive["Iff"] := Equivalent[ a]

ClearAll[ Forall$TM]
Scan[ SetAttributes[ #, HoldRest]&, {Forall$TM, Exists$TM}]
Scan[ SetAttributes[ #, HoldFirst]&, {SETRNG$, STEPRNG$}]

Forall$TM[ RNG$[ r_, s__], cond_, form_]/; buiActive["Forall"] := 
	Module[ {splitC},
		splitC = splitAnd[ cond, {r[[1]]}];
		With[ {rc = splitC[[1]], sc = splitC[[2]]},
			Forall$TM[ RNG$[r], rc, Forall$TM[ RNG$[s], sc, form]]
		]
	]

Forall$TM[ RNG$[ SETRNG$[ x_, A_Set$TM]], cond_, form_]/; buiActive["Forall"] :=
   	forallIteration[ {x, Apply[ List, A]}, cond, form] 

Forall$TM[ RNG$[ STEPRNG$[ x_, l_Integer, h_Integer, s_Integer]], cond_, form_]/; buiActive["Forall"] :=
   	forallIteration[ {x, l, h, s}, cond, form] 

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

Exists$TM[ RNG$[ SETRNG$[ x_, A_Set$TM]], cond_, form_]/; buiActive["Exists"] := 
	existsIteration[ {x, Apply[ List, A]}, cond, form]

Exists$TM[ RNG$[ STEPRNG$[ x_, l_Integer, h_Integer, s_Integer]], cond_, form_]/; buiActive["Exists"] := 
	existsIteration[ {x, l, h, s}, cond, form]

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
    
End[]
EndPackage[]