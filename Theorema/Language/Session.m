(* Theorema 
    Copyright (C) 2010 The Theorema Group

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

BeginPackage["Theorema`Language`Session`"];

Needs["Theorema`Common`"];
Needs["Theorema`Language`"];
Needs["Theorema`Interface`Language`"];

Begin["`Private`"]


(* ::Section:: *)
(* Preprocessing *)

(* Define "freshNames[]", "freshNamesProg[]" as below, because otherwise parts with "Program" don't work. *)
(* 'dropWolf' specifies whether prefix "\[Wolf]" should be dropped from symbols for getting the corresponding Mma function.
	This should in fact only happen in computation-cells but not in formula cells, in order to prevent evaluation.
	Function 'transferToComputation' takes care of dropping "\[Wolf]" in function definitions that originate from formulas. *)
freshNames[ expr_Hold, dropWolf_:False] :=
	Module[ {symPos, repl, progPos, progSymPos, remSyms},
		progPos = Position[ expr, (Theorema`Computation`Language`Program|Program)[ _]];
		(* There are certain expressions, into which we do not want to go deeper for substituting fresh names.
		   An example is a META$[__] expression representing a meta-variable in a proof, which has a list as
		   its 3rd parameter. Going into it would turn the list into a Set$TM ...
		   If other cases occur in the future, just add a suitable transformation here BEFORE the replaceable
		   positions are computed. *)
		symPos = DeleteCases[ Position[ expr /. {(h:(Theorema`Computation`Language`META$|META$))[ __] -> h[]}, _Symbol], {0}, {1}, 1];
		progSymPos = Select[ symPos, isSubPositionOfAny[ #, progPos]&];
		(* Use 'Replace' instead of 'Map', otherwise there are problems with 'Slot' appearing in the Theorema expression. *)
		(* 'freshSymbol' and 'freshSymbolProg' sow all symbols (wrapped inside 'Hold') which shall be removed later. *)
		{repl, remSyms} =
			Reap[ Join[ Replace[ Complement[ symPos, progSymPos], p_ :> (p -> freshSymbol[ Extract[ expr, p, Hold], dropWolf]), {1}],
					Replace[ progSymPos, p_ :> (p -> freshSymbolProg[ Extract[ expr, p, Hold], dropWolf]), {1}]], "remove"];
		(* The "FlattenAt" simply replaces every "Program[p]" by "p". *)
		repl = FlattenAt[ ReplacePart[ expr, repl], progPos];
		(* We remove the symbols in 'remSyms' only *after* they are replaced in 'expr' above. *)
		Remove @@ Join @@ DeleteDuplicates[ Join @@ remSyms];
		repl
	]
freshNames[ args___] := unexpected[ freshNames, {args}]


isSubPositionOfAny[ pos_List, l_List] := Catch[ (Scan[ If[isSubPosition[pos, #], Throw[True]]&, l]; False)]
isSubPosition[ l1_List, l2_List] :=
	With[{len = Length[l2]}, 
 		Length[l1] >= len && l1[[1 ;; len]] === l2[[1 ;; len]]
 	]
(*
freshSymbols uses ToExpression in order to generate a symbol. If, e.g. in
a computation, we use knowledge x==1, then the generated symbol x$TM has a 
value and ToExpression evaluates. Therefore, we wrap the fresh symbol in
Hold (using ToExpression[..., Hold]) and process the resulting expression
with the expectation that all symbols are wrapped in Hold. (-> markVariables, etc.)
*)

freshSymbol[ sym:Hold[ s_Symbol], dropWolf_] :=
    Module[ {name},
        Switch[ Unevaluated[ s],
            (* We use ToExpression in order to have the symbol generated in the right context
               depending on whether we are in a computation or not *)
            _?isMathematicalConstant, s,
            (* processing the number domain symbols by MakeExpression does not work, I think MakeExpression is only
               applied to boxes and not to individual symbols. We convert them to respective ranges here. *)
            Theorema`Computation`Language`\[DoubleStruckCapitalN]|\[DoubleStruckCapitalN],
            	ToExpression[ "IntegerInterval$TM[ 1, Infinity, True, False]"],
            Theorema`Computation`Language`\[DoubleStruckCapitalZ]|\[DoubleStruckCapitalZ],
            	ToExpression[ "IntegerInterval$TM[ -Infinity, Infinity, False, False]"],
            Theorema`Computation`Language`\[DoubleStruckCapitalQ]|\[DoubleStruckCapitalQ],
            	ToExpression[ "RationalInterval$TM[ -Infinity, Infinity, False, False]"],
            Theorema`Computation`Language`\[DoubleStruckCapitalR]|\[DoubleStruckCapitalR],
            	ToExpression[ "RealInterval$TM[ -Infinity, Infinity, False, False]"],
            Theorema`Computation`Knowledge`\[EmptySet]|Theorema`Knowledge`\[EmptySet],
            	Sow[ sym, "remove"]; ToExpression[ "Set$TM[]"],
            DoubleLongRightArrow|DoubleRightArrow, ToExpression[ "Implies$TM"],
            DoubleLongLeftRightArrow|DoubleLeftRightArrow|Equivalent, ToExpression[ "Iff$TM"],
        	SetDelayed, ToExpression[ "EqualDef$TM"],
        	Set, ToExpression[ "Assign$TM"],
        	Wedge, ToExpression[ "And$TM"],
        	Vee, ToExpression[ "Or$TM"],
        	makeSet, ToExpression[ "Set$TM"],
        	AngleBracket|List, ToExpression[ "Tuple$TM"],	(* Attention! If this changes, lists must be turned into tuples in 'renameToStandardContext! *)
        	Inequality, ToExpression[ "OperatorChain$TM"],
        	_,
        	name = ToString[ Unevaluated[ s]];
        	Which[
    			StringTake[ name, -1] === "$" || (StringLength[ name] >= 3 && StringTake[ name, -3] === "$TM"),
    			s,
    		(*else*)
    			StringLength[ name] >= 2 && StringTake[ name, 1] === "\[Wolf]" && dropWolf,
    			Sow[ sym, "remove"];
    			ToExpression[ StringDrop[ name, 1], InputForm, Hold],
    		(*else*)
    			True,
    			If[ StringMatchQ[ Context[ Unevaluated[ s]], "Theorema`Knowledge`"|"Theorema`Computation`Knowledge`"], Sow[ sym, "remove"]];
    			ToExpression[ name <> "$TM", InputForm, Hold]
        	]
        ]
    ]
freshSymbol[ args___] := unexpected[ freshSymbol, {args}]

freshSymbolProg[ sym:Hold[ s_Symbol], dropWolf_] :=
    Module[ {name},
        Switch[ Unevaluated[ s],
            _?isMathematicalConstant, s,
            Theorema`Computation`Language`\[DoubleStruckCapitalN]|\[DoubleStruckCapitalN],
            	ToExpression[ "IntegerInterval$TM[1, DirectedInfinity[1], True, False]"],
            Theorema`Computation`Language`\[DoubleStruckCapitalZ]|\[DoubleStruckCapitalZ],
            	ToExpression[ "IntegerInterval$TM[DirectedInfinity[-1], DirectedInfinity[1], False, False]"],
            Theorema`Computation`Language`\[DoubleStruckCapitalQ]|\[DoubleStruckCapitalQ],
            	ToExpression[ "RationalInterval$TM[DirectedInfinity[-1], DirectedInfinity[1], False, False]"],
            Theorema`Computation`Language`\[DoubleStruckCapitalR]|\[DoubleStruckCapitalR],
            	ToExpression[ "RealInterval$TM[DirectedInfinity[-1], DirectedInfinity[1], False, False]"],
            Theorema`Computation`Knowledge`\[EmptySet]|Theorema`Knowledge`\[EmptySet],
            	Sow[ sym, "remove"]; ToExpression[ "Set$TM[]"],	(* We always interpret '\[EmptySet]' as an empty *set* rather than an empty *list*, even inside a program. *)
        	Set, ToExpression[ "Assign$TM"],
        	makeSet, ToExpression[ "List$TM"],
        	Inequality, ToExpression[ "OperatorChain$TM"],
        	_,
        	name = ToString[ Unevaluated[ s]];
        	Which[
    			StringTake[ name, -1] === "$" || (StringLength[ name] >= 3 && StringTake[ name, -3] === "$TM"),
    			s,
    		(*else*)
    			StringLength[ name] >= 2 && StringTake[ name, 1] === "\[Wolf]" && dropWolf,
    			Sow[ sym, "remove"];
    			ToExpression[ StringDrop[ name, 1], InputForm, Hold],
    		(*else*)
    			True,
    			If[ StringMatchQ[ Context[ Unevaluated[ s]], "Theorema`Knowledge`"|"Theorema`Computation`Knowledge`"], Sow[ sym, "remove"]];
    			ToExpression[ name <> "$TM", InputForm, Hold]
        	]
        ]
    ]
freshSymbolProg[ args___] := unexpected[ freshSymbolProg, {args}]

markVariables[ Hold[ QU$[ r_RNG$, expr_]]] :=
    Module[ {s, seq, vars, violating, out},
        (* all symbols sym specified as variables in r are translated into VAR$[sym]
           we substitute all symbols with matching "base name" (neglecting the context!) so that also
           symbols in different context get substituted. This is important when processing archives, because
           global variables in an archive live in the archive's private context, whereas the global declaration
           lives in the context of the loading notebook/archive. With the substitution below, the private`sym becomes 
           a VAR$[loading`sym] *)
           
        (* We have to keep the distinction between sequence variables and individual variables,
           because "SymbolName[]" would give an error if applied to compound expressions.
        *)
        vars = specifiedVariables[ r];
        seq = Cases[vars, (SEQ0$|SEQ1$)[ _]];
        vars = Complement[ vars, seq];
        violating = checkForValidRange[ seq, vars, Hold[ r], SEQ0$|SEQ1$];
        If[ violating =!= {},
        	(* If this function is called in 'processEnvironment', 'updateKnowledgeBase' will remove the old version of the formula from '$tmaEnv'. *)
        	notification[ translate[ "invalidRange"], DisplayForm[ ToBoxes[ violating /. Hold -> HoldForm, TheoremaForm]]];
			Throw[ $Failed]
        ];
        s = Join[ Map[ (h:(SEQ0$|SEQ1$))[ Hold[ sym_Symbol]] /; SymbolName[ Unevaluated[ sym]] === symbolNameHold[ #] -> VAR$[ h[ #]]&, seq[[All, 1]]],
        		  Map[ Hold[ sym_Symbol] /; SymbolName[ Unevaluated[ sym]] === symbolNameHold[ #] -> VAR$[ #]&, vars]];
        out = markVariables[ Hold[ expr]];
        Switch[ out,
        	Hold[ _[ ___]],
        	(* We must NOT replace in the head! Otherwise, funny things would happen if a variable bound by a quantifier has the same name as the quantifier ... *)
        	applyHold[ Extract[ out, {1, 0}, Hold], replaceAllExcept[ Delete[ out, {1, 0}], s, {}, Heads -> {SEQ0$, SEQ1$, VAR$, FIX$}]],
        	_,
        	replaceAllExcept[ out, s, {}, Heads -> {SEQ0$, SEQ1$, VAR$, FIX$}]
        ]
    ]

markVariables[ Hold[ Theorema`Computation`Language`QU$[ r_Theorema`Computation`Language`RNG$, expr_]]] :=
    Module[ {s, seq, vars, violating, out},
    	vars = specifiedVariables[ Hold[ r]];
        seq = Cases[vars, (Theorema`Computation`Language`SEQ0$|Theorema`Computation`Language`SEQ1$)[ _]];
        vars = Complement[ vars, seq];
        violating = checkForValidRange[ seq, vars, Hold[ r], Theorema`Computation`Language`SEQ0$|Theorema`Computation`Language`SEQ1$];
        If[ violating =!= {},
        	(* If this function is called in 'processEnvironment', 'updateKnowledgeBase' will remove the old version of the formula from '$tmaEnv'. *)
        	notification[ translate[ "invalidRange"], DisplayForm[ ToBoxes[ violating /. Hold -> HoldForm, TheoremaForm]]];
			Throw[ $Failed]
        ];
        s = Join[ Map[ (h:(Theorema`Computation`Language`SEQ0$|Theorema`Computation`Language`SEQ1$))[ Hold[ sym_Symbol]] /; SymbolName[ Unevaluated[ sym]] === symbolNameHold[ #] -> Theorema`Computation`Language`VAR$[ h[ #]]&, seq[[All, 1]]],
        		  Map[ Hold[ sym_Symbol] /; SymbolName[ Unevaluated[ sym]] === symbolNameHold[ #] -> Theorema`Computation`Language`VAR$[ #]&, vars]];
       	out = markVariables[ Hold[ expr]];
       	Switch[ out,
        	Hold[ _[ ___]],
        	applyHold[
        		Extract[ out, {1, 0}, Hold],
        		replaceAllExcept[ Delete[ out, {1, 0}], s, {}, Heads -> {Theorema`Computation`Language`SEQ0$, Theorema`Computation`Language`SEQ1$, Theorema`Computation`Language`VAR$, Theorema`Computation`Language`FIX$}]
        	],
        	_,
        	replaceAllExcept[ out, s, {}, Heads -> {Theorema`Computation`Language`SEQ0$, Theorema`Computation`Language`SEQ1$, Theorema`Computation`Language`VAR$, Theorema`Computation`Language`FIX$}]
        ]
    ]
    
markVariables[ Hold[ h_[ e___]]] := applyHold[
  		markVariables[ Hold[ h]],
  		markVariables[ Hold[ e]]]

markVariables[ Hold[ f_, t__]] := joinHold[
  		markVariables[ Hold[ f]],
  		markVariables[ Hold[ t]]]

markVariables[ Hold[]] := Hold[]

markVariables[ Hold[e_]] := Hold[ e]

markVariables[ args___] := unexpected[ markVariables, {args}]

(* "checkForValidRange[ seq, vars, r, patt ]" collects all variables which appear more than once in the range "r". If there are any, the range is invalid. *)
checkForValidRange[ seq_List, vars_List, r_Hold, patt_] :=
	Module[ {out = {}, tmp},
        Scan[ With[ {h = Head[ #], name = symbolNameHold[ First[ #]]},
        		If[ Count[ r, h[ Hold[ sym_Symbol]] /; SymbolName[ Unevaluated[ sym]] === name, {0, Infinity}, Heads -> True] > 1,
        			AppendTo[ out, #]
        		]
        	]&,
        	seq
        ];
        tmp = r /. (h:patt)[ _] :> h; (* Sequence variables are different from individual variables, even if they have the same name. *)
        Scan[ With[ {name = symbolNameHold[ #]},
        		If[ Count[ tmp, Hold[ sym_Symbol] /; SymbolName[ Unevaluated[ sym]] === name, {0, Infinity}, Heads -> True] > 1,
        			AppendTo[ out, #]
        		]
        	]&,
        	vars
        ];
        out
	]
	
addVarPrefixes[ expr_] :=
	Module[ {vp = Position[ expr, (VAR$|Theorema`Computation`Language`VAR$)[ _]], repl},
		repl = MapThread[ (#1 -> addSinglePrefix[ #2])&, {vp, Extract[ expr, vp, Hold]}];
		ReplacePart[ expr, repl]
	]
addSinglePrefix[ Hold[ sym_Symbol]] :=
	Module[ {n = SymbolName[ Unevaluated[ sym]]},
		If[ StringLength[ n] < 5 || StringTake[ n, 4] =!= "VAR$",
			ToExpression[ "VAR$" <> n, InputForm, Hold],
			Hold[ sym]
		]
	]
addSinglePrefix[ Hold[ (h:(VAR$|SEQ0$|SEQ1$|Theorema`Computation`Language`VAR$|Theorema`Computation`Language`SEQ0$|Theorema`Computation`Language`SEQ1$))[ x_]]] :=
	h[ addSinglePrefix[ Hold[ x]]]
addSinglePrefix[ Hold[ x_Hold]] := addSinglePrefix[ x]

(* "addAbbrevPositions[ expr ]" adds the positions of the free occurrences of all ABBREV-variables in 'expr' to their respective ABBRVRNG$-ranges.
	Note that multiranges are temporarily split into individual ranges, and that an invisible 'Hold' is assumed to be wrapped around the quantified expressions,
	such that later in computation the positions are just what they should be. *)
addAbbrevPositions[ expr_Hold] :=
	Module[ {p = Position[ expr, (Abbrev$TM|Theorema`Computation`Language`Abbrev$TM)[ _, _]], new = expr},
		Scan[ (new = Delete[ ReplacePart[ new, # -> newAbbrev[ Extract[ new, #, Hold]]], Append[ #, 0]])&, p];
		new
	]
addAbbrevPositions[ expr_] := ReleaseHold[ addAbbrevPositions[ Hold[ expr]]]

newAbbrev[ Hold[ (q:(Abbrev$TM|Theorema`Computation`Language`Abbrev$TM))[ (rng:(RNG$|Theorema`Computation`Language`RNG$))[ (ar:(ABBRVRNG$|Theorema`Computation`Language`ABBRVRNG$))[ l_, r_], rest__], expr_]]] :=
	Module[ {tmp = newAbbrev[ Hold[ q[ rng[ rest], expr]]]},
		With[ {pos = getFreePositions[ l, tmp]},
			ReplacePart[ Insert[ tmp, Hold[ l, r, pos], {1, 1, 1}], {1, 1, 1, 0} -> ar]
		]
	]
newAbbrev[ Hold[ (q:(Abbrev$TM|Theorema`Computation`Language`Abbrev$TM))[ (rng:(RNG$|Theorema`Computation`Language`RNG$))[ (ar:(ABBRVRNG$|Theorema`Computation`Language`ABBRVRNG$))[ l_, r_]], expr_]]] :=
	With[ {pos = getFreePositions[ l, Hold[ expr]]},
		Hold[ q[ rng[ ar[ l, r, pos]], expr]]
	]
newAbbrev[ expr_Hold] := expr

getFreePositions[ var_, expr_] :=
	Replace[ Replace[ var, analyzeVars[ expr, "FreeOnly" -> True, "Pattern" -> var]], var -> {}]

(*
	makeTmaExpression[ e] and makeTmaExpressionFromBoxes[ box] are the combinations of functions that we export to be used in other places if needed.
*)
SetAttributes[ makeTmaExpression, HoldFirst]
makeTmaExpression[ e_] := makeTmaExpression[ e, True, ReleaseHold]
makeTmaExpression[ e_, True, post_] :=
	Block[ {$ContextPath = Join[ {"Theorema`Language`"}, $TheoremaArchives, $ContextPath]},
		makeTmaExpression[ e, False, post]
	]
makeTmaExpression[ e_Hold, False, post_] :=
	Catch[ post[ addAbbrevPositions[ Replace[ addVarPrefixes[ markVariables[ freshNames[ e]]], Hold[ x_] :> x, Infinity, Heads -> True]]]]
makeTmaExpression[ e_, False, post_] := makeTmaExpression[ Hold[ e], post]
makeTmaExpression[ args___] := unexpected[ makeTmaExpression, {args}]

makeTmaExpressionFromBoxes[ box_, pre_:removeRedundantBoxes, post_:ReleaseHold] :=
	Block[ {$parseTheoremaExpressions = True, $ContextPath = Join[ {"Theorema`Language`"}, $TheoremaArchives, $ContextPath]},
		If[ !inArchive[] && $Context =!= "Theorema`Knowledge`", Begin[ "Theorema`Knowledge`"]];
		With[ {tmp = Quiet[ Check[ ToExpression[ pre[ box], StandardForm, Hold], $Failed]]},
		With[ {out = If[ MatchQ[ tmp, _Hold], makeTmaExpression[ tmp, False, post], $Failed]},
			If[ !inArchive[] && $Context === "Theorema`Knowledge`", End[]];
			out
		]]
	]
makeTmaExpressionFromBoxes[ args___] := unexpected[ makeTmaExpressionFromBoxes, {args}]

(* processing Theorema expressions essentially works on Hold-expressions, where symbols inside are again
   wrapped into Hold in order to prevent values to enter the expressions during their processing e.g. in a computation.
   When processing is finished, the Holds must be removed again. We first remove the inner Holds and finally remove the outer head Hold.
*)
removeHold[ expr_Hold] :=
	(* level infinity does not apply to the main head. This is only removed with ReleaseHold. *)
	ReleaseHold[ Replace[ expr, Hold[ x_] -> x, Infinity, Heads -> True]]
removeHold[ args___] := unexpected[ removeHold, {args}]

symbolNameHold[ Hold[ s_Symbol]] := SymbolName[ Unevaluated[ s]]
symbolNameHold[ args___] := unexpected[ symbolNameHold, {args}]


openGlobalDeclaration[ expr_] :=
    Module[ {},
        $parseTheoremaGlobals = True;
        $ContextPath = Join[ {"Theorema`Language`"}, $TheoremaArchives, $ContextPath];
        If[ !inArchive[] && $Context =!= "Theorema`Knowledge`", Begin[ "Theorema`Knowledge`"]];
        expr
    ]
openGlobalDeclaration[ args___] := unexpected[ openGlobalDeclaration, {args}]

closeGlobalDeclaration[] :=
    Module[ {},
		If[ !inArchive[] && $Context === "Theorema`Knowledge`", End[]];
		(* Restore context path that has been modified in openEnvironment *)
		$ContextPath = DeleteCases[ $ContextPath, Apply[ Alternatives, Join[ {"Theorema`Language`"}, $TheoremaArchives]]];
        $parseTheoremaGlobals = False;
    ]
closeGlobalDeclaration[ args___] := unexpected[ closeGlobalDeclaration, {args}]

getGlobalDeclaration[ file_String] := Replace[ file, $globalDeclarations]
getGlobalDeclaration[ file_String, id_Integer] := Cases[ getGlobalDeclaration[ file], {id, _, d_} -> d, {1}, 1]
getGlobalDeclaration[ file_String, l_List] := 
	(* Mapping over l ensures the order of extracted definitions to match the order of ids in l *)
	Apply[ Join, Map[ getGlobalDeclaration[ file, #]&, l]]
getGlobalDeclaration[ args___] := unexpected[ getGlobalDeclaration, {args}]

putGlobalDeclaration[ file_String, id_Integer, pos_List, nb_Notebook, decl_] :=
	Module[ {posF, posId, allDeclFile, allDeclPos},
		(* in case of an extension domain, we must generate the default definition that redirects to the original domain *)
		processDomainDefinition[ decl, file, id];
		posF = Position[ $globalDeclarations, file -> _, {1}, 1];
		If[ posF === {},
			PrependTo[ $globalDeclarations, file -> {{id, pos, decl}}],
			allDeclPos = Append[ posF[[1]], 2];
			allDeclFile = Extract[ $globalDeclarations, allDeclPos];
			posId = Position[ allDeclFile, {id, __}, {1}, 1];
			If[ posId === {},
				(* before we add the new one, we have to update positions in the existing declarations *)
				allDeclFile = updateGlobalDeclarations[ allDeclFile, pos, nb];
				$globalDeclarations = ReplacePart[ $globalDeclarations, allDeclPos -> Append[ allDeclFile, {id, pos, decl}]],
				(* else: an entry for id already exists *)
				If[ Extract[ allDeclFile, Append[ posId[[1]], 2]] =!= pos,
					(* the new position is NOT the same as the original one: update positions in the existing declarations *)
					allDeclFile = updateGlobalDeclarations[ allDeclFile, pos, nb]
				];
				allDeclFile = ReplacePart[ allDeclFile, posId[[1]] -> {id, pos, decl}];
				$globalDeclarations = ReplacePart[ $globalDeclarations, allDeclPos -> allDeclFile]
			]
		]
	]
putGlobalDeclaration[ args___] := unexpected[ putGlobalDeclaration, {args}]

updateGlobalDeclarations[ decl_List, pos_List, nb_Notebook] :=
	Module[{declCellPos},
		declCellPos = Select[ Position[ nb, Cell[ _, "GlobalDeclaration", ___]], occursBelow[ pos, #]&];
		declCellPos = Map[ {#, Options[ Extract[ nb, #], CellID]}&, declCellPos];
		Map[ updateCachedGlobalPos[ declCellPos, #]&, decl]
	]
updateGlobalDeclarations[ args___] := unexpected[ updateGlobalDeclarations, {args}]

updateCachedGlobalPos[ {___, {posNew_, {CellID -> id_}}, ___}, {id_, _, decl_}] := {id, posNew, decl}
updateCachedGlobalPos[ _List, orig_List] := orig
updateCachedGlobalPos[ args___] := unexpected[ updateCachedGlobalPos, {args}]

resyncGlobals[ file_String] :=
	Module[ {nb, pos, updDecl},
		nb = Select[ Notebooks[], CurrentValue[ #, "NotebookFullFileName"] === file&, 1];
		pos = Position[ $globalDeclarations, file -> _, {1}, 1];
		If[ nb =!= {} && pos =!= {},
			pos = Append[ pos[[1]], 2];
			updDecl = updateGlobalDeclarations[ Extract[ $globalDeclarations, pos], {0}, NotebookGet[ nb[[1]]]];
			$globalDeclarations = ReplacePart[ $globalDeclarations, pos -> updDecl]
		];
	]
resyncGlobals[ args___] := unexpected[ resyncGlobals, {args}]


(* For an extension domain, we do something, otherwise nothing needs to be done. There must not be an unexpected[...] *)
processDomainDefinition[ d:Hold[ domainConstruct$TM][ dom_, RNG$[ DOMEXTRNG$[ VAR$[ new_Hold], base_]]], file_String, id_Integer] := 
	Module[ {extDef}, 
		extDef = Forall$TM[ RNG$[ SIMPRNG$[ VAR$[ Theorema`Knowledge`op$TM]]], 
				notContainedIn[ VAR$[ Theorema`Knowledge`op$TM], opDefInDom[ dom]],
				Equal$TM[ DomainOperation$TM[ new, VAR$[ Theorema`Knowledge`op$TM]], DomainOperation$TM[ base, VAR$[ Theorema`Knowledge`op$TM]]]];
		(* we store it to be finalized with the first real def that goes into the environment -> updateKnowledgeBase 
		   Still, we prepare the formula here, because here is exactly the time to be sure that we have a domain extension.
		   If we would do all in updateKnowledgeBase, we'd have to fiddle around to find out whether we have a domain def or not.
		   On the other hand, we don't finalize the process here, because there may be aouter global quantifiers that need to be applied,
		   which would be difficult to find out here. We don't want to apply declarations to declarations ... *)
		$tmaDefaultDomainDef[ d] = {extDef, cellIDLabel[ id], sourceLabel[ file]};
		(* we should set the CellTags to cellID *)
	]

$tmaDefaultDomainDef[_] := {}
SetAttributes[ notContainedIn, HoldAll];
	
SetAttributes[ processGlobalDeclaration, HoldAll];
processGlobalDeclaration[ x_] := 
	Module[ {nb = EvaluationNotebook[], id, file, nbExpr, newFrameLabel, decl},
		SelectionMove[ nb, All, EvaluationCell];
		id = CurrentValue[ "CellID"];
		file = CurrentValue[ nb, "NotebookFullFileName"];
		newFrameLabel = With[ {fid = {file, id}},
			Cell[ BoxData[
				ButtonBox[ "\[Times]", Evaluator -> Automatic, Appearance -> None, ButtonFunction :> removeGlobal[ fid]]]]
		];
		SetOptions[ NotebookSelection[ nb],
			CellTags -> {cellIDLabel[ id]}, ShowCellTags -> False,
			CellFrameLabels -> {{None, newFrameLabel}, {None, None}}];
		nbExpr = NotebookGet[ nb];
		decl = ReleaseHold[ Catch[ markVariables[ freshNames[ Hold[ x]]]]];
		If[ decl =!= $Failed, 
			putGlobalDeclaration[ file, id, evaluationPosition[ nb, nbExpr, id], nbExpr, decl];
		];
		(* "Abbrev" cannot appear in global declarations, hence no need to call "addAbbrevPositions". *)
		SelectionMove[ nb, After, Cell];
	]
processGlobalDeclaration[ args___] := unexpected[ processGlobalDeclaration, {args}]

SetAttributes[ processEnvironment, HoldAll];
processEnvironment[ Theorema`Language`nE] := Null

processEnvironment[ x_] :=
    Module[ {nb = EvaluationNotebook[], nbFile, nbExpr, key, tags, globDec, pos, cellpos},
    	(* select current cell: we need to refer to this selection when we set the cell options *)
		SelectionMove[ nb, All, EvaluationCell];
    	{key, tags} = adjustFormulaLabel[ nb];
		(* Perform necessary actions on the whole notebook *)
		nbFile = CurrentValue[ nb, "NotebookFullFileName"];
		adjustEnvironment[ nb, nbFile];
		If[ $refreshBrowser,
			(* $refreshBrowser is set in openEnvironment, it basically depends on how long ago the last evaluation has been.
			   If browser need not refresh then this indicates that we are in a multi-cell evaluation. In this case we do not get a fresh
			   nbExpr, otherwise yes, because nb might have changed (been edited) *)
        	nbExpr = NotebookGet[ nb];
        	(* For the outside, we also store the filename *)
        	pos = Position[ $TMAcurrentEvalNB, {nbFile, _}, {1}, 1];
        	If[ pos === {},
        		(* usually, if the notebook has been opened regulary, this should never be the case.
        		   But e.g. after a kernel quit and restart it might be empty ... *)
        		$TMAcurrentEvalNB = {{nbFile, nbExpr}},
        		(* else *)
        		$TMAcurrentEvalNB = ReplacePart[ $TMAcurrentEvalNB, pos -> {nbFile, nbExpr}]
        	],
        	(* else: we are most probably in a multi-cell evaluation. Need not get new nbExpr. Cases MUST find sth, First must work. *)
        	nbExpr = First[ Cases[ $TMAcurrentEvalNB, {nbFile, e_} -> e, {1}, 1]]
		];
		(* extract the global declarations that are applicable in the current evaluation *)
		cellpos = evaluationPosition[ nb, nbExpr];
		globDec = applicableGlobalDeclarations[ nb, nbExpr, cellpos];
		(* process the expression according the Theorema syntax rules and add it to the KB
		   ReleaseHold will remove the outer Hold but leave the Holds around fresh symbols *)
        updateKnowledgeBase[ Catch[ ReleaseHold[ markVariables[ freshNames[ Hold[ x]]]]], key, globDec, cellTagsToString[ tags], cellTagsToFmlTags[ tags], cellpos];
        (* Positions of abbreviations are added in "updateKnowledgeBase". *)
        SelectionMove[ nb, After, Cell];
    ]
processEnvironment[ args___] := unexpected[ processEnvironment, {args}]

(* adjustEnvironment checks whether the filename of the given notebook changed, and if so, updates the Theorema
	environment accordingly. *)
adjustEnvironment[ nb_NotebookObject] :=
	adjustEnvironment[ nb, CurrentValue[ nb, "NotebookFullFileName"]]
adjustEnvironment[ nb_NotebookObject, nbFile_String] :=
	With[ {origName = updateNotebookFileName[ nb, nbFile]},
		(* Check whether the file name of the notebook changed and the original file does not exist any more *)
		If[ nbFile =!= origName && !FileExistsQ[ origName],
			(* If yes, this indicates that probably some formulae are stored in the environment with an outdated key
				-> update the keys
				-> remove outdated tab from KBbrowser
			*)
        	updateSingleKey[ sourceLabel[ nbFile], sourceLabel[ origName]]
		]
	]
adjustEnvironment[ args___] := unexpected[ adjustEnvironment, {args}]

evaluationPosition[ nb_NotebookObject, raw_Notebook] :=
	Module[ {id, pos},
		SelectionMove[ nb, All, EvaluationCell];
		(* find the cell according to CellID *)
		id = CurrentValue[ "CellID"];
		pos = Position[ raw, Cell[ _, ___, CellID -> id, ___], Infinity, 1];
		pos[[1]]
		(* we leave the current cell selected, the calling function should decide where to move the selection *)
	]
evaluationPosition[ nb_NotebookObject, raw_Notebook, id_Integer] :=
	Module[ {pos},
		pos = Position[ raw, Cell[ _, ___, CellID -> id, ___], Infinity, 1];
		pos[[1]]
	]
evaluationPosition[ nb_NotebookObject, id_Integer] := evaluationPosition[ nb, NotebookGet[ nb], id]

evaluationPosition[ args___] := unexpected[ evaluationPosition, {args}]

adjustFormulaLabel[ nb_NotebookObject] := 
	Module[ {cellTags, cellID, cleanCellTags, key},
		{cellTags, cellID} = {CellTags, CellID} /. Options[ NotebookSelection[ nb], {CellTags, CellID}];
		(* Make sure we have a list of CellTags (could also be a plain string) *)
		cellTags = Flatten[ {cellTags}];
		(* Remove any automated labels (begins with "ID<sep>" or "Source<sep>"). Remove initLabel *)
		cleanCellTags = getCleanCellTags[ cellTags];
        (* Replace unlabeled formula with counter *)
         If[ cleanCellTags === {},
         	cleanCellTags = automatedFormulaLabel[ nb]
         ];
        (* Relabel Cell and hide CellTags *)
        key = relabelCell[ nb, cleanCellTags, cellID];
        {key, cleanCellTags}
	]
adjustFormulaLabel[ args___] := unexpected[ adjustFormulaLabel, {args}]

(* getCleanCellTags returns all CellTags except the generated tags used for formula identification, i.e. ID<sep>... and Source<sep>...*)
getCleanCellTags[ cellTags_List] :=
	With[ {prefixes = ("ID" <> $cellTagKeySeparator | "Source" <> $cellTagKeySeparator | "Proof|ID" <> $cellTagKeySeparator)},
		(* Although "Source:..." tags are not generated automatically any more, we still remove them in 'getCleanCellTags' to handle older
			notebooks properly, too. *)
    	Select[ cellTags, !StringMatchQ[ #, (prefixes ~~ __) | $initLabel]&]
	]
getCleanCellTags[ cellTag_String] := getCleanCellTags[ {cellTag}]
getCleanCellTags[ args___] := unexpected[ getCleanCellTags, {args}]

getKeyTags[ cellTags_List, file_String] :=
	With[ {prefix = "ID" <> $cellTagKeySeparator},
		(* We completely ignore existing "Source:..." tags stemming from old notebooks, but use 'file' instead. *)
    	Append[ Select[ cellTags, StringMatchQ[ #, prefix ~~ __]&], sourceLabel[ file]]
	]
getKeyTags[ cellTag_String, file_String] := getKeyTags[ {cellTag}, file]
getKeyTags[ args___] := unexpected[ getKeyTags, {args}]

getCellLabel[ cellTags_List, key_String] :=
	Module[{id = Select[ cellTags, StringMatchQ[ #, key ~~ $cellTagKeySeparator ~~ __]&]},
		If[ id === {},
			cellLabel[ $initLabel, key],
			id[[1]]
		]
	]
getCellLabel[ args___] := unexpected[ getCellLabel, {args}]

getCellIDLabel[ cellTags_] := getCellLabel[ cellTags, "ID"]
getCellIDLabel[ args___] := unexpected[ getCellIDLabel, {args}]

(* Extract the CellID from the formula key *)
getCellIDFromKey[ k_List] :=
	Module[{lab},
		lab = getCellIDLabel[ k];
		Part[ StringSplit[ lab, $cellTagKeySeparator], 2]
	]
getCellIDFromKey[ args___] := unexpected[ getCellIDFromKey, {args}]

(*
 cellTagsToString[ tags] extracts the formula label from a list of cell tags. It does so by first
 looking for tags starting with "Label<sep>"; if it finds some, the first of them is returned (without "Label<sep>").
 Otherwise, simply the first element of tags is returned.
*)
cellTagsToString[ {___, l_String?(StringMatchQ[ #, ("Label" <> $cellTagKeySeparator) ~~ __]&), ___}] :=
	StringDrop[ l, 5 + StringLength[ $cellTagKeySeparator]]
cellTagsToString[ {l_String, ___}] := l
cellTagsToString[ ct_String] := ct
cellTagsToString[ args___] := unexpected[ cellTagsToString, {args}]

(*
 cellTagsToFmlTags[ tags] extracts the formula tags from a list of cell tags. The formula tags are simply
 all elements of tags except the one that is taken as the label of the formula, according to cellTagsToString.
*)
cellTagsToFmlTags[ _String|{}] := {}
cellTagsToFmlTags[ {pre___, _String?(StringMatchQ[ #, ("Label" <> $cellTagKeySeparator) ~~ __]&), post___}] :=
	{pre, post}
cellTagsToFmlTags[ {_String, rest___}] := {rest}
cellTagsToFmlTags[ args___] := unexpected[ cellTagsToFmlTags, {args}]

makeLabel[ s_String] := "(" <> s <> ")"
makeLabel[ args___] := unexpected[ makeLabel, {args}]

relabelCell[ nb_NotebookObject, cellTags_List, cellID_Integer] :=
	Module[ {newFrameLabel, newCellTags},
	With[ {idTag = cellIDLabel[ cellID]},
		(* Keep cleaned CellTags and add identification (ID) *)
		newCellTags = Prepend[ cellTags, idTag];
		(* Join list of CellTags, use $labelSeparator *)
		newFrameLabel =
			Cell[ BoxData[ RowBox[{
				StyleBox[ makeLabel[ cellTagsToString[ cellTags]], "FrameLabel"], "  ",
				ButtonBox[ "\[Times]", Evaluator -> Automatic, Appearance -> None, ButtonFunction :> removeFormula[ idTag]]}]]];
		SetOptions[ NotebookSelection[ nb], CellFrameLabels -> {{None, newFrameLabel}, {None, None}}, CellTags -> newCellTags, ShowCellTags -> False];
		(* return autoTags to be used as key for formula in KB *)
		{idTag, sourceLabel[ nb]}
	]]
relabelCell[ args___] := unexpected[ relabelCell, {args}]

removeEnvironment[ nb_NotebookObject] :=
	Module[ {cells, file = CurrentValue[ nb, "NotebookFullFileName"]},
		SelectionMove[ nb, All, ButtonCell];
		SelectionMove[ nb, All, CellGroup];
		(* The selection is Cell[ CellGroupData[ {cell1, ..., celln}]]], so we have to search on level 3 *)
		cells = Cases[ NotebookRead[ nb], Cell[ _, "FormalTextInputFormula"|"GlobalDeclaration", ___], {3}];
		NotebookDelete[ nb];
		NotebookFind[ nb, "CloseEnvironment", Next, CellStyle];
		SelectionMove[ nb, All, Cell];
		NotebookDelete[ nb];
		NotebookFind[ nb, "OpenEnvironment", Previous, CellStyle];
		SelectionMove[ nb, All, Cell];
		NotebookDelete[ nb];
		Scan[ removeFromSession[ file, #]&, cells];
		updateKBBrowser[ file];	
	]
removeEnvironment[ args___] := unexpected[ removeEnvironment, {args}]

removeFromSession[ file_, Cell[ _, "FormalTextInputFormula", ___, CellTags -> t_, ___]] := removeFromEnv[ getKeyTags[ t, file]]
removeFromSession[ file_, Cell[ _, "GlobalDeclaration", ___, CellID -> id_, ___]] := removeFromGlobals[ {file, id}]
removeFromSession[ args___] := unexpected[ removeFromSession, {args}]

removeFromEnv[ key_List] :=
	Module[ {p},
		$tmaEnv = DeleteCases[ $tmaEnv, FML$[ key, ___]];
		p = Position[ DownValues[ kbSelectProve], key];
		If[ p =!= {}, Unset[ kbSelectProve[ key]]];
		p = Position[ DownValues[ kbSelectCompute], key];
		If[ p =!= {}, Unset[ kbSelectCompute[ key]]];
	]
removeFromEnv[ args___] := unexpected[ removeFromEnv, {args}]

removeFormula[ id_String] :=
	With[ {nb = ButtonNotebook[]},
	With[ {nbFile = CurrentValue[ nb, "NotebookFullFileName"]},
		adjustEnvironment[ nb, nbFile];		(* otherwise the formula might not get removed *)
		removeFormula[ {id, sourceLabel[ nbFile]}, nb, nbFile];
	]]
removeFormula[ key_List] :=
	(* for compatibility *)
	With[ {nb = ButtonNotebook[]},
		removeFormula[ key, nb, CurrentValue[ nb, "NotebookFullFileName"]];
	]
removeFormula[ key_List, nb_NotebookObject, nbFile_String] :=
	(
		SelectionMove[ nb, All, ButtonCell];
		NotebookDelete[ nb];
		removeFromEnv[ key];
		updateKBBrowser[ nbFile];
	)
removeFormula[ args___] := unexpected[ removeFormula, {args}]

removeGlobal[ {file_, id_}] :=
	Module[ {posF, pos, nb, allDeclPos, allDeclFile},
		(* we search for the position in the notebook, thus we find a position regardless whether the declaration
		   has been evaluated or not. It would be faster to use the cached position but this would not work if we delete a
		   declaration that has not been evaluated yet. *)
		nb = NotebookGet[ ButtonNotebook[]];
		pos = evaluationPosition[ ButtonNotebook[], nb, id];
		(* we remove the cell *)
		SelectionMove[ ButtonNotebook[], All, ButtonCell];
		NotebookDelete[ ButtonNotebook[]];
		posF = Position[ $globalDeclarations, file -> _, {1}, 1];
		If[ posF =!= {},
			(* we only need to update something if the current file has evaluated declarations *)
			allDeclPos = Append[ posF[[1]], 2];
			allDeclFile = DeleteCases[ Extract[ $globalDeclarations, allDeclPos], {id, __}, {1}, 1];
			(* the positions of those below pos will be updated. In fact, these cells just move up by one position.
			   we do not use occursBelow because using pattern matching in shiftUp (similar to occursBelow) allows
			   to do everything at once. *)
			allDeclFile = Map[ shiftUp[ pos, #]&, allDeclFile];
			$globalDeclarations = ReplacePart[ $globalDeclarations, allDeclPos -> allDeclFile]
		]		
	]
removeGlobal[ args___] := unexpected[ removeGlobal, {args}]

shiftUp[ {pre___, x_}, {id_, {pre___, y_, post___}, decl_}] /; x < y := {id, {pre, y-1, post}, decl}
shiftUp[ l_List, orig_List] := orig
shiftUp[ args___] := unexpected[ shiftUp, {args}]

removeFromGlobals[ {file_, id_}] :=
	Module[ {posF, allDeclPos, allDeclFile},
		(* we need not update any other cached positions when we remove an entire environment *)
		posF = Position[ $globalDeclarations, file -> _, {1}, 1];
		If[ posF =!= {},
			(* we only need to update something if the current file has evaluated declarations *)
			allDeclPos = Append[ posF[[1]], 2];
			allDeclFile = DeleteCases[ Extract[ $globalDeclarations, allDeclPos], {id, __}, {1}, 1];
			$globalDeclarations = ReplacePart[ $globalDeclarations, allDeclPos -> allDeclFile]
		]		
	]
removeFromGlobals[ args___] := unexpected[ removeFromGlobals, {args}]


cellLabel[ l_, key_String] := key <> $cellTagKeySeparator <> ToString[l]
cellLabel[ args___] := unexpected[ cellLabel, {args}]

cellIDLabel[ cellID_] := cellLabel[ cellID, "ID"]
cellIDLabel[ args___] := unexpected[ cellIDLabel, {args}]

(* TODO: Maybe archives and ordinary notebooks should not be treated differently here. *)
sourceLabel[ nb_NotebookObject] /; inArchive[] := cellLabel[ currentArchiveName[], "Source"]
sourceLabel[ nb_NotebookObject] := cellLabel[ CurrentValue[ nb, "NotebookFullFileName"], "Source"]
sourceLabel[ file_String] := cellLabel[ file, "Source"]
sourceLabel[ args___] := unexpected[ sourceLabel, {args}]


ensureNotebookIntegrity[ file_] :=
	Module[ {nb},
		nb = Select[ Notebooks[], CurrentValue[ #, "NotebookFullFileName"] === file &, 1];
		If[ nb === {},
			nb = NotebookOpen[ file, Visible -> False],
			(* else *)
			nb = First[ nb]
		];
		ensureNotebookIntegrity[ nb]
	]
ensureNotebookIntegrity[ nb_NotebookObject] :=
	Module[ {allLabels, duplicateLabels, sl, nbFile = CurrentValue[ nb, "NotebookFullFileName"]},
		sl = sourceLabel[ nbFile];
		(* Collect labels of all formulas whose source is 'nb'. *)
		allLabels = label /@ Select[ $tmaEnv, source[ #] === sl &];
		(* Check whether labels are unique. *)
		duplicateLabels = Select[ Tally[ allLabels], duplicateLabel];
		If[ duplicateLabels =!= {} && duplicateLabels =!= $lastDuplicateFormulaLabels,
			(* If not, give an appropriate warning. *)
			$lastDuplicateFormulaLabels = duplicateLabels;
			notification[ translate[ "notUniqueLabel"], nbFile, Map[ First, duplicateLabels]]
		];
	]
ensureNotebookIntegrity[ args___] := unexpected[ ensureNotebookIntegrity, {args}]


duplicateLabel[ {_, occurences_Integer}] := occurences > 1
duplicateLabel[ args___] := unexpected[ duplicateLabel, {args}]

updateSingleKey[ new_String, old_String] :=
    Module[ {},
        $tmaEnv = Map[ Replace[ #, {id_, old} :> {id, new}]&, $tmaEnv, {2}];
        DownValues[ kbSelectProve] = DownValues[ kbSelectProve] /. {id_, old} :> {id, new};
        DownValues[ kbSelectCompute] = DownValues[ kbSelectCompute] /. {id_, old} :> {id, new};
        DownValues[ kbSelectSolve] = DownValues[ kbSelectSolve] /. {id_, old} :> {id, new};
        new
    ]
updateSingleKey[args___] := unexpected[ updateSingleKey, {args}]


automatedFormulaLabel[ nb_NotebookObject] :=
	With[ {formulaCounter = incrementFormulaCounter[ nb]},
		(* Construct new CellTags with value of the incremented formulaCounter as a list. *)
		{"Label" <> $cellTagKeySeparator <> ToString[ formulaCounter]}
	]
automatedFormulaLabel[ args___] := unexpected[ automatedFormulaLabel, {args}]

applicableGlobalDeclarations[ nb_NotebookObject, raw_Notebook, pos_List] :=
	Module[{ file = CurrentValue[ nb, "NotebookFullFileName"]},
		(* Find global declarations that apply to the cell at position pos, i.e. those at a position p, where pos occur "below" p (incl. nesting).
		   The stored global declarations have their position cached, we use the cached positions to find the relevant declarations.
		   It is important to keep the cached positions up to date when the notebook is edited, in particular when new declarations are added or removed.
		   Originally (before we cached positions) we searched through the raw notebook expression for declaration cells, computed their position, and
		   chose the relevant ones using "occursBelow". For big notebooks, this really makes a difference. *)
		Map[ Last, Sort[ Cases[ getGlobalDeclaration[ file], {_, p_, d_} /; occursBelow[ p, pos], {1}], occursBelow[ #1[[2]], #2[[2]]]&]]
	]
applicableGlobalDeclarations[ args___] := unexpected[ applicableGlobalDeclarations, {args}]

displayGlobalDeclarations[ nb_NotebookObject] :=
	Module[{ globDecl, pos, raw, sel, availDecl},
		raw = NotebookGet[ nb];
		(* If nothing is selected, i.e. the cursor is between cells, or not an entire cell is selected, then select some cell *)
		Do[ 
			If[ Head[ sel = NotebookRead[ nb]] === Cell,
				Break[]
			];
			SelectionMove[ nb, dir, Cell],
			{dir, {All, Next, Previous}}
		];
		pos = First[ Position[ raw, sel]];
		(* Remove the Holds around fresh symbols *)
		availDecl = ReleaseHold[ applicableGlobalDeclarations[ nb, raw, pos]];
		If[ availDecl =!= {},
			globDecl = DisplayForm[ RowBox[ Map[ theoremaDisplay, availDecl]]],
			globDecl = "\[LongDash]"
		];
		globDecl
	]
displayGlobalDeclarations[ args___] := unexpected[ displayGlobalDeclarations, {args}]

occursBelow[ {a___, p_}, {a___, q_, ___}] /; q > p := True
occursBelow[ x_, y_] := False
occursBelow[ args___] := unexpected[ occursBelow, {args}]

updateKnowledgeBase[ $Failed, k_, ___] :=
	(
		$tmaEnv = DeleteCases[ $tmaEnv, _[ k, ___], {1}, 1];
		If[ inArchive[],
	        $tmaArch = DeleteCases[ $tmaArch, _[ k, ___], {1}, 1]
	    ];
	)
(* 
	form and glob still carry Holds around fresh symbols. After globals have been applied, ReleaseHold will remove them.
*)
updateKnowledgeBase[ form_, k_, glob_, l_String] :=
	updateKnowledgeBase[ form, k, glob, l, {}]
updateKnowledgeBase[ form_, k_, glob_, l_String, tags_List] :=
	updateKnowledgeBase[ form, k, glob, l, tags, Null]
updateKnowledgeBase[ form_, k_, glob_, l_String, tags_List, cellPos_] :=
    Module[ {newForm, fml, inDomDef = Cases[ glob, Hold[ domainConstruct$TM][_,_], {1}, 1], defDef},
    	If[ inDomDef =!= {} && (defDef = $tmaDefaultDomainDef[ inDomDef[[1]]]) =!= {},
    		(* we are in a domain definition and there is a pending default for this domain *)
    		$tmaDefaultDomainDef[ inDomDef[[1]]] = {};
    		newForm = Catch[ addAbbrevPositions[ ReleaseHold[ addVarPrefixes[ applyGlobalDeclaration[ defDef[[1]], glob]]]]];
		    If[ newForm === $Failed,
		    	updateKnowledgeBase[ $Failed, k],
		    (*else*)
		    	fml = makeFML[ key -> Rest[ defDef], formula -> newForm, preprocess -> $tmaFmlPre,
		    			label -> StringReplace[ ToString[ ReleaseHold[ inDomDef[[1,1]]]], "$TM" -> ""] <> ".defOp", simplify -> False,
		    			formulaTags -> tags, cellPosition -> cellPos];
		    	Switch[ fml,
		    		$Failed,
		    		notification[ translate[ "invalidExpr"]];
	    			updateKnowledgeBase[ $Failed, k],
	    		(*else*)
	    			Null,
	    			updateKnowledgeBase[ $Failed, k],
	    		(*else*)
	    			_,
	    			$tmaFmlPost[ fml];
		    		$tmaEnv = Append[ DeleteCases[ $tmaEnv, _[ First[ fml], ___], {1}, 1], fml];
		        	If[ inArchive[],
		            	$tmaArch = Append[ DeleteCases[ $tmaArch, _[ First[ fml], ___], {1}, 1], fml];
		        	]
		    	]
		    ];
    	];
    	(* for the actual formula we proceed in the same way *)
    	(* Since 'applyGlobalDeclaration' may throw '$Failed' (via 'markVariables'), we have to put it inside a 'Catch'. *)
    	newForm = Catch[ addAbbrevPositions[ ReleaseHold[ addVarPrefixes[ applyGlobalDeclaration[ form, glob]]]]];
    	If[ newForm === $Failed,
    		(*no need to show any notification, has already been done in 'markVariables'*)
    		updateKnowledgeBase[ $Failed, k],
    	(*else*)
	    	fml = makeFML[ key -> k, formula -> newForm, label -> l, simplify -> False, preprocess -> $tmaFmlPre,
	    					formulaTags -> tags, cellPosition -> cellPos];
	    	Switch[ fml,
	    		$Failed,
	    		notification[ translate[ "invalidExpr"]];
	    		updateKnowledgeBase[ $Failed, k],
	    	(*else*)
	    		Null,
	    		(* In this case we do not notify the user. *)
	    		updateKnowledgeBase[ $Failed, k],
	    	(*else*)
	    		_,
		    	$tmaFmlPost[ fml];
		    	(* If new formulae are appended rather than prepended, the old formulae with the same label
		    		have to be deleted first, because "DeleteDuplicates" would delete the new ones. *)
				$tmaEnv = Append[ DeleteCases[ $tmaEnv, _[ First[ fml], ___], {1}, 1], fml];
		        If[ inArchive[],
		            $tmaArch = Append[ DeleteCases[ $tmaArch, _[ First[ fml], ___], {1}, 1], fml];
		        ]
	    	]
    	]
    ]
updateKnowledgeBase[ args___] := unexpected[ updateKnowledgeBase, {args}]

findSelectedFormula[ Cell[ _, ___, CellTags -> t_, ___], file_String] :=
	Module[ { key = getKeyTags[ t, file]},
		Cases[ $tmaEnv, FML$[ key, _, __], {1}, 1]
	]
findSelectedFormula[ sel_, _] := {}
findSelectedFormula[ args___] := unexpected[ findSelectedFormula, {args}]

(*
	The global declarations have all symbols still wrapped in Hold (from freshSymbols) 
	in order to make things consistent with a local quantifier written in front of the expression.
	As a result, also the globalForall$TM, globalImplies$TM, etc. have a Hold.
*)
Clear[ applyGlobalDeclaration]
applyGlobalDeclaration[ expr_, g_List] :=
	Module[ {form = Fold[ applyGlobalDeclaration, expr, Reverse[ g]]},
		form //. {globalImplies$TM[ a_, b_] :> Module[ {fa}, b /; ((fa = freeVariables[ a]) =!= {} && Intersection[ fa, freeVariables[ b]] === {})]}
			 //. {fa:(globalForall$TM[ _, _, _]) :> Module[ {res}, res /; (res = analyzeQuantifiedExpression[ fa]) =!= fa]}
			 /. {globalForall$TM -> Forall$TM, globalImplies$TM -> Implies$TM}
	]

applyGlobalDeclaration[ expr:globalForall$TM[ rng_, cond_, e_], Hold[ globalForall$TM][ r_, c_]] :=
	Module[ {tmp = ReleaseHold[ markVariables[ Hold[ QU$[ r, expr]]]]},
		globalForall$TM[ Join[ r, tmp[[1]]], makeConjunction[ {c, tmp[[2]]}, Hold[ And$TM]], tmp[[3]]]
	]
applyGlobalDeclaration[ expr_, Hold[ globalForall$TM][ r_, c_]] := 
	globalForall$TM[ r, c, ReleaseHold[ markVariables[ Hold[ QU$[ r, expr]]]]]
applyGlobalDeclaration[ expr_, Hold[ globalForall$TM][ r_, c_, d_]] := 
	With[ {new = applyGlobalDeclaration[ expr, d]},
		applyGlobalDeclaration[ new, Hold[ globalForall$TM][ r, c]]
	]
applyGlobalDeclaration[ expr_, Hold[ globalImplies$TM][ c_]] := globalImplies$TM[ c, expr]
applyGlobalDeclaration[ expr_, Hold[ globalImplies$TM][ c_, d_]] := globalImplies$TM[ c, applyGlobalDeclaration[ expr, d]]
applyGlobalDeclaration[ expr_, Hold[ domainConstruct$TM][ lhs_, rng:RNG$[ SIMPRNG$[ v_]]]] :=
	substituteFree[ ReleaseHold[ markVariables[ Hold[ QU$[ rng, expr]]]], {v -> lhs}, "checkTypes" -> False, "postprocessing" -> Identity]	(* sequence-type will be checked in 'makeFML' *)
applyGlobalDeclaration[ expr_, Hold[ domainConstruct$TM][ lhs_, rng:RNG$[ DOMEXTRNG$[ v_, d_]]]] :=
	substituteFree[ ReleaseHold[ markVariables[ Hold[ QU$[ rng, expr]]]], {v -> lhs}, "checkTypes" -> False, "postprocessing" -> Identity]
applyGlobalDeclaration[ expr_, Hold[ globalAbbrev$TM][ rng:RNG$[ a__ABBRVRNG$]]] :=
	substituteFree[ ReleaseHold[ markVariables[ Hold[ QU$[ rng, expr]]]], Apply[ Rule, {a}, {1}], "checkTypes" -> False, "postprocessing" -> Identity]
applyGlobalDeclaration[ args___] := unexpected[ applyGlobalDeclaration, {args}]

(*
	analyze the ranges and drop all quantifiers that aren't needed
*)
analyzeQuantifiedExpression[ globalForall$TM[ r:RNG$[ __], c_, e_]] :=
	Module[ {freeE, rc, thinnedRange, freerc},
		(* take the free vars in e and free variables in the ranges *)
		freeE = freeVariables[ {Map[ Rest, List @@ r], e}];		(*if the head of 'r' is 'RNG$', 'freeVariables' produces a wrong result*)
		(* watch out for all conditions involving the free variables in e ... *)
		{rc, freerc} = thinnedConnect[ c, freeE];
		(* ... and collect all free variables therein: these are the variables that require the quantifiers, the others can be dropped *)
		thinnedRange = Select[ r, MemberQ[ Union[ freeE, freerc], First[ #]]&];
		If[ Length[ thinnedRange] == 0,
			simplifiedImplies[ Implies$TM[ rc, e]],
			(* else *)
			Forall$TM[ thinnedRange, rc, e]
		]
	]

(*
	thinnedConnect[ expr, v]
	If expr is an And or Or connective: drop all parts that do not depend on the variables v.
	
	Used when a global quantifier is applied to an expression. Only the variables that really occur should
	finally be bound. No spurious conditions for variables not occurring in v shall remain.
*)
thinnedConnect[ expr:Hold[ And$TM][ x__], v_List] :=
	Module[ {depv = {}, depdistinct = {}, fv, p, l, e = simplifiedAnd[ expr /. Hold[ And$TM] -> And$TM], fi, i, move = {1}},
		(* move needs to be initialized to something non-empty *)
		Switch[ e,
			_And$TM,
			l = Length[ e];
			Do[
				p = e[[i]];
				fi = freeVariables[ p];
				Which[ Intersection[ fi, v] =!= {},
					(* p contains variables from v and maybe also others *)
					AppendTo[ depv, p],
					True,
					(* p contains variables distinct from v, we keep them because they might be linked to the depv *)
					AppendTo[ depdistinct, p]
				],
				{i, l}
			];
			(* Move those from depdistinct to depv, which share some variables
			   We need to try until no more moves happen *)
			fv = freeVariables[ depv];
			While[ move =!= {} && depdistinct =!= {},
				move = {};
				Do[
					p = depdistinct[[i]];
					fi = freeVariables[ p];
					If[ Intersection[ fv, fi] =!= {},
						AppendTo[ move, {i}];
						fv = Union[ fv, fi]
					],
					{i, Length[ depdistinct]}
				];
				depv = Join[ depv, Extract[ depdistinct, move]];
				depdistinct = Delete[ depdistinct, move]
			];
			(* Those that remain in depdistinct can be dropped *)
			{makeConjunction[ depv, And$TM], fv},

			_,
			thinnedConnect[ e, v]
		]
	]

thinnedConnect[ expr:Hold[ Or$TM][ x__], v_List] :=
	Module[ {depv = {}, depdistinct = {}, fv, p, l, e = simplifiedOr[ expr /. Hold[ Or$TM] -> Or$TM], fi, i, move = {1}},
		(* move needs to be initialized to something non-empty *)
		Switch[ e,
			_Or$TM,
			l = Length[ e];
			Do[
				p = e[[i]];
				fi = freeVariables[ p];
				Which[ Intersection[ fi, v] =!= {},
					(* p contains variables from v and maybe also others *)
					AppendTo[ depv, p],
					True,
					(* p contains variables distinct from v, we keep them because they might be linked to the depv *)
					AppendTo[ depdistinct, p]
				],
				{i, l}
			];
			(* Move those from depdistinct to depv, which share some variables
			   We need to try until no more moves happen *)
			fv = freeVariables[ depv];
			While[ move =!= {} && depdistinct =!= {},
				move = {};
				Do[
					p = depdistinct[[i]];
					fi = freeVariables[ p];
					If[ Intersection[ fv, fi] =!= {},
						AppendTo[ move, {i}];
						fv = Union[ fv, fi]
					],
					{i, Length[ depdistinct]}
				];
				depv = Join[ depv, Extract[ depdistinct, move]];
				depdistinct = Delete[ depdistinct, move]
			];
			(* Those that remain in depdistinct can be dropped *)
			{makeDisjunction[ depv, Or$TM], fv},

			_,
			thinnedConnect[ e, v]
		]
	]

thinnedConnect[ e_, v_List] :=
	Module[ {fe},
		fe = freeVariables[ e];
		Which[ Intersection[ fe, v] =!= {},
			{e, fe},
			True,
			{True, {}}
		]
	]
thinnedConnect[ args___] := unexpected[ thinnedConnect, {args}]


initSession[] :=
    Module[ {},
    	$TheoremaArchives = {};
        $tmaEnv = {};
        $tmaArch = {};
        $globalDeclarations = {};
        $tmaArchNeeds = {};
        $formulaCounterName = "TheoremaFormulaCounter";
        $nbFileNameCounterName = "NotebookFileName";
        $TMAcurrentEvalNB = {};
        $tmaNbUpdateQueue = {};
        $tmaNbEval = {};
        $tmaAllNotebooks = {};
        $tmaCompPre = sequenceFlatten;
        $tmaCompPost = sequenceFlatten;
        $tmaFmlPre = defaultFmlPre;	(* takes 6 arguments 'form', 'lbl', 'simp', 'tags', 'key', 'pos', and returns 4-tuple '{newForm, newLbl, newSimp, newTags}' *)
        $tmaFmlPost = transferToComputation;
        $codeProlog := (Theorema`Common`$parseTheoremaQuoted = True;);
        $codeEpilog := (Theorema`Common`$parseTheoremaQuoted = False;);
        $inputProlog := (Theorema`Common`$parseTheoremaQuoted = True;);
        $inputEpilog := (Theorema`Common`$parseTheoremaQuoted = False;);
        $Pre=.;
        $PreRead=.;
    ]
initSession[ args___] := unexpected[ initSession, {args}]

incrementFormulaCounter[ nb_NotebookObject] :=
	With[ {counters = getCounterAssignments[ nb]},
	With[ {formulaCounter = getFormulaCounter[ counters] + 1},
		(* Save Incremented formulaCounter to the notebook options. *)
		SetOptions[ nb, CounterAssignments -> updateCounterAssignments[ counters, $formulaCounterName -> formulaCounter]];
		formulaCounter
	]]
incrementFormulaCounter[ args___] := unexpected[ incrementFormulaCounter, {args}]

getFormulaCounter[ nb_NotebookObject] :=
	getFormulaCounter[ getCounterAssignments[ nb]]
getFormulaCounter[ counters_List] :=
	Replace[ Replace[ $formulaCounterName, Flatten[ counters]], $formulaCounterName -> 0]
getFormulaCounter[ args___] := unexpected[ getFormulaCounter, {args}]

(* updateNotebookFileName changes the counter assignment for $nbFileNameCounterName and returns its original value. *)
updateNotebookFileName[ nb_NotebookObject, new_String] :=
	With[ {counters = getCounterAssignments[ nb]},
	With[ {orig = Replace[ $nbFileNameCounterName, Flatten[ counters]]},
		If[ new =!= orig,
			SetOptions[ nb, CounterAssignments -> updateCounterAssignments[ counters, $nbFileNameCounterName -> new]]
		];
		orig
	]]
updateNotebookFileName[ args___] := unexpected[ updateNotebookFileName, {args}]

getCounterAssignments[ nb_NotebookObject] :=
	Replace[ Replace[ CounterAssignments, Options[ nb, CounterAssignments]], CounterAssignments -> {}]
getCounterAssignments[ args___] := unexpected[ getCounterAssignments, {args}]

updateCounterAssignments[ counters_, k_ -> v_] :=
	Append[ DeleteCases[ counters, {k -> _}], {k -> v}]
updateCounterAssignments[ args___] := unexpected[ updateCounterAssignments, {args}]

removeRedundantBoxes[ expr_] :=
	With[ {pos = Position[ expr, TagBox[ _, _Theorema`Language`TAG$|_Theorema`Computation`Language`TAG$, ___]]},
		MapAt[ First, expr, pos]
	]

(*
	openEnvironment is assigned to $PreRead, which might be called under certain circumstances.
	In order not to mess up the contexts, we do some checks.
*) 
openEnvironment[ expr_] :=
    Module[ {t = lastEvalTimeAgo[ CurrentValue[ EvaluationNotebook[], "NotebookFullFileName"]]},
    	If[ t > 1.5,
    		$refreshBrowser = True,
    		(* else *)
    		$refreshBrowser = False
    	];
		$parseTheoremaExpressions = True;
        $ContextPath = DeleteDuplicates[ Join[ {"Theorema`Language`"}, $TheoremaArchives, $ContextPath]];
        (* Set default context when not in an archive *)
        If[ !inArchive[] && $Context =!= "Theorema`Knowledge`", Begin[ "Theorema`Knowledge`"]];
        removeRedundantBoxes[ expr]
    ]
openEnvironment[args___] := unexpected[ openEnvironment, {args}]

closeEnvironment[] := 
	Module[ {file = CurrentValue[ EvaluationNotebook[], "NotebookFullFileName"]},
		(* Leave "Theorema`Knowledge`" context when not in an archive *)
		If[ !inArchive[] && $Context === "Theorema`Knowledge`", End[]];
		(* Restore context path that has been modified in openEnvironment *)
		$ContextPath = DeleteCases[ $ContextPath, Apply[ Alternatives, Join[ {"Theorema`Language`"}, $TheoremaArchives]]];
		$parseTheoremaExpressions = False;
		If[ $refreshBrowser,
			updateKBBrowser[ file],
			(* else *)
			putToUpdateQueue[ file]
		];
		putToEvalTime[ file]
	]
closeEnvironment[args___] := unexpected[ closeEnvironment, {args}]

inEnvironment[] := TrueQ[ $parseTheoremaExpressions || $parseTheoremaGlobals]
inEnvironment[ args___] := unexpected[ inEnvironment, {args}]

lastEvalTimeAgo[ file_] :=
	Module[{t = Cases[ $tmaNbEval, {file, timestamp_} -> timestamp, {1}, 1]},
		If[ t === {},
			Infinity,
			(* else *)
			SessionTime[] - t[[1]]
		]
	]
lastEvalTimeAgo[ args___] := unexpected[ lastEvalTimeAgo, {args}]

putToUpdateQueue[ file_] := 
	Module[ {pos = Position[ $tmaNbUpdateQueue, {file, _}, {1}, 1]},
		If[ pos === {},
			$tmaNbUpdateQueue = Prepend[ $tmaNbUpdateQueue, {file, SessionTime[]}],
			(* else *)
			$tmaNbUpdateQueue = ReplacePart[ $tmaNbUpdateQueue, Append[ pos[[1]], 2] -> SessionTime[]]
		]
	]
putToUpdateQueue[ args___] := unexpected[ putToUpdateQueue, {args}]

putToEvalTime[ file_] :=
	Module[ {pos = Position[ $tmaNbEval, {file, _}, {1}, 1]},
		If[ pos === {},
			$tmaNbEval = Prepend[ $tmaNbEval, {file, SessionTime[]}],
			(* else *)
			$tmaNbEval = ReplacePart[ $tmaNbEval, Append[ pos[[1]], 2] -> SessionTime[]]
		]
	]
putToEvalTime[ args___] := unexpected[ putToEvalTime, {args}]

(* ::Section:: *)
(* Archives *)

getArchivePath[ arch_String] :=
    Module[ {fn, absfn},
        Which[ FileExtension[ arch] === "ta",
            fn = arch,
            StringQ[ fn = Quiet[ ContextToFileName[ arch]]],
            fn = StringReplacePart[ Last[ FileNameSplit[ fn]], "ta", -1],
            True,
            notification[ Theorema::archiveName, context];
            Return[ $Failed]
        ];
        absfn = Block[ {$Path = $TheoremaArchivePath},
                    FindFile[ fn]
                ];
        If[ absfn === $Failed,
            absfn = FileNameJoin[ {$TheoremaArchiveDirectory, fn}]
        ];
        absfn
    ]
getArchivePath[args___] := unexpected[ getArchivePath, {args}]

getArchiveNotebookPath[arch_String] := StringReplacePart[ getArchivePath[ arch], "nb", {-2,-1}]
getArchiveNotebookPath[args___] := unexpected[ getArchiveNotebookPath, {args}]

openArchive[ name_String] :=
    Module[ {nb = EvaluationNotebook[], nbFile, archiveNotebookPath, posBrowser},
        archiveNotebookPath = getArchiveNotebookPath[ name];
        nbFile = CurrentValue[ nb, "NotebookFullFileName"];
        (* Create the directory for an archive if does not exist. *)
        If[ !DirectoryQ[ DirectoryName[ archiveNotebookPath]],
            CreateDirectory[ DirectoryName[ archiveNotebookPath]]
        ];
        If[ nbFile =!= archiveNotebookPath,
        	(* In the presence of symlinks nbFile and archiveNotebookPath might point to the same file.
        	   In this case we get a warning telling us to save to an open notebook. There is no easy way to check this.
        	   As a workaround, we save the notebook only if no notebook with the same name exists
        	   in the archive path. This will do the job in the "normal cases", i.e. when turning a new 
        	   notebook Untitled-n or an existing notebook from outside the archive path into an archive. *)
        	Block[ {$Path = $TheoremaArchivePath},
        		If[ FindFile[ CurrentValue[ nb, "NotebookFileName"]] === $Failed,
        			NotebookSave[ nb, archiveNotebookPath]
        		]
        	];        	
        	posBrowser = Position[ $kbStruct, nbFile -> _, 1, 1];
        	If[ Length[ posBrowser] === 1, 
		        (* If the notebook has now been saved under the archive name
           		   then replace the name in the KB browser and update $tcKBBrowseSelection correspondingly *)
            	$kbStruct = ReplacePart[ $kbStruct, Append[ posBrowser[[1]], 1] -> archiveNotebookPath];
        		Scan[ ($tcKBBrowseSelection[ #] = archiveNotebookPath)&, {"prove", "compute", "solve"}]
        	]
        ];
        NotebookFind[ nb, "ArchiveInfo", All, CellStyle];
        (* We memorize the setting of loaded archives *)
        $globalArchivesList = $TheoremaArchives;
        BeginPackage[ "Theorema`Knowledge`" <> name, {"Theorema`"}];
        SelectionEvaluate[ nb];
    ]
openArchive[ args___] := unexpected[ openArchive, {args}]

inArchive[] := StringLength[ $Context] >= 9 && StringTake[ $Context, -9] === "`private`"
inArchive[ args___] := unexpected[ inArchive, {args}]

currentArchiveName[] := StringDrop[$Context,-8]
currentArchiveName[ args___] := unexpected[ currentArchiveName, {args}]

openArchiveInfo[ s_] :=
	Module[{},
		AppendTo[ $ContextPath, "Theorema`Language`"];
		s
	]
openArchiveInfo[ args___] := unexpected[ openArchiveInfo, {args}]

closeArchiveInfo[ ] :=
	Module[{},
		$ContextPath = Most[ $ContextPath];
	]
closeArchiveInfo[ args___] := unexpected[ closeArchiveInfo, {args}]

SetAttributes[ processArchiveInfo, HoldAll];
processArchiveInfo[ a_] :=
	Module[ {cf},
		If[ inArchive[],
			(* The archive info cells are evaluated automatically when opening the archive, see openArchive.
			   If they are evaluated again manually, we exit immediately in order not to mess up the contexts. *)
			Return[]
		];
		cf = CurrentValue[ "CellFrameLabels"];
		Switch[ cf[[1,1]],
			translate[ "archLabelNeeds"],
			(* The {} in the input are interpreted as Set$TM, therefore the Apply[ List, ...] *)
			$tmaArchNeeds = Apply[ List, a]; Scan[ loadArchive, a], (* Remember and load current dependencies. *)
			translate[ "archLabelPublic"],
			(* The {} in the input are interpreted as Set$TM, therefore the Apply[ List, ...] *)
			$tmaArchExports = Apply[ List, removeHold[ freshNames[ Hold[ a]]]];
			Begin[ "`private`"];     
		];
	]
processArchiveInfo[ args___] := unexpected[ processArchiveInfo, {args}]

closeArchive[ _String] :=
    Module[ {nb = EvaluationNotebook[], currNB, archName, archFile, archivePath},
    	If[ inArchive[],
        	End[],
        	(* The contexts do not fit, leave the function without action *)
        	Return[ "Null"]
    	];
        currNB = CurrentValue[ nb, "NotebookFullFileName"];
        archName = $Context;
        archivePath = getArchivePath[ archName];
        $tmaArchTree = currNB /. $kbStruct;
        EndPackage[];
        (* We don't want to have the archive name in the context path,
           we control the context path when required using $TheoremaArchives *)
        $ContextPath = DeleteCases[$ContextPath, archName, {1}, 1];
        (* We restore the globally loaded archives from the value it had before entering the current archive,
           i.e. all archives loaded inside are removed again, they are treated as local w.r.t. the current archive *)
        $TheoremaArchives = DeleteDuplicates[ Prepend[ $globalArchivesList, archName]];
        (* Reset the context path in order to force Mathematica to write
        explicit contexts to the file *)
        Block[ {$ContextPath = {"System`"}},
            (* Save an archive. *)
            NotebookSave[ nb];
            archFile = OpenWrite[ archivePath];
            WriteString[ archFile, "(* **********************\n   DO NOT EDIT THIS FILE!\n   ----------------------\n   It is generated automatically by Theorema\n   *)\n\n"];
            Write[ archFile, {"Archive name" -> archName}];
            Scan[ WriteString[ archFile, "loadArchive[\""<>#<>"\"]\n"]&, $tmaArchNeeds];
            Write[ archFile, Definition[$tmaArch]];
            Write[ archFile, Definition[$tmaArchTree]];
            Close[ archFile];
        ];
        (* export to OmDoc *)
        If[ $omdocExport,
       		exportArchiveOmDoc[ archivePath, $tmaArch];
        ];
        (* Reset archive related variables. *)
        $tmaArch = {};
        (* Return Null-string because this happens in $PreRead *)
        "Null"
    ]
closeArchive[args___] := unexpected[closeArchive, {args}]

loadArchive[ name_String, globalDecl_:{}] :=
    Module[ {archivePath, cxt, archiveContent, archiveNotebookPath, pos},
        (* Save Current Settings into the local Variables *)
        archivePath = getArchivePath[ name];
        If[ !FileExistsQ[ archivePath],
            notification[ Theorema::archiveNotFound, archivePath];
            Return[]
        ];
        cxt = archiveName[ archivePath];
        (* Clear computation definitions available from previous loading or somewhere *)
        With[{comp = StringReplace[ cxt <> "*", "Theorema`Knowledge`" -> "Theorema`Computation`Knowledge`", 1]},
        	Clear[comp]
        ];
        Block[ {$tmaArch},
            (* we could just Get[archivePath], but we read the content and prevent evaluation for the moment
               this would be the place to process the archive content before evaluation *)
            archiveContent = ReadList[ archivePath, Hold[ Expression]];
            ReleaseHold[ archiveContent];
            (* after reading and evaluating the archive $tmaArch has a value, namely the actual KB contained in the archive
               this is why we use the Block in order not
               to overwrite $tmaArch when loading an archive from within another one ... *)
            (* we use updateKnowledgeBase: this applies global declarations appropriately and 
               translates to computational form ... *)
            Scan[ updateKnowledgeBase[ #[[2]], #[[1]], globalDecl, #[[3]], Flatten[ Cases[ #, ("tags" -> t_List) :> t, {1}, 1], 1]]&, $tmaArch]
        ];
        $TheoremaArchives = DeleteDuplicates[ Prepend[ $TheoremaArchives, cxt]];
        If[ !FileExistsQ[ archiveNotebookPath = getArchiveNotebookPath[ name]],
            archiveNotebookPath = archivePath
        ];
        If[ (pos = Position[ $kbStruct, archiveNotebookPath -> _]) === {},
            AppendTo[ $kbStruct, archiveNotebookPath -> $tmaArchTree],
            $kbStruct = ReplacePart[ $kbStruct, pos[[1]] -> (archiveNotebookPath -> $tmaArchTree)];
        ];
    ]
    Map[ StringReplace[ #, "Theorema`Knowledge`" -> "Theorema`Computation`Knowledge`", 1]&, $TheoremaArchives]
loadArchive[ l_List, globalDecl_:{}] := Scan[ loadArchive[ #, globalDecl]&, l]
loadArchive[ args___] := unexpected[ loadArchive, {args}]

includeArchive[ name_String] :=
	Module[ {nb = EvaluationNotebook[], raw},
		raw = NotebookGet[ nb]; 
		loadArchive[ name, applicableGlobalDeclarations[ nb, raw, evaluationPosition[ nb, raw]]];
		SelectionMove[ nb, After, Cell];
	]
(* we don't use Listable because we want no output *)
includeArchive[ l_List] := Scan[ includeArchive, l]
includeArchive[ args___] := unexpected[ includeArchive, {args}]

archiveName[ f_String] :=
    Module[ {file = OpenRead[ f],meta,n},
        While[ !(OptionQ[ meta = Read[ file, Expression]] || meta === EndOfFile)];
        Close[ file];
        If[ meta === EndOfFile,
            Return[ translate[ "noArchName"]],
            n = "Archive name" /. meta;
            If[ StringQ[ n] && StringMatchQ[ n, (WordCharacter|"`").. ~~ "`"],
                n,
                (* else *)
                translate[ "noArchName"]
            ]
        ]
    ]
archiveName[ f_String, Short] := StringReplace[ archiveName[ f], "Theorema`Knowledge`" -> ""]
archiveName[ args___] := unexpected[ archiveName, {args}]

exportArchiveOmDoc[ archive_String, arch_List] :=
	Module[{expFile},
		expFile = OpenWrite[ StringReplacePart[ archive, "omdoc", -2]];
		convert2OmDocConst[ expFile, $tmaArchExports];
		convert2OmDoc[ expFile, FileBaseName[ archive], arch];
        Close[ expFile];
	]
exportArchiveOmDoc[ args___] := unexpected[ exportArchiveOmDoc, {args}]

convert2OmDocConst[ file_, e_] := 
	Scan[ WriteString[ file, makeTag[ {"constant", genAttr[ "name", dropContext[ #]]}]]&, e]
convert2OmDocConst[ args___] := unexpected[ convert2OmDocConst, {args}]

convert2OmDoc[ file_, name_String, l_List] := 
	Module[ {},
		Scan[ convert2OmDoc[ file, #]&, l];
		WriteString[ file, openTag[ {"theory", genAttr[ "name", name], genAttr[ "meta", "?Theorema"]}]];
		Scan[ WriteString[ file, makeTag[ {"imports", genAttr[ "from", #]}]]&, $tmaArchNeeds];
		WriteString[ file, closeTag[ "theory"]];
	]
convert2OmDoc[ file_, f_FML$] := 
	Module[ {def},
		def = Cases[ formula@f, _EqualDef$TM|_IffDef$TM, {0, Infinity}, 1];
		If[ def =!= {},
			WriteString[ file, openTag[ {"constant", genAttr[ "name", id@f]}]];
			writeMetadata[ file, id@f, def];
			WriteString[ file, openTag[ {"type"}]]
		];
		convert2OmDoc[ file, id@f, source@f, {}, formula@f];
		If[ def =!= {},
			WriteString[ file, closeTag[ "type"]];
			WriteString[ file, closeTag[ "constant"]];
		]
	]
convert2OmDoc[ file_, id_, src_, pos_, VAR$[ x_]] := 
	Module[ {},
		WriteString[ file, makeTag[ {"OMV", genAttr[ "name", dropContext[ x]], srcrefAttr[ src, id, pos]}]];
	]
convert2OmDoc[ file_, id_, src_, pos_, Q_[ r_RNG$, c_, b_]] := 
	Module[ {},
		WriteString[ file, openTag[ {"OMBIND", srcrefAttr[ src, id, pos]}]];
		WriteString[ file, makeTag[ {"OMS", genAttr[ "name", dropContext[ Q]], genAttr[ "cd", "Theorema"]}]];
		MapIndexed[ convert2OmDoc[ file, id, src, Join[ pos, {1}, #2], #1]&, r];
		convert2OmDoc[ file, id, src, Join[ pos, {2}], c];
		convert2OmDoc[ file, id, src, Join[ pos, {3}], b];
		WriteString[ file, closeTag[ "OMBIND"]]
	]
convert2OmDoc[ file_, id_, src_, pos_, SIMPRNG$[ v_]] := 
	Module[ {},
		WriteString[ file, openTag[ {"OMBVAR"}]];
		convert2OmDoc[ file, id, src, pos, v];
		WriteString[ file, closeTag[ "OMBVAR"]]
	]
convert2OmDoc[ file_, id_, src_, pos_, SETRNG$[ v_, A_]] := 
	Module[ {},
		WriteString[ file, openTag[ {"OMBVAR"}]];
		convert2OmDoc[ file, id, src, pos, v];
		WriteString[ file, closeTag[ "OMBVAR"]]
	]
convert2OmDoc[ file_, id_, src_, pos_, PREDRNG$[ v_, P_]] := 
	Module[ {},
		WriteString[ file, openTag[ {"OMBVAR"}]];
		convert2OmDoc[ file, id, src, pos, v];
		WriteString[ file, closeTag[ "OMBVAR"]]
	]
convert2OmDoc[ file_, id_, src_, pos_, STEPRNG$[ v_, l_, h_, s_]] := 
	Module[ {},
		WriteString[ file, openTag[ {"OMBVAR"}]];
		convert2OmDoc[ file, id, src, pos, v];
		WriteString[ file, closeTag[ "OMBVAR"]]
	]
convert2OmDoc[ file_, id_, src_, pos_, f_[ x___]] := 
	Module[ {},
		WriteString[ file, openTag[ {"OMA", srcrefAttr[ src, id, pos]}]];
		convert2OmDoc[ file, id, src, Join[ pos, {0}], f];
		MapIndexed[ convert2OmDoc[ file, id, src, Join[ pos, #2], #1]&, {x}];
		WriteString[ file, closeTag[ "OMA"]]
	]
convert2OmDoc[ file_, id_, src_, pos_, s:True|False] := 
	Module[ {},
		WriteString[ file, makeTag[ {"OMS", genAttr[ "name", ToString[ s]], genAttr[ "cd", "Theorema"]}]];
	]
convert2OmDoc[ file_, id_, src_, pos_, s_Symbol] := 
	Module[ {},
		WriteString[ file, makeTag[ {"OMS", genAttr[ "name", dropContext[ s]], genAttr[ "cd", "Theorema"]}]];
	]
convert2OmDoc[ file_, id_, src_, pos_, s_?NumberQ] := 
	Module[ {t},
		t = Switch[ s,
			_Integer, "INT",
			_Rational, "RAT",
			_Real, "REAL",
			_Complex, "COMPLEX"
		];
		WriteString[ file, makeTag[ {"OMLIT", genAttr[ "value", ToString[ s]], genAttr[ "type", "?Numbers?" <> t], srcrefAttr[ src, id, pos]}]];
	]
convert2OmDoc[ args___] := unexpected[ convert2OmDoc, {args}]

openTag[ l_List] := "<" <> Apply[ StringJoin, Riffle[ l, " "]] <> ">\n"
openTag[ args___] := unexpected[ openTag, {args}]

closeTag[ t_String] := "</" <> t <> ">\n"
closeTag[ args___] := unexpected[ closeTag, {args}]

makeTag[ l_List] := "<" <> Apply[ StringJoin, Riffle[ l, " "]] <> "/>\n"
makeTag[ args___] := unexpected[ makeTag, {args}]

srcrefAttr[ src_, id_String, pos_List] := "srcref=\"" <> src <> "#" <> id <> "@" <> ToString[ pos] <> "\""
srcrefAttr[ args___] := unexpected[ srcrefAttr, {args}]

genAttr[ t_String, x_] := t <> "=\"" <> x <> "\""
genAttr[ args___] := unexpected[ genAttr, {args}]

dropContext[ name_] := 
	With[ { n = ToString[ name], c = Context[ name]},
		If[ StringMatchQ[ c, "Theorema`" ~~ __], 
			StringDrop[ n, StringLength[ c]],
			(* else *)
			n
		]
	]
dropContext[ args___] := unexpected[ dropContext, {args}]

writeMetadata[ file_, id_String, {def_}] :=
	Module[ {},
		WriteString[ file, openTag[ {"metadata"}]];
		WriteString[ file, makeTag[ {"link", genAttr[ "rel", "theory:srcref"], genAttr[ "resource", id]}]];
		WriteString[ file, makeTag[ {"link", genAttr[ "rel", "omdoc:defines"], genAttr[ "resource", "??" <> definedSymbol[ def]]}]];
		WriteString[ file, closeTag[ "metadata"]];

	]
writeMetadata[ args___] := unexpected[ writeMetadata, {args}]

definedSymbol[ (EqualDef$TM|IffDef$TM)[ left_, _]] := definedSymbol[ left]
definedSymbol[ (Overscript$TM|Subscript$TM|Subsuperscript$TM|Superscript$TM|Underoverscript$TM|Underscript$TM)[ f_, __]] := definedSymbol[ f];
definedSymbol[ f_[ ___]] := definedSymbol[ f]
definedSymbol[ f_Symbol] := dropContext[ f];
definedSymbol[ args___] := unexpected[ definedSymbol, {args}]


(* ::Section:: *)
(* Computation *)

SetAttributes[ processComputation, HoldAll];

processComputation[ x:Theorema`Computation`Language`nE] := 
	Module[{},
		$Failed
	]
processComputation[ x_] := Module[ { procSynt, res, lhs = Null},
	(* Remove the inner Holds around fresh symbols, and note that we have to catch parsing-errors (e.g. invalid multi ranges). *)
	procSynt = addAbbrevPositions[ Replace[ addVarPrefixes[ Catch[ markVariables[ freshNames[ Hold[ x], True]]]], Hold[ s_] -> s, Infinity, Heads -> True]];
	If[ MatchQ[ procSynt, _[ Theorema`Computation`Language`Assign$TM[ _, _]]],
		lhs = Extract[ procSynt, {1, 1}, Hold];
		procSynt = Extract[ procSynt, {1, 2}, Hold]
	];
	procSynt = $tmaCompPre[ procSynt];
	(* As an initial computation object, we start with the box form of the input cell *)
	$TmaComputationObject = {ToExpression[ InString[ $Line]]};
	$TmaCompInsertPos = {2};
	setComputationContext[ "compute"];
	{$compTime, res} = Timing[ Check[ Catch[ ReleaseHold[ procSynt]], $Failed]];
	setComputationContext[ "none"];
	(*NotebookWrite[ EvaluationNotebook[], Cell[ ToBoxes[ res, TheoremaForm], "ComputationResult", CellLabel -> "Out["<>ToString[$Line]<>"]="]];*)
	(* We force the MakeBoxes[ ..., TheoremaForm] to apply by setting $PrePrint in the CellProlog of a computation cell.
	   Unsetting $PrePrint in the CellEpilog ensures this behaviour only for Theorema computation *)
	AppendTo[ $TmaComputationObject, res];
	$tmaCompPost[ renameToStandardContext[ res, lhs]]
]
processComputation[ args___] := unexcpected[ processComputation, {args}]

openComputation[ expr_] :=
	Module[ {fileCache},
		$evalCellID = CurrentValue[ "CellID"];
		$cacheComp = True;
		$fileEvalNb = CurrentValue[ EvaluationNotebook[], "NotebookFullFileName"];
		If[ TrueQ[ $TMAcomputationDemoMode],
			fileCache = FileNameJoin[ {DirectoryName[ $fileEvalNb], FileBaseName[ fileEvalNb], "c" <> ToString[ $evalCellID]}];
			$cacheComp = setComputationEnvironment[ fileCache];
		];
		$parseTheoremaExpressions = True;
		$ContextPath = Join[
			{"Theorema`Computation`Language`"},
			Map[ StringReplace[ #, "Theorema`Knowledge`" -> "Theorema`Computation`Knowledge`", 1]&, $TheoremaArchives],
			$ContextPath];
		Begin[ "Theorema`Computation`Knowledge`"];
		removeRedundantBoxes[ expr]
	]
openComputation[args___] := unexcpected[ openComputation, {args}]

closeComputation[] :=
    Module[ {},
        End[];
		$ContextPath = Select[ $ContextPath, (!StringMatchQ[ #, "Theorema`Computation`" ~~ __])&];
		$parseTheoremaExpressions = False;
		printComputationInfo[ $evalCellID, $cacheComp, $fileEvalNb, $compTime];
    ]
closeComputation[args___] := unexcpected[ closeComputation, {args}]

displayBoxes[ expr_] := RawBoxes[ theoremaBoxes[ expr]]
displayBoxes[ args___] := unexpected[ displayBoxes, {args}]

renameToStandardContext[ expr_, lhs_:Null] :=
	Block[{$ContextPath = {"System`"}, $Context = "System`", stringExpr, cp},
		(* FullForm[] is needed, for otherwise it doesn't work if outermost symbol is built-in Power *)
		stringExpr = ToString[ FullForm[ Hold[ expr]]];
		If[ lhs =!= Null,
			(* The assignment needs to be carried out with "expr" in Computation`-context! *)
			cp = $ContextPath;
			$ContextPath = Join[ {"Theorema`Computation`Language`"}, $TheoremaArchives, $ContextPath];
			(* We must not remove the outermost "Hold", for otherwise some of the Computation`-symbols would be immediately replaced by Mathematica-symbols again.
				Also, the tuples which are introduced by "replaceAllExcept" above are in Theorema`Language`-conext, and thus have to be moved to Computation`-context. *)
			assign[ lhs, Replace[ freshNames[ ToExpression[ stringExpr]] /. Theorema`Language`Tuple$TM -> Theorema`Computation`Language`Tuple$TM, Hold[ x_] -> x, Infinity, Heads -> True]];
			$ContextPath = cp
		];
		stringExpr = StringReplace[ stringExpr, "Theorema`Computation`" -> "Theorema`"];
		$ContextPath = Join[ {"Theorema`Language`"}, $TheoremaArchives, $ContextPath];
        removeHold[ freshNames[ ToExpression[ stringExpr]]]
	]
renameToStandardContext[ args___] := unexpected[ renameToStandardContext, {args}]

(* We have to use "SetDelayed", because "expr" might evaluate. *)
assign[ Hold[ s_Symbol], Hold[ expr_]] := (s := expr)
assign[ Hold[ Theorema`Computation`Language`Tuple$TM[ elems___]], Hold[ Theorema`Computation`Language`Tuple$TM[ expr___]]] :=
	Module[ {l, r},
		Scan[ Apply[ assign, #]&, Transpose[ {l, r}]] /; 
			Length[ l = List@@Map[ Hold, Hold[ elems]]] === Length[ r = List@@Map[ Hold, Hold[ expr]]]
	]
assign[ args___] := unexpected[ assign, {args}]

(* ::Section:: *)
(* Computation within proving *)

(* This version will be used for simplification of the initial proof situation. *)
computeInProof[ f:FML$[ _, _, _, ___, "origForm" -> _, ___]] := f
	(* If there is already an "origForm" -> _, this means that computation has already been applied to this formula. We do nothing. *)

computeInProof[ FML$[ k_, f_, l_, r___]] :=
	(* computation happens in makeFML, which calls computeInProof[ expr] below.
	   In presence of optional components r___, we restore them into the final formula. *)
	With[ {out = makeFML[ key -> k, formula -> f, label -> l]},
		If[ out === $Failed,
			$Failed,
			Join[ out, FML$[ r]]
		]
	]

computeInProof[ expr_] :=
	Module[{simp},
		setComputationContext[ "prove"];
		simp = ToExpression[ StringReplace[ ToString[ FullForm[ expr]], "Theorema`Language`" -> "Theorema`Computation`Language`"]];
		setComputationContext[ "none"];
		(* simp does not evaluate further *)
		With[ {res = simp},
			(* We need FullForm here, for the same reason as in "renameToStandardContext" *)
			ToExpression[ StringReplace[ ToString[ FullForm[ renameToStandardContext[ res]]], "Theorema`Computation`" -> "Theorema`"]]
		]
	]
computeInProof[ args___] := unexpected[ computeInProof, {args}]


(* ::Section:: *)
(* Notebook operations *)

createNbRememberLocation[ opts___?OptionQ] :=
	Module[{file, dir, fpMode, nb},
		If[ ValueQ[ $dirLastOpened],
			dir = $dirLastOpened,
			dir = $HomeDirectory
		];
		file = SystemDialogInput[ "FileSave", {dir, {translate["fileTypeNotebook"] -> {"*.nb"}}}];
		If[ StringQ[ file] && !FileExistsQ[ file],
			$dirLastOpened = DirectoryName[ file];
			trustNotebookDirectory[ $dirLastOpened];
			(* Fiddling in the FrontEnd options is a workaround caused by a Mma bug (under Linux?), 
			   which causes an error message when saving a notebook and other notebooks are open
			   at the same time. Once this bug is corrected, we can just NotebookSave[ NotebookCreate[ ...]]. *)
			fpMode = Replace[ Global`FileChangeProtection, Options[ $FrontEnd, Global`FileChangeProtection]];
			SetOptions[ $FrontEnd, Global`FileChangeProtection -> None];
			nb = CreateDocument[ {}, opts, StyleDefinitions -> makeColoredStylesheet[ "Notebook"]];
			SetOptions[ nb, CounterAssignments -> {{$formulaCounterName -> 0}, {$nbFileNameCounterName -> file}}];
			NotebookSave[ nb, file];
			SetOptions[ $FrontEnd, Global`FileChangeProtection -> fpMode];
			putToUpdateQueue[ file];
			$TMAcurrentEvalNB = DeleteDuplicates[ Prepend[ $TMAcurrentEvalNB, {file, NotebookGet[ nb]}],
					#1[[1]] === #2[[1]]&];
			$tmaAllNotebooks = DeleteDuplicates[ Prepend[ $tmaAllNotebooks, file]];
			createPerNotebookDirectory[ file];
		]
	]
createNbRememberLocation[ args___] := unexpected[ createFileRememberLocation, {args}]

trustNotebookDirectory[ dir_String] :=
	Module[{tPath, cleanDir, nbSecurOpts = Options[ $FrontEnd, "NotebookSecurityOptions"]},
		(* remove trailing pathname separator, e.g. "/" *)
		If[ StringTake[ dir, -StringLength[ $PathnameSeparator]] === $PathnameSeparator,
			cleanDir = StringDrop[ dir, -StringLength[ $PathnameSeparator]],
			cleanDir = dir
		];
		(* be careful in future: maybe NotebookSecurityOptions moves to a system-specific context in future versions of Mma *)
		tPath = "TrustedPath" /. (Global`NotebookSecurityOptions /. nbSecurOpts);
		(* add dir to the trusted paths *)
		Apply[ SetOptions[ $FrontEnd, #]&,
			Options[ $FrontEnd, "NotebookSecurityOptions"] /. HoldPattern[ "TrustedPath" -> _] -> ("TrustedPath" -> DeleteDuplicates[ Append[ tPath, cleanDir]])]
	]
trustNotebookDirectory[ args___] := unexpected[ trustNotebookDirectory, {args}]

openNbRememberLocation[ opts___?OptionQ] :=
	Module[{file, dir, nb},
		If[ ValueQ[ $dirLastOpened],
			dir = $dirLastOpened,
			dir = $HomeDirectory
		];
		file = SystemDialogInput[ "FileOpen", {dir, {translate["fileTypeNotebook"] -> {"*.nb"}}}];
		If[ StringQ[ file] && FileExistsQ[ file],
			$dirLastOpened = DirectoryName[ file];
			trustNotebookDirectory[ $dirLastOpened];
			If[ (nb = NotebookOpen[ file, opts, StyleDefinitions -> makeColoredStylesheet[ "Notebook"]]) =!= $Failed,
				putToUpdateQueue[ file];
				$TMAcurrentEvalNB = DeleteDuplicates[ Prepend[ $TMAcurrentEvalNB, {file, NotebookGet[ nb]}],
					#1[[1]] === #2[[1]]&];
				$tmaAllNotebooks = DeleteDuplicates[ Prepend[ $tmaAllNotebooks, file]];
			]
		]
	]
openNbRememberLocation[ args___] := unexpected[ openNbRememberLocation, {args}]

(* create per-notebook directory, return the name *)
createPerNotebookDirectory[ nb_NotebookObject] := 
	Module[ {nbDir = CurrentValue[ nb, "NotebookDirectory"], file}, 
		(* nbDir is the per-notebook directory, in which we store all files belonging to this notebook *)
		If[ nbDir === $Failed,
			(* nb has not yet been saved, it's an Untitled-... *)
			file = saveNbRememberLocation[ nb],
			(* else: use full name *)
			file = CurrentValue[ nb, "NotebookFullFileName"]
		];
		createPerNotebookDirectory[ file]		
	]
createPerNotebookDirectory[ file_String] :=
	Module[ {nbDir, new}, 
		(* nbDir is the per-notebook directory, in which we store all files belonging to this notebook *)
		nbDir = FileNameJoin[ {DirectoryName[ file], FileBaseName[ file]}];
		If[ DirectoryQ[ nbDir],
			new = nbDir,
			(* create the dir if it does not yet exist *)
			new = CreateDirectory[ nbDir];
			If[ new === $Failed,
				notification[ translate[ "cantCreateDir"], nbDir]
			]
		];
		new		
	]
createPerNotebookDirectory[ args___] := unexpected[ createPerNotebookDirectory, {args}]

(* saveNbRememberLocation[ nb_NotebookObject] saves nb, asks for filename, returns filename *)
saveNbRememberLocation[ nb_NotebookObject] :=
	Module[{file, dir},
		If[ ValueQ[ $dirLastOpened],
			dir = $dirLastOpened,
			dir = $HomeDirectory
		];
		file = SystemDialogInput[ "FileSave", {dir, {translate["fileTypeNotebook"] -> {"*.nb"}}}];
		If[ StringQ[ file],
			$dirLastOpened = DirectoryName[ file];
			NotebookSave[ nb, file]
		];
		file
	]
saveNbRememberLocation[ args___] := unexpected[ saveNbRememberLocation, {args}]

allTmaNotebooks[ ] := $tmaAllNotebooks
allTmaNotebooks[ args___] := unexpected[ allTmaNotebooks, {args}]


(* ::Section:: *)
(* end of package *)

initSession[];
  
End[]

EndPackage[];