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

BeginPackage["Theorema`Language`Session`"];

Needs["Theorema`Common`"];
Needs["Theorema`Language`"];
Needs["Theorema`Interface`Language`"];

Begin["`Private`"]


(* ::Section:: *)
(* Preprocessing *)

(* amaletzk: Define "freshNames[]", "freshNamesProg[]" in the way below, because otherwise parts with "Program" don't work.
	Maybe the case "Theorema`Computation`Language`Program" should also be included, such that "Program"-constructs
	work in computation cells as well. *)
freshNames[expr_Hold] :=
	Module[ {symPos, repl, progPos, progSymPos},
		progPos = Position[ expr, Program[_]];
		(* There are certain expressions, into which we do not want to go deeper for substituting fresh names. 
		   An example is a META$[__] expression representing a meta-variable in a proof, which has a list as
		   its 3rd parameter. Going into it would turn the list into a Set$TM ... 
		   If other cases occur in the future, just add a suitable transformation here BEFORE the replaceable
		   positions are computed. *)
		symPos = DeleteCases[ Position[ expr /. {META$[__] -> META$[]}, _Symbol], {0}, {1}, 1];
		progSymPos = Cases[ symPos, x_ /; isSubPositionOfAny[ x, progPos]];
		repl = Join[Map[ # -> freshSymbol[ Extract[ expr, #, Hold]]&, Complement[symPos, progSymPos]],
					Map[ # -> freshSymbolProg[ Extract[ expr, #, Hold]]&, progSymPos]];		
		(* amaletzk: The "FlattenAt" simply replaces every "Program[p]" by "p". *)
		FlattenAt[ReplacePart[ expr, repl], progPos]
	]
freshNames[args___] := unexpected[ freshNames, {args}]


isSubPositionOfAny[ pos_List, l_List] := Catch[ (Scan[ If[isSubPosition[pos, #], Throw[True]]&, l]; False)]
isSubPosition[ l1_List, l2_List] :=
	With[{len = Length[l2]}, 
 		Length[l1] >= len && l1[[1 ;; len]] === l2[[1 ;; len]]
 	]


freshSymbol[ Hold[ s_Symbol]] :=
    Module[ {name},
        Switch[ Unevaluated[ s],
            (* We use ToExpression in order to have the symbol generated in the right context
               depending on whether we are in a computation or not *)
            _?isMathematicalConstant, s,
            (* processing the number domain symbols by MakeExpression does not work, I think MakeExpression is only
               applied to boxes and not to individual symbols. We convert them to respective ranges here. *)
            Theorema`Computation`Knowledge`\[DoubleStruckCapitalN]|Theorema`Knowledge`\[DoubleStruckCapitalN],
            	ToExpression[ "IntegerInterval$TM[ 1, Infinity, True, False]"],
            Theorema`Computation`Knowledge`\[DoubleStruckCapitalZ]|Theorema`Knowledge`\[DoubleStruckCapitalZ],
            	ToExpression[ "IntegerInterval$TM[ -Infinity, Infinity, False, False]"],
            Theorema`Computation`Knowledge`\[DoubleStruckCapitalQ]|Theorema`Knowledge`\[DoubleStruckCapitalQ],
            	ToExpression[ "RationalInterval$TM[ -Infinity, Infinity, False, False]"],
            Theorema`Computation`Knowledge`\[DoubleStruckCapitalR]|Theorema`Knowledge`\[DoubleStruckCapitalR],
            	ToExpression[ "RealInterval$TM[ -Infinity, Infinity, False, False]"],
            DoubleLongRightArrow|DoubleRightArrow, ToExpression[ "Implies$TM"],
            DoubleLongLeftRightArrow|DoubleLeftRightArrow|Equivalent, ToExpression[ "Iff$TM"],
        	SetDelayed, ToExpression[ "EqualDef$TM"], 
        	(* we don't encourage to use =, but in case it appears we interpret it as Equal *)
        	Set, ToExpression[ "Equal$TM"],
        	Wedge, ToExpression[ "And$TM"],
        	Vee, ToExpression[ "Or$TM"],
        	List, makeSet,
        	AngleBracket, makeTuple,
        	Inequality, ToExpression[ "OperatorChain$TM"],
        	_,
        	name = ToString[ Unevaluated[s]];
        	If[ StringTake[ name, -1] === "$" || (StringLength[ name] >= 3 && StringTake[ name, -3] === "$TM"),
        		s,
            	ToExpression[ name <> "$TM"]
        	]
        ]
    ]
freshSymbol[ args___] := unexpected[ freshSymbol, {args}]

freshSymbolProg[ Hold[ s_Symbol]] :=
    Module[ {name},
        Switch[ Unevaluated[ s],
            _?isMathematicalConstant, s,
            Theorema`Computation`Knowledge`\[DoubleStruckCapitalN]|Theorema`Knowledge`\[DoubleStruckCapitalN],
            	ToExpression[ "IntegerInterval$TM[1, DirectedInfinity[1], True, False]"],
            Theorema`Computation`Knowledge`\[DoubleStruckCapitalZ]|Theorema`Knowledge`\[DoubleStruckCapitalZ],
            	ToExpression[ "IntegerInterval$TM[DirectedInfinity[-1], DirectedInfinity[1], False, False]"],
            Theorema`Computation`Knowledge`\[DoubleStruckCapitalQ]|Theorema`Knowledge`\[DoubleStruckCapitalQ],
            	ToExpression[ "RationalInterval$TM[DirectedInfinity[-1], DirectedInfinity[1], False, False]"],
            Theorema`Computation`Knowledge`\[DoubleStruckCapitalR]|Theorema`Knowledge`\[DoubleStruckCapitalR],
            	ToExpression[ "RealInterval$TM[DirectedInfinity[-1], DirectedInfinity[1], False, False]"],
        	Set, ToExpression[ "Assign$TM"],
        	Inequality, ToExpression[ "OperatorChain$TM"],
        	_,
        	name = ToString[s];
        	Which[
        			StringTake[ name, -1] === "$" || (StringLength[ name] >= 3 && StringTake[ name, -3] === "$TM"),
        			s,
        			StringLength[ name] >= 3 && StringTake[ name, -2] === "$M",
        			s,
        			True,
        			ToExpression[ name <> "$TM"]
        	]
        ]
    ]
freshSymbolProg[ args___] := unexpected[ freshSymbolProg, {args}]

SetAttributes[isMathematicalConstant, HoldAll];
isMathematicalConstant[ Indeterminate|True|False|I|Pi|E|Infinity|DirectedInfinity|Complex|Rational|Degree|EulerGamma|GoldenRatio|Catalan|Khinchin|Glaisher] := True
isMathematicalConstant[ _] := False

markVariables[ Hold[ QU$[ r_RNG$, expr_]]] :=
    Module[ {s, seq, vars},
        (* all symbols sym specified as variables in r are translated into VAR$[sym]
           we substitute all symbols with matching "base name" (neglecting the context!) so that also
           symbols in different context get substituted. This is important when processing archives, because
           global variables in an archive live in the archive's private context, whereas the global declaration
           lives in the context of the loading notebook/archive. With the substitution below, the private`sym becomes 
           a VAR$[loading`sym] *)
           
        (* amaletz: We have to keep the distinction between sequence variables and individual variables,
        			because "SymbolName[]" would give an error if applied to compound expressions.
        *)
        vars = specifiedVariables[ r];
        seq = Cases[vars, (SEQ0$|SEQ1$)[ _]];
        vars = Complement[ vars, seq];
        s = Join[Map[ (h:(SEQ0$|SEQ1$))[sym_Symbol] /; SymbolName[ sym] === SymbolName[ #] -> VAR$[h[ #]]&, seq[[All, 1]]],
        		 Map[ sym_Symbol /; SymbolName[ sym] === SymbolName[ #] -> VAR$[ #]&, vars]];
        replaceAllExcept[ markVariables[ Hold[ expr]], s, {}, Heads -> {SEQ0$, SEQ1$, VAR$, FIX$}]
    ]

markVariables[ Hold[ Theorema`Computation`Language`QU$[ r_Theorema`Computation`Language`RNG$, expr_]]] :=
    Module[ {s, seq, vars},
    	vars = specifiedVariables[ Hold[ r]];
        seq = Cases[vars, (Theorema`Computation`Language`SEQ0$|Theorema`Computation`Language`SEQ1$)[ _]];
        vars = Complement[ vars, seq];
        s = Join[Map[ (h:(Theorema`Computation`Language`SEQ0$|Theorema`Computation`Language`SEQ1$))[sym_Symbol] /; SymbolName[ sym] === SymbolName[ #] -> Theorema`Computation`Language`VAR$[h[ #]]&, seq[[All, 1]]],
        		 Map[ sym_Symbol /; SymbolName[ sym] === SymbolName[ #] -> Theorema`Computation`Language`VAR$[ #]&, vars]];
        replaceAllExcept[ markVariables[ Hold[ expr]], s, {}, Heads -> {Theorema`Computation`Language`SEQ0$, Theorema`Computation`Language`SEQ1$, Theorema`Computation`Language`VAR$, Theorema`Computation`Language`FIX$}]
    ]
    
markVariables[Hold[h_[e___]]] := applyHold[
  		markVariables[Hold[h]],
  		markVariables[Hold[e]]]

markVariables[Hold[f_, t__]] := joinHold[
  		markVariables[Hold[f]],
  		markVariables[Hold[t]]]

markVariables[Hold[]] := Hold[]

markVariables[Hold[e_]] := Hold[e]

markVariables[args___] := unexpected[ markVariables, {args}]

(*
	makeTmaExpression[ e] is the combination of functions that we export to be used in other places if needed.
*)
SetAttributes[ makeTmaExpression, HoldAll]
makeTmaExpression[ e_Hold] := Block[ {$ContextPath},
	$ContextPath = Join[ {"Theorema`Language`"}, $TheoremaArchives, $ContextPath];
	ReleaseHold[ markVariables[ freshNames[ e]]]
]
makeTmaExpression[ e_] := Block[ {$ContextPath},
	$ContextPath = Join[ {"Theorema`Language`"}, $TheoremaArchives, $ContextPath];
	ReleaseHold[ markVariables[ freshNames[ Hold[ e]]]]
]
makeTmaExpression[ args___] := unexpected[ makeTmaExpression, {args}]

openGlobalDeclaration[ expr_] :=
    Module[ {},
        $parseTheoremaGlobals = True;
		(* Remember context path *)
		$origContextPath = $ContextPath;
        $ContextPath = Join[ {"Theorema`Language`"}, $TheoremaArchives, $ContextPath];
        If[ !inArchive[], Begin["Theorema`Knowledge`"]];
        expr
    ]
openGlobalDeclaration[ args___] := unexpected[ openGlobalDeclaration, {args}]

closeGlobalDeclaration[] :=
    Module[ {},
		If[ !inArchive[], End[]];
		(* Restore context path that has been modified in openEnvironment *)
		$ContextPath = $origContextPath;
        $parseTheoremaGlobals = False;
    ]
closeGlobalDeclaration[ args___] := unexpected[ closeGlobalDeclaration, {args}]

getGlobalDeclaration[ file_String] := Replace[ file, $globalDeclarations]
getGlobalDeclaration[ file_String, id_Integer] := Cases[ getGlobalDeclaration[ file], {id, d_} -> d]
getGlobalDeclaration[ file_String, l_List] := 
	(* Mapping over l ensures the order of extracted definitions to match the order of ids in l *)
	Apply[ Join, Map[ getGlobalDeclaration[ file, #]&, l]]
getGlobalDeclaration[ args___] := unexpected[ getGlobalDeclaration, {args}]

putGlobalDeclaration[ file_String, id_Integer, decl_] :=
	Module[{posF, posId},
		posF = Position[ $globalDeclarations, file -> _];
		If[ posF === {},
			PrependTo[ $globalDeclarations, file -> {{id, decl}}],
			posId = Position[ Extract[ $globalDeclarations, posF[[1]]], {id, _}];
			If[ posId === {},
				$globalDeclarations = With[ {posDecl = Append[ posF[[1]], 2]}, 
					ReplacePart[ $globalDeclarations, posDecl -> Append[ Extract[ $globalDeclarations, posDecl], {id, decl}]]],
				$globalDeclarations = With[ {posDecl = Append[ Join[ posF[[1]], posId[[1]]], 2]}, 
					ReplacePart[ $globalDeclarations, posDecl -> decl]]
			]
		]
	]
putGlobalDeclaration[ args___] := unexpected[ putGlobalDeclaration, {args}]

SetAttributes[ processGlobalDeclaration, HoldAll];
processGlobalDeclaration[ x_] := 
	Module[ {},
		putGlobalDeclaration[ CurrentValue["NotebookFullFileName"], CurrentValue["CellID"], ReleaseHold[ markVariables[ freshNames[ Hold[x]]]]];
		closeGlobalDeclaration[];
	]
processGlobalDeclaration[ args___] := unexpected[ processGlobalDeclaration, {args}]


SetAttributes[ processEnvironment, HoldAll];
processEnvironment[ Theorema`Language`nE] := Null

processEnvironment[x_] :=
    Module[ {nb = EvaluationNotebook[], rawNotebook, key, tags, globDec},
    	(* select current cell: we need to refer to this selection when we set the cell options *)
		SelectionMove[ nb, All, EvaluationCell];
    	{key, tags} = adjustFormulaLabel[ nb];
		(* Perform necessary actions on the whole notebook *)
        rawNotebook = NotebookGet[ nb];
		ensureNotebookIntegrity[ nb, rawNotebook, tags];
		(* extract the global declarations that are applicable in the current evaluation *)
		globDec = applicableGlobalDeclarations[ nb, rawNotebook, evaluationPosition[ nb, rawNotebook]];
		(* process the expression according the Theorema syntax rules and add it to the KB *)
        Catch[ updateKnowledgeBase[ReleaseHold[ markVariables[ freshNames[ Hold[x]]]], key, globDec, cellTagsToString[ tags]]];
        SelectionMove[ nb, After, Cell];
    ]
processEnvironment[args___] := unexcpected[ processEnvironment, {args}]

evaluationPosition[ nb_NotebookObject, raw_Notebook] :=
	Module[{pos},
		SelectionMove[ nb, All, EvaluationCell];
		pos = Position[ raw, NotebookRead[nb]];
		pos[[1]]
		(* we leave the current cell selected, the calling function should decide where to move the selection *)
	]
evaluationPosition[ args___] := unexpected[ evaluationPosition, {args}]

adjustFormulaLabel[nb_NotebookObject] := 
	Module[{ cellTags = CurrentValue["CellTags"], cellID = CurrentValue["CellID"], cleanCellTags, key},
		(*
		 * Make sure we have a list of CellTags (could also be a plain string)
		 *)
		cellTags = Flatten[{cellTags}];
		(*
		 * Remove any automated labels (begins with "ID<sep>" or "Source<sep>").
		 * Remove initLabel.
		 *)
		cleanCellTags = getCleanCellTags[ cellTags];
        (*
         * Replace unlabeled formula with counter.
         *)
         If[cleanCellTags==={},
         	cleanCellTags = automatedFormulaLabel[ nb]
         ];
        (*
         * Relabel Cell and hide CellTags.
         *)
        key = relabelCell[ nb, cleanCellTags, cellID];
        {key, cleanCellTags}
	]
adjustFormulaLabel[ args___] := unexpected[ adjustFormulaLabel, {args}]

(*
 * Returns all CellTags except the generated tags used for formula identification, i.e. ID<sep>... and Source<sep>...
 *)
getCleanCellTags[cellTags_List] :=
    Select[ cellTags, !StringMatchQ[ #, (("ID"<>$cellTagKeySeparator|"Source"<>$cellTagKeySeparator) ~~ __) | $initLabel]&]
getCleanCellTags[cellTag_String] := getCleanCellTags[{cellTag}]
getCleanCellTags[args___] := unexpected[getCleanCellTags,{args}]

getKeyTags[ cellTags_List] :=
    Select[ cellTags, StringMatchQ[ #, ("ID"<>$cellTagKeySeparator|"Source"<>$cellTagKeySeparator) ~~ __]&]
getKeyTags[ cellTag_String] := getKeyTags[ {cellTag}]
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

getCellSourceLabel[ cellTags_] := getCellLabel[ cellTags, "Source"]
getCellSourceLabel[ args___] := unexpected[ getCellSourceLabel, {args}]

cellTagsToString[ cellTags_ /; VectorQ[ cellTags, StringQ]] := Apply[ StringJoin, Riffle[ cellTags, $labelSeparator]]
cellTagsToString[ ct_String] := ct
cellTagsToString[ args___] := unexpected[cellTagsToString, {args}]

makeLabel[ s_String] := "(" <> s <> ")"
makeLabel[ args___] := unexpected[ makeLabel, {args}]

relabelCell[nb_NotebookObject, cellTags_List, cellID_Integer] :=
	Module[{ newFrameLabel, newCellTags, autoTags},
		(* Keep cleaned CellTags and add identification (ID) *)
		autoTags = {cellIDLabel[ cellID], sourceLabel[ nb]};
		newCellTags = Join[ autoTags, cellTags];
		(* Join list of CellTags, use $labelSeparator *)
		newFrameLabel = With[ {key = autoTags}, 
			Cell[ BoxData[ RowBox[{
				StyleBox[ makeLabel[ cellTagsToString[ cellTags]], "FrameLabel"], "  ",
				ButtonBox["\[Times]", Evaluator -> Automatic, Appearance -> None, ButtonFunction :> removeFormula[ key]]}]]]];
		SetOptions[ NotebookSelection[nb], CellFrameLabels -> {{None, newFrameLabel}, {None, None}}, CellTags -> newCellTags, ShowCellTags -> False];
		(* return autoTags to be used as key for formula in KB *)
		autoTags
	]
relabelCell[args___] := unexpected[ relabelCell,{args}]

removeEnvironment[ nb_NotebookObject] :=
	Module[{keys},
		SelectionMove[ nb, All, ButtonCell];
		SelectionMove[ nb, All, CellGroup];
		keys = Map[ getKeyTags,
			Cases[ NotebookRead[ nb],
				Cell[_, "FormalTextInputFormula", ___, CellTags -> tags_, ___] -> tags, Infinity]];
		NotebookDelete[ nb];
		NotebookFind[ nb, "CloseEnvironment", Next, CellStyle];
		SelectionMove[ nb, All, Cell];
		NotebookDelete[ nb];
		NotebookFind[ nb, "OpenEnvironment", Previous, CellStyle];
		SelectionMove[ nb, All, Cell];
		NotebookDelete[ nb];
		Scan[ removeFromEnv, keys];
		updateKBBrowser[];	
	]
removeEnvironment[ args___] := unexpected[ removeEnvironment, {args}]

removeFormula[ key_List] :=
	Module[{},
		SelectionMove[ ButtonNotebook[], All, ButtonCell];
		NotebookDelete[ ButtonNotebook[]];
		removeFromEnv[ key];
		updateKBBrowser[];
	]
removeFormula[ args___] := unexpected[ removeFormula, {args}]

removeFromEnv[ key_List] :=
	Module[{p},
		$tmaEnv = DeleteCases[ $tmaEnv, FML$[ key, ___]];
		p = Position[ DownValues[ kbSelectProve], key];
		If[ p =!= {},
			Unset[ kbSelectProve[ key]]];
		p = Position[ DownValues[ kbSelectCompute], key];
		If[ p =!= {},
			Unset[ kbSelectCompute[ key]]];			
	]
removeFromEnv[ args___] := unexpected[ removeFromEnv, {args}]

cellLabel[ l_, key_String] := key <> $cellTagKeySeparator <> ToString[l]
cellLabel[ args___] := unexpected[ cellLabel, {args}]

cellIDLabel[ cellID_] := cellLabel[ cellID, "ID"]
cellIDLabel[ args___] := unexpected[ cellIDLabel, {args}]

sourceLabel[ nb_NotebookObject] /; inArchive[] := cellLabel[ currentArchiveName[], "Source"]
sourceLabel[ nb_NotebookObject] := cellLabel[ CurrentValue[ nb, "NotebookFullFileName"], "Source"]
sourceLabel[ args___] := unexpected[ sourceLabel, {args}]
	
ensureNotebookIntegrity[ nb_NotebookObject, rawNotebook_Notebook, cellTags_List] :=
    Module[ {allCellTags, selectedCellTags, duplicateCellTags, srcTags, sl, outdPos, updNb},
    	sl = sourceLabel[ nb];
        (* Collect all CellTags from document. *)
        allCellTags = Flatten[Cases[rawNotebook,Cell[___,CellTags -> tags_,___] -> tags, Infinity]];
        (* We look only for the duplicates to elements of current CellTags list.*)
        selectedCellTags = Select[allCellTags,MemberQ[cellTags,#] &];
        (* Check if CellTags are unique in current Notebook. *)
        If[ Length[selectedCellTags] > Length[DeleteDuplicates[selectedCellTags]],
            (* If not give an appropriate warning *)
            duplicateCellTags = Cases[Select[Tally[selectedCellTags], duplicateLabel],{cellTag_,_} -> cellTag];
            notification[ translate["notUniqueLabel"], duplicateCellTags]
        ];
        (* Check if we have cell tags Source<sep>src with src != current notebook filename *)
        srcTags = DeleteDuplicates[ Select[ allCellTags, (StringMatchQ[#, "Source" ~~ $cellTagKeySeparator ~~ __] && # =!= sl)&]];
        If[ srcTags =!= {},
        	(* If yes, this indicates that the filename has changed and probably some formulae 
        	are stored in the environment with an outdated key 
        	-> update the key
        	-> update the cell tags
        	-> remove outdated tab from KBbrowser
        	 *)
        	updateKeys[ sl, srcTags];
        	outdPos = Position[ rawNotebook, CellTags -> { ___, s_String /; StringMatchQ[ s, "Source" ~~ $cellTagKeySeparator ~~ __] && s =!= sl, ___}];
        	updNb = MapAt[ (# /. s_String /; StringMatchQ[ s, "Source" ~~ $cellTagKeySeparator ~~ __] -> sl)&, rawNotebook, outdPos];
        	(* TODO: notify the user that outdated labels have been encountered, ask for update *)
        	(* NotebookPut[ updNb, nb] *)
        ]
    ]
ensureNotebookIntegrity[ args___] := unexpected[ ensureNotebookIntegrity, {args}]

duplicateLabel[{_, occurences_Integer}] := occurences > 1
duplicateLabel[args___] := unexpected[ duplicateLabel, {args}]

updateKeys[ new_String, srcTags_List] := Fold[ updateSingleKey, new, srcTags]
updateKeys[args___] := unexpected[updateKeys, {args}]

updateSingleKey[ new_String, old_String] :=
    Module[ {},
        $tmaEnv = Map[ Replace[ #, {id_,old}:>{id,new}]&, $tmaEnv, {2}];
        DownValues[kbSelectProve] = DownValues[kbSelectProve] /. {id_,old} :> {id,new};
        DownValues[kbSelectCompute] = DownValues[kbSelectCompute] /. {id_,old} :> {id,new};
        new
    ]
updateSingleKey[args___] := unexpected[updateSingleKey, {args}]


automatedFormulaLabel[nb_NotebookObject] := 
	Module[{formulaCounter, newCellTags},
		incrementFormulaCounter[nb];
		(* Find highest value of any automatically counted formula. *)
		formulaCounter = getFormulaCounter[nb];
		(* Construct new CellTags with value of the incremented formulaCounter as a list. *)
		newCellTags = {ToString[formulaCounter]}
	]
automatedFormulaLabel[args___] := unexpected[ automatedFormulaLabel, {args}]

applicableGlobalDeclarations[ nb_NotebookObject, raw_Notebook, pos_List] :=
	Module[{ globDeclID},
		(* Find global declarations that apply to the cell at position pos, i.e. those that occur "above" (incl. nesting)
		   from those cells collect the CellIDs *)
		globDeclID = Cases[ raw, c:Cell[ _, "GlobalDeclaration", ___, CellID -> id_, ___] /; occursBelow[ Position[ raw, c][[1]], pos] -> id, Infinity];
		(* Lookup the ids in the global declarations in the current notebook
		   Due to the way the ids are searched, they are sorted by the order how they occur in the notebook
		   -> this is how they have to be applied to the expression *)
		getGlobalDeclaration[ CurrentValue[ nb, "NotebookFullFileName"], globDeclID]
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
		availDecl = applicableGlobalDeclarations[ nb, raw, pos];
		If[ availDecl =!= {},
			globDecl = DisplayForm[ RowBox[ Map[ theoremaDisplay, availDecl]]],
			globDecl = translate[ "None"]
		];
		globDecl
	]
displayGlobalDeclarations[ args___] := unexpected[ displayGlobalDeclarations, {args}]

occursBelow[ {a___, p_}, {a___, q_, ___}] /; q > p := True
occursBelow[ x_, y_] := False
occursBelow[args___] := unexpected[ occursBelow, {args}]

updateKnowledgeBase[ form_, k_, glob_, tags_String] :=
    Module[ {newForm = applyGlobalDeclaration[ form, glob], fml},
    	transferToComputation[ newForm, k];
    	fml = makeFML[ key -> k, formula -> newForm, label -> tags, simplify -> False];
    	(* If new formulae are appended rather than prepended, the old formulae with the same label
    		have to be deleted first, because "DeleteDuplicates" would delete the new ones. *)
		$tmaEnv = Append[ DeleteCases[ $tmaEnv, _[ First[ fml], ___]], fml];
        If[ inArchive[],
            $tmaArch = Append[ DeleteCases[ $tmaArch, _[ First[ fml], ___]], fml];
        ]
    ]
updateKnowledgeBase[args___] := unexpected[ updateKnowledgeBase, {args}]

findSelectedFormula[ Cell[ _, ___, CellTags -> t_, ___]] :=
	Module[ { key = getKeyTags[ t]},
		Cases[ $tmaEnv, FML$[ key, _, __], {1}, 1]
	]	
findSelectedFormula[ sel_] := {}
findSelectedFormula[args___] := unexpected[ findSelectedFormula, {args}]

Clear[ applyGlobalDeclaration]
applyGlobalDeclaration[ expr_, g_List] :=
	Module[ {form = Fold[ applyGlobalDeclaration, expr, Reverse[ g]]},
		form //. {globalImplies$TM[ a_, b_] :> Module[ {fa}, b /; ((fa = freeVariables[ a]) =!= {} && Intersection[ fa, freeVariables[ b]] === {})]}
			 //. {fa:(globalForall$TM[ _, _, _]) :> Module[ {res}, res /; (res = analyzeQuantifiedExpression[ fa]) =!= fa]}
			 /. {globalForall$TM -> Forall$TM, globalImplies$TM -> Implies$TM}
	]

applyGlobalDeclaration[ expr_, globalForall$TM[ r_, c_]] := 
	globalForall$TM[ r, c, ReleaseHold[ markVariables[ Hold[ QU$[ r, expr]]]]]
applyGlobalDeclaration[ expr_, globalForall$TM[ r_, c_, d_]] := 
	With[ {new = applyGlobalDeclaration[ expr, d]},
		applyGlobalDeclaration[ new, globalForall$TM[ r, c]]
	]
applyGlobalDeclaration[ expr_, globalImplies$TM[ c_]] := globalImplies$TM[ c, expr]
applyGlobalDeclaration[ expr_, globalImplies$TM[ c_, d_]] := globalImplies$TM[ c, applyGlobalDeclaration[ expr, d]]
applyGlobalDeclaration[ expr_, domainConstruct$TM[ lhs_, rng:RNG$[ SIMPRNG$[ v_]]]] :=
	substituteFree[ ReleaseHold[ markVariables[ Hold[ QU$[ rng, expr]]]], {v -> lhs}]
applyGlobalDeclaration[ expr_, domainConstruct$TM[ lhs_, rng:RNG$[ DOMEXTRNG$[ v_, d_]]]] :=
	substituteFree[ ReleaseHold[ markVariables[ Hold[ QU$[ rng, expr]]]], {v -> lhs}]
applyGlobalDeclaration[ expr_, globalAbbrev$TM[ rng:RNG$[ a__ABBRVRNG$]]] := substituteFree[ ReleaseHold[ markVariables[ Hold[ QU$[ rng, expr]]]], 
	Apply[ Rule, {a}, {1}]]
applyGlobalDeclaration[ args___] := unexpected[ applyGlobalDeclaration, {args}]

(*
	analyze the ranges and drop all quantifiers that aren't needed
*)
analyzeQuantifiedExpression[ globalForall$TM[ r:RNG$[ __], c_, e_]] :=
	Module[ {freeE, rc, sc, dropVar, thinnedRange, thinnedCond},
		(* take the free vars in e *)
		freeE = freeVariables[ e];
		(* watch out for all conditions involving the free variables in e ... *)
		{rc, sc} = splitAnd[ c, freeE, False];
		(* ... and collect all free variables therein: these are the variables that require the quantifiers, the others can be dropped *)
		dropVar = Complement[ rngVariables[ r], freeVariables[ rc], freeE];
		(* all others and conditions involving the others can be dropped *)
		thinnedRange = thinnedExpression[ r, dropVar];
		If[ Length[ thinnedRange] == 0,
			e,
			thinnedCond = simplifiedAnd[ And$TM[ thinnedExpression[ sc, dropVar], rc]];
			globalForall$TM[ thinnedRange, thinnedCond, e]
		]
	]

initSession[] :=
    Module[ {},
    	$TheoremaArchives = {};
        $tmaEnv = {};
        $tmaArch = {};
        $globalDeclarations = {};
        $tmaArchNeeds = {};
        $formulaCounterName = "TheoremaFormulaCounter";
        $Pre=.;
        $PreRead=.;
    ]
initSession[args___] := unexpected[ initSession, {args}]

incrementFormulaCounter[nb_NotebookObject] :=
	Module[{formulaCounter},
		formulaCounter = getFormulaCounter[nb];
		formulaCounter++;
		(* Save Incremented formulaCounter to the notebook options. *)
		SetOptions[nb, CounterAssignments -> {{$formulaCounterName -> formulaCounter}}]
	]
incrementFormulaCounter[args___] := unexpected[ incrementFormulaCounter, {args}]

getFormulaCounter[nb_NotebookObject] :=
	Module[{formulaCounter},
		(* Extract theoremaFormulaCounter from the options of the notebook. *)
		formulaCounter = 
			$formulaCounterName /. Flatten[
				(* Extract CounerAssignments from the options of the notebook. *)
				{CounterAssignments } /. Options[nb, CounterAssignments]
			]
	]
getFormulaCounter[args___] := unexpected[ getFormulaCounter, {args}]
 
openEnvironment[expr_] :=
    Module[{},
		$parseTheoremaExpressions = True;
		(* Remember context path *)
		$origContextPath = $ContextPath;
        $ContextPath = Join[ {"Theorema`Language`"}, $TheoremaArchives, $ContextPath];
        (* Set default context when not in an archive *)
        If[ !inArchive[], Begin["Theorema`Knowledge`"]];
        expr
    ]
openEnvironment[args___] := unexpected[ openEnvironment, {args}]

closeEnvironment[] := 
	Module[{},
		(* Leave "Theorema`Knowledge`" context when not in an archive *)
		If[ !inArchive[], End[]];
		(* Restore context path that has been modified in openEnvironment *)
		$ContextPath = $origContextPath;
		$parseTheoremaExpressions = False; 
        updateKBBrowser[];
	]
closeEnvironment[args___] := unexpected[ closeEnvironment, {args}]

(* ::Section:: *)
(* Archives *)

getArchivePath[arch_String] :=
    Module[ {fn, absfn},
        Which[ FileExtension[arch]==="ta",
            fn = arch,
            StringQ[fn = Quiet[ContextToFileName[ arch]]],
            fn = StringReplacePart[ Last[ FileNameSplit[ fn]], "ta", -1],
            True,
            notification[ Theorema::archiveName, context];
            Return[$Failed]
        ];
        absfn = Block[ {$Path = $TheoremaArchivePath},
                    FindFile[fn]
                ];
        If[ absfn === $Failed,
            absfn = FileNameJoin[ {$TheoremaArchiveDirectory, fn}]
        ];
        absfn
    ]
getArchivePath[args___] := unexpected[ getArchivePath, {args}]

getArchiveNotebookPath[arch_String] := StringReplacePart[getArchivePath[arch],"nb",{-2,-1}]
getArchiveNotebookPath[args___] := unexpected[ getArchiveNotebookPath, {args}]

openArchive[name_String] :=
    Module[ {nb = EvaluationNotebook[], archiveNotebookPath, posBrowser},
        archiveNotebookPath = getArchiveNotebookPath[ name];
        (* Create the directory for an archive if does not exist. *)
        If[ !DirectoryQ[ DirectoryName[ archiveNotebookPath]],
            CreateDirectory[ DirectoryName[ archiveNotebookPath]]
        ];
        posBrowser = Position[ $kbStruct, CurrentValue["NotebookFullFileName"] -> _, 1, 1];
        If[ !FileExistsQ[ archiveNotebookPath],
        	NotebookSave[ nb, archiveNotebookPath];
        ];
        (* If the notebook was originally Untitled-n and has now been saved under the archive name
           then replace the name in the KB browser *)
        If[ Length[posBrowser] === 1,
            $kbStruct = ReplacePart[ $kbStruct, Append[posBrowser[[1]],1] -> CurrentValue["NotebookFullFileName"]]
        ];
        NotebookFind[ nb, "ArchiveInfo", All, CellStyle];
        (* We memorize the setting of loaded archives *)
        $globalArchivesList = $TheoremaArchives;
        BeginPackage[ "Theorema`Knowledge`" <> name, {"Theorema`"}];
        SelectionEvaluate[nb];
    ]
openArchive[args___] := unexpected[openArchive, {args}]

inArchive[] := StringLength[$Context] >= 9 && StringTake[$Context,-9]==="`private`"
inArchive[args___] := unexpected[inArchive, {args}]

currentArchiveName[] := StringDrop[$Context,-8]
currentArchiveName[args___] := unexpected[currentArchiveName, {args}]

SetAttributes[ processArchiveInfo, HoldAll];

processArchiveInfo[ a_] :=
	Module[{cf},
		cf = CurrentValue[ "CellFrameLabels"];
		Switch[ cf[[1,1]],
			translate[ "archLabelNeeds"],
			$tmaArchNeeds = a; Scan[ loadArchive, a], (* Remember and load current dependencies. *)
			translate["archLabelPublic"],
			ReleaseHold[ freshNames[ Hold[a]]];
			Begin[ "`private`"];     
		];
	]
processArchiveInfo[args___] := unexpected[processArchiveInfo, {args}]

closeArchive[_String] :=
    Module[ {nb = EvaluationNotebook[], currNB, archName, archFile, archivePath},
        End[];
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
        If[ !FileExistsQ[archivePath],
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
            archiveContent = ReadList[ archivePath, Hold[Expression]];
            ReleaseHold[ archiveContent];
            (* after reading and evaluating the archive $tmaArch has a value, namely the actual KB contained in the archive
               this is why we use the Block in order not
               to overwrite $tmaArch when loading an archive from within another one ... *)
            (* we use updateKnowledgeBase: this applies global declarations appropriately and 
               translates to computational form ... *)
            Scan[ updateKnowledgeBase[ #[[2]], #[[1]], globalDecl, #[[3]]]&, $tmaArch]
        ];
        $TheoremaArchives = DeleteDuplicates[ Prepend[ $TheoremaArchives, cxt]];
        If[ !FileExistsQ[archiveNotebookPath = getArchiveNotebookPath[ name]],
            archiveNotebookPath = archivePath
        ];
        If[ (pos = Position[ $kbStruct, archiveNotebookPath -> _]) === {},
            AppendTo[ $kbStruct, archiveNotebookPath -> $tmaArchTree],
            $kbStruct = ReplacePart[ $kbStruct, pos[[1]] -> (archiveNotebookPath -> $tmaArchTree)];
        ];
    ]
    Map[ StringReplace[ #, "Theorema`Knowledge`" -> "Theorema`Computation`Knowledge`", 1]&, $TheoremaArchives]
loadArchive[ l_List, globalDecl_:{}] := Scan[ loadArchive[ #, globalDecl]&, l]
loadArchive[args___] := unexpected[loadArchive, {args}]

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
    Module[ {file = OpenRead[f],meta,n},
        While[ !(OptionQ[meta = Read[file, Expression]] || meta === EndOfFile)];
        Close[file];
        If[ meta===EndOfFile,
            Return[translate["noArchName"]],
            n = "Archive name" /. meta;
            If[ StringQ[n] && StringMatchQ[n, (WordCharacter|"`")..~~"`"],
                n,
                translate["noArchName"]
            ]
        ]
    ]
archiveName[ f_String, Short] := StringReplace[ archiveName[ f], "Theorema`Knowledge`" -> ""]
archiveName[args___] :=
    unexpected[archiveName, {args}]


(* ::Section:: *)
(* Computation *)

SetAttributes[processComputation, HoldAll];

processComputation[ x:Theorema`Computation`Language`nE] := 
	Module[{},
		$Failed
	]
processComputation[x_] := Module[ { procSynt, res},
	procSynt = markVariables[ freshNames[ Hold[x]]];
	$TmaComputationObject = {Apply[ HoldForm, procSynt]};
	$TmaCompInsertPos = {2}; 
	setComputationContext[ "compute"];
	res = Check[ Catch[ ReleaseHold[ procSynt]], $Failed];
	setComputationContext[ "none"];
	(*NotebookWrite[ EvaluationNotebook[], Cell[ ToBoxes[ res, TheoremaForm], "ComputationResult", CellLabel -> "Out["<>ToString[$Line]<>"]="]];*)
	(* We force the MakeBoxes[ ..., TheoremaForm] to apply by setting $PrePrint in the CellProlog of a computation cell.
	   Unsetting $PrePrint in the CellEpilog ensures this behaviour only for Theorema computation *)
	AppendTo[ $TmaComputationObject, res]; 
	renameToStandardContext[ res]
]
processComputation[args___] := unexcpected[ processComputation, {args}]

openComputation[] := 
	Module[{},
		$evalCellID = CurrentValue[ "CellID"];
		$parseTheoremaExpressions = True;
		$ContextPath = Join[ 
			{"Theorema`Computation`Language`"}, 
			Map[ StringReplace[ #, "Theorema`Knowledge`" -> "Theorema`Computation`Knowledge`", 1]&, $TheoremaArchives], 
			$ContextPath]; 
		Begin[ "Theorema`Computation`Knowledge`"];
	]
openComputation[args___] := unexcpected[ openComputation, {args}]

closeComputation[] :=
    Module[ {},    	
        End[];
		$ContextPath = Select[ $ContextPath, (!StringMatchQ[ #, "Theorema`Computation`" ~~ __])&];
		$parseTheoremaExpressions = False;
		printComputationInfo[ $evalCellID];
    ]
closeComputation[args___] := unexcpected[ closeComputation, {args}]

displayBoxes[ expr_] := RawBoxes[ theoremaBoxes[ expr]]
displayBoxes[ args___] := unexpected[ displayBoxes, {args}]

renameToStandardContext[ expr_] :=
	Block[{$ContextPath = {"System`"}, $Context = "System`", stringExpr},
		(* BUGFIX amaletzk: added FullForm[], otherwise doesn't work if outermost symbol is built-in Power *)
		(* The result of $M functions may be Lists; They have to be transformed into tuples BEFORE freshNames[]
			is applied, because otherwise they are transformed into sets.
			We don't use makeTuple[] here, because otherwise we get problems with contexts. *)
		(* Do not substitute into a META$, because a META$ has a list of a.b.f. constants at pos. 3 *)
		stringExpr = ToString[ replaceAllExcept[ FullForm[ Hold[ expr]], {List -> Tuple$TM}, {}, Heads -> {Theorema`Computation`Language`META$}]];
		stringExpr = StringReplace[ stringExpr, "Theorema`Computation`" -> "Theorema`"];
		$ContextPath = Join[ {"Theorema`Language`"}, $TheoremaArchives, $ContextPath];
        (* Set default context when not in an archive *)
        ReleaseHold[ freshNames[ ToExpression[ stringExpr]]]
	]
renameToStandardContext[ args___] := unexpected[ renameToStandardContext, {args}]

(* ::Section:: *)
(* Computation within proving *)

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
	Module[{file, dir, fpMode},
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
			NotebookSave[
				NotebookCreate[ opts, StyleDefinitions -> makeColoredStylesheet[ "Notebook"]],
				file
			];
			SetOptions[ $FrontEnd, Global`FileChangeProtection -> fpMode];
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
	Module[{file, dir},
		If[ ValueQ[ $dirLastOpened],
			dir = $dirLastOpened,
			dir = $HomeDirectory
		];
		file = SystemDialogInput[ "FileOpen", {dir, {translate["fileTypeNotebook"] -> {"*.nb"}}}];
		If[ StringQ[ file] && FileExistsQ[ file],
			$dirLastOpened = DirectoryName[ file];
			trustNotebookDirectory[ $dirLastOpened];
			NotebookOpen[ file, opts, StyleDefinitions -> makeColoredStylesheet[ "Notebook"]]
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

(* ::Section:: *)
(* end of package *)

initSession[];
  
End[]

EndPackage[];