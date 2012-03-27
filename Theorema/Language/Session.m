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

Begin["`Private`"] (* Begin Private Context *) 


(* ::Section:: *)
(* Preprocessing *)

freshNames[ Hold[ f_[ lhs_, Program[ rhs_]]]] :=
	Module[ {},
		ReplacePart[ freshNames[ Hold[ f[ lhs, "DUMMY"]]], {1,2} -> freshNamesProg[ Hold[ rhs]]]
	]
freshNames[expr_Hold] :=
	Module[ {symPos, repl},
		symPos = DeleteCases[ Position[ expr, _Symbol], {0}, {1}, 1];
		repl = Map[ # -> freshSymbol[ Extract[ expr, #]]&, symPos];
		ReplacePart[ expr, repl]
	]
freshNames[args___] := unexpected[ freshNames, {args}]

freshNamesProg[ expr_Hold] :=
	Module[ {symPos, repl},
		symPos = DeleteCases[ Position[ expr, _Symbol], {0}, {1}, 1];
		repl = Map[ # -> freshSymbolProg[ Extract[ expr, #]]&, symPos];
		ReleaseHold[ ReplacePart[ expr, repl]]
	]
freshNamesProg[ args___] := unexpected[ freshNamesProg, {args}]

freshSymbol[ s_Symbol] :=
    Module[ {name},
        Switch[ s,
            (* We use ToExpression in order to have the symbol generated in the right context
               depending on whether we are in a computation or not *)
            True|False, s,
            DoubleLongRightArrow|DoubleRightArrow, ToExpression[ "Implies$TM"],
            DoubleLongLeftRightArrow|DoubleLeftRightArrow|Equivalent, ToExpression[ "Iff$TM"],
        	SetDelayed, ToExpression[ "EqualDef$TM"], 
        	Set, ToExpression[ "Equal$TM"],
        	Wedge, ToExpression[ "And$TM"],
        	Vee, ToExpression[ "Or$TM"],
        	List, makeSet,
        	AngleBracket, makeTuple,
        	_,
        	name = ToString[s];
        	If[ StringTake[ name, -1] === "$",
            	s,
            	ToExpression[ name <> "$TM"]
        	]
        ]
    ]
freshSymbol[ args___] := unexpected[ freshSymbol, {args}]

freshSymbolProg[ s_Symbol] :=
    Module[ {name},
        Switch[ s,
            True|False, s,
        	Set, ToExpression[ "Assign$TM"],
        	_,
        	name = ToString[s];
        	If[ StringTake[ name, -1] === "$",
            	s,
            	ToExpression[ name <> "$TM"]
        	]
        ]
    ]
freshSymbolProg[ args___] := unexpected[ freshSymbolProg, {args}]

markVariables[ Hold[ QU$[ r_RNG$, expr_]]] :=
    Module[ {s},
        (* all symbols sym specified as variables in r are translated into VAR$[sym]
           we substitute all symbols with matching "base name" (neglecting the context!) so that also
           symbols in different context get substituted. This is important when processing archives, because
           global variables in an archive live in the archive's private context, whereas the global declaration
           lives in the context of the loading notebook/archive. With the substitution below, the private`sym becomes 
           a VAR$[loading`sym] *)
        s = Map[ sym_Symbol /; SymbolName[sym] === SymbolName[#] -> VAR$[#]&, specifiedVariables[r]];
        replaceAllExcept[ markVariables[ Hold[ expr]], s, {}, Heads -> {SEQ$, VAR$, NEW$, FIX$}]
    ]

markVariables[ Hold[ Theorema`Computation`Language`QU$[ r_Theorema`Computation`Language`RNG$, expr_]]] :=
    Module[ {s},
        s = Map[ sym_Symbol /; SymbolName[sym] === SymbolName[#] -> Theorema`Computation`Language`VAR$[#]&, specifiedVariables[r]];
        replaceAllExcept[ markVariables[ Hold[ expr]], s, {}, Heads -> {Theorema`Computation`Language`SEQ$, Theorema`Computation`Language`VAR$}]
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

processGlobalDeclaration[ x_] := 
	Module[ {},
		putGlobalDeclaration[ CurrentValue["NotebookFullFileName"], CurrentValue["CellID"], ReleaseHold[ freshNames[ markVariables[ Hold[x]]]]];
		closeGlobalDeclaration[];
	]
processGlobalDeclaration[ args___] := unexpected[ processGlobalDeclaration, {args}]


SetAttributes[processEnvironment,HoldAll];

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
        Catch[ updateKnowledgeBase[ReleaseHold[ freshNames[ markVariables[ Hold[x]]]], key, globDec, tags]];
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

getCellSourceLabel[ cellTags_] := getCellLabel[ cellTags, "Source"]
getCellSourceLabel[ args___] := unexpected[ getCellSourceLabel, {args}]

cellTagsToString[ cellTags_ /; VectorQ[ cellTags, StringQ]] := makeLabel[ Apply[ StringJoin, Riffle[ cellTags, $labelSeparator]]]
cellTagsToString[ ct_String] := makeLabel[ ct]
cellTagsToString[ args___] := unexpected[cellTagsToString, {args}]

makeLabel[ s_String] := "(" <> s <> ")"
makeLabel[ args___] := unexpected[ makeLabel, {args}]

relabelCell[nb_NotebookObject, cellTags_List, cellID_Integer] :=
	Module[{ newFrameLabel, newCellTags, autoTags},
		(* Join list of CellTags, use $labelSeparator *)
		newFrameLabel = cellTagsToString[ cellTags];
		(* Keep cleaned CellTags and add identification (ID) *)
		autoTags = {cellIDLabel[ cellID], sourceLabel[ nb]};
		newCellTags = Join[ autoTags, cellTags];
		SetOptions[NotebookSelection[nb], CellFrameLabels->{{None,newFrameLabel},{None,None}}, CellTags->newCellTags, ShowCellTags->False];
		(* return autoTags to be used as key for formula in KB *)
		autoTags
	]
relabelCell[args___] := unexpected[ relabelCell,{args}]

cellLabel[ l_, key_String] := key <> $cellTagKeySeparator <> ToString[l]
cellLabel[ args___] := unexpected[ cellLabel, {args}]

cellIDLabel[ cellID_] := cellLabel[ cellID, "ID"]
cellIDLabel[ args___] := unexpected[ cellIDLabel, {args}]

sourceLabel[ nb_NotebookObject] /; inArchive[] := cellLabel[ currentArchiveName[], "Source"]
sourceLabel[ nb_NotebookObject] := cellLabel[ CurrentValue[ nb, "NotebookFullFileName"], "Source"]
sourceLabel[ args___] := unexpected[ sourceLabel, {args}]
	
ensureNotebookIntegrity[ nb_NotebookObject, rawNotebook_Notebook, cellTags_List] :=
    Module[ {allCellTags, selectedCellTags, duplicateCellTags, srcTags, sl, outdPos, updNb},
    	sl = sourceLabel[];
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
        DownValues[Theorema`Interface`GUI`Private`kbSelectProve] = DownValues[Theorema`Interface`GUI`Private`kbSelectProve] /. {id_,old} :> {id,new};
        DownValues[Theorema`Computation`Language`Private`activeComputationKB] = DownValues[Theorema`Computation`Language`Private`activeComputationKB] /. {id_,old} :> {id,new};
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
		globDeclID = Cases[ raw, c:Cell[ _, "GlobalDeclaration"|"EnvironmentDeclaration", ___, CellID -> id_, ___] /; occursBelow[ Position[ raw, c][[1]], pos] -> id, Infinity];
		(* Lookup the ids in the global declarations in the current notebook
		   Due to the way the ids are searched, they are sorted by the order how they occur in the notebook
		   -> this is how they have to be applied to the expression *)
		getGlobalDeclaration[ CurrentValue[ nb, "NotebookFullFileName"], globDeclID]
	]
applicableGlobalDeclarations[ args___] := unexpected[ applicableGlobalDeclarations, {args}]

displayGlobalDeclarations[ nb_NotebookObject] :=
	Module[{ globDecl, pos, raw, magOpt = Options[ nb, Magnification], availDecl},
		raw = NotebookGet[ nb];
		pos = First[ Position[ raw, NotebookRead[ nb]]];
		availDecl = applicableGlobalDeclarations[ nb, raw, pos];
		If[ availDecl =!= {},
			globDecl = ExpressionCell[ theoremaDisplay[ applyGlobalDeclaration[ "\[SelectionPlaceholder]", availDecl]], 
				"DisplayFormula", ShowSyntaxStyles -> False],
			globDecl = TextCell[ translate[ "None"]]
		];
		CreateDialog[ Join[
			{
				Cell[ translate["Global Declarations"], "Title"],
				globDecl
			},
			{CancelButton[ translate[ "OK"], NotebookClose[ButtonNotebook[]]]}],
			First[ magOpt]]
	]
displayGlobalDeclarations[ args___] := unexpected[ displayGlobalDeclarations, {args}]

occursBelow[ {a___, p_}, {a___, q_, ___}] /; q > p := True
occursBelow[ x_, y_] := False
occursBelow[args___] := unexpected[ occursBelow, {args}]

updateKnowledgeBase[ form_, key_, glob_, tags_] :=
    Module[ {newForm = applyGlobalDeclaration[ form, glob]},
    	transferToComputation[ newForm, key];
        $tmaEnv = joinKB[ {{key, newForm, cellTagsToString[ tags]}}, $tmaEnv];
        If[ inArchive[],
            $tmaArch = joinKB[ {{key, newForm, tags}}, $tmaArch];
        ]
    ]
updateKnowledgeBase[args___] := unexpected[ updateKnowledgeBase, {args}]

findSelectedFormula[ Cell[ _, ___, CellTags -> t_, ___]] :=
	Module[ { key = getKeyTags[ t]},
		Cases[ $tmaEnv, {key, form_, tag_}, {1}, 1]
	]	
findSelectedFormula[ sel_] := {}
findSelectedFormula[args___] := unexpected[ findSelectedFormula, {args}]

Clear[ applyGlobalDeclaration]
applyGlobalDeclaration[ expr_, g_List] := Fold[ applyGlobalDeclaration, expr, Reverse[ g]]
applyGlobalDeclaration[ expr_, globalForall$TM[ r_, c_]] := Forall$TM[ r, c, ReleaseHold[ markVariables[ Hold[ QU$[ r, expr]]]]]
applyGlobalDeclaration[ expr_, globalForall$TM[ r_, c_, d_]] := 
	With[ {new = applyGlobalDeclaration[ expr, d]}, 
		Forall$TM[ r, c, ReleaseHold[ markVariables[ Hold[ QU$[ r, new]]]]]
	]
applyGlobalDeclaration[ expr_, globalImplies$TM[ c_]] := Implies$TM[ c, expr]
applyGlobalDeclaration[ expr_, globalImplies$TM[ c_, d_]] := Implies$TM[ c, applyGlobalDeclaration[ expr, d]]
applyGlobalDeclaration[ args___] := unexpected[ applyGlobalDeclaration, {args}]

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
            (* an alternative to updateKnowledgeBase would be:
            $tmaArch = Map[ MapAt[ applyGlobalDeclaration[ #, globalDecl]&, #, 2]&, $tmaArch];
            $tmaEnv = joinKB[ $tmaArch, $tmaEnv];*)
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
		printComputationInfo[];
		$Failed
	]
processComputation[x_] := Module[ { procSynt, res},
	procSynt = freshNames[ markVariables[ Hold[x]]];
	printComputationInfo[];
	setComputationContext[ "compute"];
	res = Catch[ ReleaseHold[ procSynt]];
	setComputationContext[ "none"];
	(*NotebookWrite[ EvaluationNotebook[], Cell[ ToBoxes[ res, TheoremaForm], "ComputationResult", CellLabel -> "Out["<>ToString[$Line]<>"]="]];*)
	(* We force the MakeBoxes[ ..., TheoremaForm] to apply by setting $PrePrint=displayBoxes in the CellProlog of a computation cell.
	   Unsetting $PrePrint in the CellEpilog ensures this behaviour only for Theorema computation *)
	res
]
processComputation[args___] := unexcpected[ processComputation, {args}]

openComputation[] := 
	Module[{},
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
    ]
closeComputation[args___] := unexcpected[ closeComputation, {args}]

displayBoxes[ expr_] := RawBoxes[ ToBoxes[ expr, TheoremaForm]]
displayBoxes[ args___] := unexpected[ displayBoxes, {args}]


(* ::Section:: *)
(* end of package *)

initSession[];
  
End[] (* End Private Context *)

EndPackage[];