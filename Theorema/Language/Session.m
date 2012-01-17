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


freshNames[expr_Hold] :=
    replaceAllExcept[ expr, 
    {DoubleLongRightArrow|DoubleRightArrow->Implies$TM, DoubleLongLeftRightArrow|DoubleLeftRightArrow|Equivalent->Iff$TM,
    	SetDelayed->EqualDef$TM, Set->Equal$TM, Wedge->And$TM, Vee->Or$TM, List->makeSet, AngleBracket->Tuple$TM,
(*    s_Symbol /; (Context[s] === "System`") :> Module[ {name = ToString[s]},
                    If[ StringTake[ name, -1] === "$",
                        s,
                        ToExpression[ ToLowerCase[ StringTake[ name, 1]] <> StringDrop[ name, 1] <> "$TM"]
                    ]
                ],
                *)
    s_Symbol :> Module[ {name = ToString[s]},
                    If[ StringTake[ name, -1] === "$",
                        s,
                        ToExpression[ name <> "$TM"]
                    ]
                ]}, {Hold}]
freshNames[args___] := unexpected[ freshNames, {args}]

specifiedVariables[ (RNG$|Theorema`Computation`RNG$)[r___]] := Map[ extractVar, {r}]
specifiedVariables[ args___] := unexpected[ specifiedVariables, {args}]

extractVar[ r_[ (VAR$|Theorema`Computation`VAR$)[ v_], ___]] := v
extractVar[ r_[ v_, ___]] := v
extractVar[ args___] := unexpected[ extractVar, {args}]


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

markVariables[ Hold[ Theorema`Computation`QU$[ r_Theorema`Computation`RNG$, expr_]]] :=
    Module[ {s},
        s = Map[ sym_Symbol /; SymbolName[sym] === SymbolName[#] -> Theorema`Computation`VAR$[#]&, specifiedVariables[r]];
        replaceAllExcept[ markVariables[ Hold[ expr]], s, {}, Heads -> {Theorema`Computation`SEQ$, Theorema`Computation`VAR$}]
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
        PrependTo[ $ContextPath, "Theorema`Language`"];
        expr
    ]
openGlobalDeclaration[ args___] := unexpected[ openGlobalDeclaration, {args}]

closeGlobalDeclaration[] :=
    Module[ {},
		$ContextPath = DeleteCases[ $ContextPath, "Theorema`Language`"];
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
        updateKnowledgeBase[ReleaseHold[ freshNames[ markVariables[ Hold[x]]]], key, globDec, tags];
        (* close the environment to clear $Pre and $PreRead *)
        closeEnvironment[];
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
		 * Remove any automated labels (begins with "ID_" or "Source_").
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
 * Returns all CellTags except the generated tags used for formula identification, i.e. ID_... and Source_...
 *)
getCleanCellTags[cellTags_List] :=
    Select[ cellTags, !StringMatchQ[ #, (("ID_"|"Source_") ~~ __) | $initLabel]&]
getCleanCellTags[cellTag_String] := getCleanCellTags[{cellTag}]
getCleanCellTags[args___] := unexpected[getCleanCellTags,{args}]

getKeyTags[ cellTags_List] :=
    Select[ cellTags, StringMatchQ[ #, ("ID_"|"Source_") ~~ __]&]
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
        (* Check if we have cell tags Source_src with src != current notebook filename *)
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
        DownValues[Theorema`Computation`activeComputationKB] = DownValues[Theorema`Computation`activeComputationKB] /. {id_,old} :> {id,new};
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

occursBelow[ {a___, p_}, {a___, q_, ___}] /; q > p := True
occursBelow[ x_, y_] := False
occursBelow[args___] := unexpected[ occursBelow, {args}]

updateKnowledgeBase[ form_, key_, glob_, tags_] :=
    Module[ {newForm = applyGlobalDeclaration[ form, glob]},
        $tmaEnv = joinKB[ {{key, newForm, cellTagsToString[ tags]}}, $tmaEnv];
        If[ inArchive[],
            $tmaArch = joinKB[ {{key, newForm, cellTagsToString[ tags]}}, $tmaArch];
        ]
    ]
updateKnowledgeBase[args___] := unexpected[ updateKnowledgeBase, {args}]

findSelectedFormula[ Cell[ _, ___, CellTags -> t_, ___]] :=
	Module[ { key = getKeyTags[ t]},
		Cases[ $tmaEnv, {key, form_, tag_} -> {form, tag}]
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
        PrependTo[ $ContextPath, "Theorema`Language`"];
        (* Set default context if I am not in an archive. *)
        If[ !inArchive[], Begin["Theorema`Knowledge`"]];
        expr
    ]
openEnvironment[args___] := unexpected[ openEnvironment, {args}]

closeEnvironment[] := 
	Module[{},
		(* Restore context if I am not in an archive. *)
		If[ !inArchive[], End[]];
		$ContextPath = DeleteCases[ $ContextPath, "Theorema`Language`"];
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
            fn = StringReplacePart[ fn, "ta", -1],
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
        (* TODO: Check whether notebook or corresponding archive already exists in order to prevent overwriting existing archives *)
        posBrowser = Position[ $kbStruct, CurrentValue["NotebookFullFileName"] -> _, 1, 1];
        NotebookSave[ nb, archiveNotebookPath];
        If[ Length[posBrowser] === 1,
            $kbStruct = ReplacePart[ $kbStruct, Append[posBrowser[[1]],1] -> CurrentValue["NotebookFullFileName"]]
        ];
        NotebookFind[ nb, "ArchiveInfo", All, CellStyle];
        BeginPackage[ name, {"Theorema`"}];
        SelectionEvaluate[nb];
        (* openArchive is used as $PreRead, therefore it must return a string *)
        "Null"
    ]
openArchive[args___] := unexpected[openArchive, {args}]

inArchive[] := StringLength[$Context] >= 9 && StringTake[$Context,-9]==="`private`"
inArchive[args___] := unexpected[inArchive, {args}]

currentArchiveName[] := StringDrop[$Context,-8]
currentArchiveName[args___] := unexpected[currentArchiveName, {args}]

SetAttributes[ processArchiveInfo, HoldAll];

processArchiveInfo[ a_] :=
	Module[{nb = EvaluationNotebook[], cf},
		cf = CurrentValue[ nb, "CellFrameLabels"];
		Switch[cf[[1,1]],
			translate["archLabelNeeds"],
			$tmaArchNeeds = a; Scan[ loadArchive, a], (* Remember and load current dependencies. *)
			translate["archLabelPublic"],
			ReleaseHold[freshNames[ Hold[a]]];
			Begin["`private`"];     
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
        Block[ {$tmaArch},
            BeginPackage[cxt];
            (* we could just Get[archivePath], but we read the content and prevent evaluation for the moment
               this would be the place to process the archive content before evaluation *)
            archiveContent = ReadList[ archivePath, Hold[Expression]];
            ReleaseHold[ archiveContent];
            (* after reading and evaluating the archive $tmaArch has a value, namely the actual KB contained in the archive
               this is why we use the Block in order not
               to overwrite $tmaArch when loading an archive from within another one ... *)
        	(* ContextPath updated in order to make sure that public archive symbols are visible *)
            EndPackage[];
            (* before joining it to the KB, we apply global declarations *)
            $tmaArch = Map[ MapAt[ applyGlobalDeclaration[ #, globalDecl]&, #, 2]&, $tmaArch];
            $tmaEnv = joinKB[ $tmaArch, $tmaEnv];
        ];
        If[ !FileExistsQ[archiveNotebookPath = getArchiveNotebookPath[ name]],
            archiveNotebookPath = archivePath
        ];
        If[ (pos = Position[ $kbStruct, archiveNotebookPath -> _]) === {},
            AppendTo[ $kbStruct, archiveNotebookPath -> $tmaArchTree],
            $kbStruct = ReplacePart[ $kbStruct, pos[[1]] -> (archiveNotebookPath -> $tmaArchTree)];
        ];
    ]
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
archiveName[args___] :=
    unexpected[archiveName, {args}]


(* ::Section:: *)
(* Computation *)

SetAttributes[processComputation, HoldAll];

processComputation[x_] := Module[ {},
	printComputationInfo[];
	ReleaseHold[ freshNames[ markVariables[ Hold[x]]]]
]
processComputation[args___] := unexcpected[ processComputation, {args}]

openComputation[] := 
	Module[{},
		$parseTheoremaExpressions = True; 
		Begin["Theorema`Computation`"];
	]
openComputation[args___] := unexcpected[ openComputation, {args}]

closeComputation[] :=
    Module[ {},
        End[];
		$parseTheoremaExpressions = False;
    ]
closeComputation[args___] := unexcpected[ closeComputation, {args}]


(* ::Section:: *)
(* end of package *)

initSession[];
  
End[] (* End Private Context *)

EndPackage[];