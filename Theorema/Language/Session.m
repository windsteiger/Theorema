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
    {DoubleLongRightArrow|DoubleRightArrow->implies$TM, DoubleLongLeftRightArrow|DoubleLeftRightArrow->iff$TM,
    	SetDelayed->equalDef$TM, Wedge->and$TM, Vee->or$TM,
    s_Symbol/;(Context[s]==="System`") :> Module[ {name = ToString[s]},
                    If[ StringTake[name,{-1}]==="$",
                        s,
                        ToExpression[ToLowerCase[StringTake[name,1]]<>StringDrop[name,1]<> "$TM"]
                    ]
                ],
    s_Symbol :> Module[ {name = ToString[s]},
                    If[ StringTake[name,{-1}]==="$",
                        s,
                        ToExpression[name <> "$TM"]
                    ]
                ]}, {Hold}]
freshNames[args___] := unexpected[ freshNames, {args}]

specifiedVariables[RNG$[r___]] :=
    Map[ Part[#,1]&, {r}]

markVariables[Hold[QU$[r_RNG$, expr_]]] := 
 Module[{s = Map[#->VAR$[#]&, specifiedVariables[r]]},
  		replaceAllExcept[markVariables[Hold[expr]], s, {SEQ$, VAR$, NEW$, FIX$}]]

markVariables[Hold[h_[e___]]] := applyHold[
  		markVariables[Hold[h]],
  		markVariables[Hold[e]]]

markVariables[Hold[f_, t__]] := joinHold[
  		markVariables[Hold[f]],
  		markVariables[Hold[t]]]

markVariables[Hold[]] := Hold[]

markVariables[Hold[e_]] := Hold[e]

markVariables[args___] := unexpected[ markVariables, {args}]


(*processEnvironment[\[GraySquare]] :=
    (closeEnvironment[];
     SelectionMove[EvaluationNotebook[], After, EvaluationCell];)
*)
SetAttributes[processEnvironment,HoldAll];

processEnvironment[x_] :=
    Module[ {nb = EvaluationNotebook[], newLab},
        newLab = adjustFormulaLabel[nb];
        updateKnowledgeBase[ReleaseHold[ freshNames[ markVariables[ Hold[x]]]], newLab];
    ]
processEnvironment[args___] := unexcpected[ processEnvironment, {args}]

adjustFormulaLabel[nb_NotebookObject] := 
	Module[{ cellTags, cellID, newCellTags, cleanCellTags}, 
		SelectionMove[nb, All, EvaluationCell];
        {cellTags,cellID} = {CellTags,CellID} /. Options[NotebookSelection[nb], {CellTags,CellID}];
		(*
		 * Make sure we have a list of CellTags
		 *)
		cellTags = Flatten[{cellTags}];
		(*
		 * Remove any automated labels (begins with "ID_" or "Source_").
		 * Remove initLabel.
		 *)
		cleanCellTags = getCleanCellTags[cellTags];
        (*
         * Replace unlabeled formula with counter.
         *)
         If[cleanCellTags==={},
         	cleanCellTags = automatedFormulaLabel[nb]
         ];
        (*
         * Relabel Cell and hide CellTags.
         *)
        newCellTags = relabelCell[nb,cleanCellTags,cellID];
        SelectionMove[nb, After, Cell];
        newCellTags
	]
adjustFormulaLabel[args___]	:= unexpected[adjustFormulaLabel,{args}]

(*
 * Returns all CellTags except the generated tags used for formula identification, i.e. ID_...
 *)
getCleanCellTags[cellTags_List] :=
    Select[ cellTags, !StringMatchQ[ #, (("ID_"|"Source_") ~~ __) | $initLabel]&]
getCleanCellTags[args___] := unexpected[getCleanCellTags,{args}]

getKeyTags[cellTags_List] :=
    Select[ cellTags, StringMatchQ[ #, ("ID_"|"Source_") ~~ __]&]
getKeyTags[args___] := unexpected[getKeyTags,{args}]

relabelCell[nb_NotebookObject, cellTags_List, cellID_Integer] :=
	Module[{ newFrameLabel, newCellTags, autoTags},
		(* Perform check, weather are the given CellTags unique in the documment. *)
		ensureNotebookIntegrity[nb,cellTags];
		(* Join list of CellTags, use $labelSeparator. *)
		newFrameLabel = StringJoin @@ Riffle[cellTags,$labelSeparator];
		(* Put newFrameLabel in brackets. *)
		newFrameLabel = "("<>newFrameLabel<>")";
		(* Keep cleaned CellTags and add identification (ID). *)
		autoTags = {cellIDLabel[cellID], sourceLabel[]};
		newCellTags = Join[ autoTags, cellTags];
		SetOptions[NotebookSelection[nb], CellFrameLabels->{{None,newFrameLabel},{None,None}}, CellTags->newCellTags, ShowCellTags->False];
		autoTags
	]
relabelCell[args___] := unexpected[ relabelCell,{args}]

cellIDLabel[ cellID_Integer] := "ID_" <> ToString[cellID]
cellIDLabel[ args___] := unexpected[ cellIDLabel, {args}]

sourceLabel[ ] /; inArchive[] := "Source_" <> currentArchiveName[]
sourceLabel[ ] := "Source_" <> CurrentValue["NotebookFullFileName"]
sourceLabel[ args___] := unexpected[ sourceLabel, {args}]
	
ensureNotebookIntegrity[nb_NotebookObject, cellTags_List] :=
    Module[ {rawNotebook,allCellTags,selectedCellTags,duplicateCellTags,srcTags, sl, outdPos, updNb},
    	sl = sourceLabel[];
        rawNotebook = NotebookGet[nb];
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
        srcTags = DeleteDuplicates[ Select[ allCellTags, (StringMatchQ[#, "Source_" ~~ __] && # =!= sl)&]];
        If[ srcTags =!= {},
        	(* If yes, this indicates that the filename has changed and probably some formulae 
        	are stored in the environment with an outdated key 
        	-> update the key
        	-> update the cell tags
        	-> remove outdated tab from KBbrowser
        	 *)
        	updateKeys[ sl, srcTags];
        	outdPos = Position[ rawNotebook, CellTags -> { ___, s_String /; StringMatchQ[ s, "Source_" ~~ __] && s =!= sl, ___}];
        	updNb = MapAt[ (# /. s_String /; StringMatchQ[ s, "Source_" ~~ __] -> sl)&, rawNotebook, outdPos];
        	(* TODO: notify the user that outdated labels have been encountered, ask for update *)
        	(*NotebookPut[ updNb, nb]*)
        ]
    ]
checkNotebookIntegrity[args___] := unexpected[checkNotebookIntegrity,{args}]

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

(* ::Section:: *)
(* Region Title *)

automatedFormulaLabel[nb_NotebookObject] := 
	Module[{formulaCounter, newCellTags},
		incrementFormulaCounter[nb];
		(* Find highest value of any automatically counted formula. *)
		formulaCounter = getFormulaCounter[nb];
		(* Construct new CellTags with value of the incremented formulaCounter as a list. *)
		newCellTags = {ToString[formulaCounter]}
	]
automatedFormulaLabel[args___] := unexpected[ automatedFormulaLabel, {args}]

updateKnowledgeBase[ form_, lab_] :=
    If[ inArchive[], 
    	$tmaArch = Union[ $tmaArch, {{lab, form}}, SameTest -> (#1[[1]]===#2[[1]]&)],
    	$tmaEnv = Union[ $tmaEnv, {{lab, form}}, SameTest -> (#1[[1]]===#2[[1]]&)]
    ]
updateKnowledgeBase[args___] := unexpected[ updateKnowledgeBase, {args}]

		
initSession[] :=
    Module[ {},
        $environmentLabels = {};
        $tmaEnv = {};
        $tmaArch = {};
        $tmaArchNeeds = {};
        $formulaCounterName = "TheoremaFormulaCounter";
        $Pre=.;
        $PreRead=.;
    ]
initSession[args___] := unexpected[ initSession, {args}]

currentEnvironment[] := First[$environmentLabels]
currentEnvironment[args___] := unexpected[ currentEnvironment, {args}]

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
 
openEnvironment[type_String] :=
    Module[{},
		$parseTheoremaExpressions = True; 
        PrependTo[$environmentLabels, type];
        SetOptions[ InputNotebook[], DefaultNewCellStyle -> "FormalTextInputFormula"];
        PrependTo[ $ContextPath, "Theorema`Language`"];
        (* Set default context if I am not in an archive. *)
        If[ !inArchive[], Begin["Theorema`Knowledge`"]];
    ]
openEnvironment[args___] := unexpected[ openEnvironment, {args}]

closeEnvironment[] := 
	Module[{},
		(* Restore context if I am not in an archive. *)
		If[ !inArchive[], End[]];
		$ContextPath = DeleteCases[ $ContextPath, "Theorema`Language`"];
		SetOptions[ InputNotebook[], DefaultNewCellStyle -> "Input"];
        $environmentLabels = Rest[$environmentLabels];
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
		SelectionMove[nb, All, EvaluationCell];
        {cf} = {CellFrameLabels} /. Options[NotebookSelection[nb], CellFrameLabels];
		Switch[cf[[1,1]],
			translate["archLabelNeeds"],
			$tmaArchNeeds = a; Scan[ loadArchive, a], (* Remember and load current dependencies. *)
			translate["archLabelPublic"],
			ReleaseHold[freshNames[ Hold[a]]];
			Begin["`private`"];
			SelectionMove[nb, After, Cell];      
		];
	]
processArchiveInfo[args___] := unexpected[processArchiveInfo, {args}]

closeArchive[_String] :=
    Module[ {nb = EvaluationNotebook[], currNB = CurrentValue["NotebookFullFileName"], archName, archFile, archivePath},
        End[];
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

SetAttributes[ loadArchive, Listable]
loadArchive[name_String] :=
    Module[ {archivePath, cxt, archiveContent, archiveNotebookPath, pos},
        (* Save Current Settings into the local Variables *)
        archivePath = getArchivePath[ name];
        If[ !FileExistsQ[archivePath],
            notification[ Theorema::archiveNotFound, archivePath];
            Return[]
        ];
        cxt = archiveName[ archivePath];
        Begin[cxt];
        	archiveContent = ReadList[ archivePath, Hold[Expression]];
        	ReleaseHold[ archiveContent];
        EndPackage[]; (* ContextPath updated in order to make sure that public archive symbols are visible *)
        $tmaEnv = Union[$tmaEnv, $tmaArch];
        If[ !FileExistsQ[archiveNotebookPath = getArchiveNotebookPath[ name]],
            archiveNotebookPath = archivePath
        ];
        If[ (pos = Position[ $kbStruct, archiveNotebookPath -> _]) === {},
            AppendTo[ $kbStruct, archiveNotebookPath -> $tmaArchTree],
            $kbStruct[[pos[[1,1]]]] = archiveNotebookPath -> $tmaArchTree
        ];
    ]
loadArchive[args___] := unexpected[loadArchive, {args}]

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
(* Built-in computation *)

Begin["Theorema`Computation`"]

activeComputation[_] := False
activeComputationKB[_] := False

plus$TM /; activeComputation["plus"] = Plus
times$TM /; activeComputation["times"] = Times
set$TM /; activeComputation["equal"] = equal

End[]

(* ::Section:: *)
(* end of package *)

initSession[];
  
End[] (* End Private Context *)

EndPackage[];