(* Theorema 
    Copyright (C) 2010 The Theorema Group

    This file is part of Theorema 2.0
    
    Theorema 2.0 is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Theorema 2.0 is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

(* TODO: Some auxiliary functions defined in this file are very similar to functions defined in "Provers/Common.m".
	Maybe one could try to "unify" them at some point. (A good example is "proofToBoxes" vs. "proofObjectToCell".) *)

(* We extend the "Theorema`Provers`Strategies`-context, i.e. all symbols defined in this file go to this context
(or, more precisely, to "`Strategies`Private`").
The reason for separating the implementation of the interactive proof strategy from the implementation of the
other strategies simply is that the former requires a whole lot of auxiliary functions (e.g. for creating dialog
windows) that otherwise would completely mess up file "Strategies.m". *)
BeginPackage["Theorema`Provers`Strategies`"]

Needs[ "Theorema`Common`"]
Needs[ "Theorema`Provers`"]

Begin["`Private`"]

$defaultThresholds = {20, 85, 20};

(* 'fullInteractiveStrategy[ ps, rules ]' asks the user for an inference step, and returns either
	- a list of new nodes, where the empty list indicates that the proof search shall be aborted (without changing the proof),
	- the ID of a pending proof situation where the proof search shall continue,
	- a pair '{a, b}', indicating that the proof search shall continue at the next/prev ('a') pending proof situation originating from an AND- or OR-node ('b').
*)
fullInteractiveStrategy[ psOrig_PRFSIT$] :=
	Module[ {ps = psOrig, allRules, rules, threshold, status, statusText = Text[ translate[ "makeInfStep"]], filterString = "", filteredRule = 0, psCells, ruleNames,
			goalSelected = False, kbS, makeAlternatives = False, nb = Null, dr, setNB = Null, thresNB = Null, psNB = Null, rNB, newNodes = {}, proposedRules},
		status = statusText;
		
		threshold = getOptionalComponent[ psOrig, "$FullInteractiveStrat$threshold"];
		If[ !MatchQ[ threshold, {__}], threshold = $defaultThresholds];
		proposedRules = getOptionalComponent[ psOrig, "proposedRules"];
		If[ !MatchQ[ proposedRules, {___List}], proposedRules = {}];
		While[ newNodes === {},
			allRules = getRulesPartitionedFilter[ ps, proposedRules, "term"|"levelSat1"|"levelSat2", threshold];
			proposedRules = First[ allRules];
			If[ proposedRules =!= {},
				statusText = {};
				While[ proposedRules =!= {},
					With[ {r = First[ proposedRules], rl = proposedRules[[1, 1]]},
						proposedRules = Rest[ proposedRules];
						If[ !MemberQ[ r, "Repeated"],
							ps = Replace[ ps, ("proposedRules" -> _List) -> ("proposedRules" -> proposedRules), {1}]
						];
						newNodes = applyAllRulesOnce[ ps, DeleteCases[ {inferenceRule[ rl]}, _inferenceRule]];
						Switch[ Length[ newNodes],
							0,
							AppendTo[ statusText, StringForm[ translate[ "ruleFailed"], MessageName[ rl, "usage", $TmaLanguage]]];
							If[ MemberQ[ r, "Repeated"],
								ps = Replace[ ps, ("proposedRules" -> _List) -> ("proposedRules" -> proposedRules), {1}]
							],
							
							1,
							proposedRules = {},
							
							_,
							newNodes = {First[ newNodes]};
							proposedRules = {}
						]
					]
				];
				status = statusText = Text[ Column[ Append[ statusText, translate[ "makeInfStep"]]]];
			];
			(* 'proposedRules' now is {}, meaning that no proposed rules will be applied in another iteration of the main loop. *)
			
			If[ newNodes === {} && Length[ allRules] > 2,
				newNodes = applyAllRulesOnce[ ps, allRules[[2]]];
				Which[
					newNodes === {} && Length[ allRules] > 3,
					Catch[ Scan[
							(newNodes = applyAllRulesOnce[ ps, #]; If[ newNodes =!= {}, Throw[ Null]])&,
							Take[ allRules, {3, -2}]
						]
					],
					
					Length[ newNodes] > 1,
					newNodes = {First[ newNodes]}
				]
			];
			If[ newNodes === {},
				$currentPS = ps;
				rules = Last[ allRules];
				ruleNames = rulesToString[ rules, 80];
				filterString = "";
				filteredRule = 0;
				If[ nb === Null,
					kbS = Table[ False, {Length[ kb@ps]}];
					psCells = selectablePSitCells[ ps, goalSelected, kbS];
					nb = Notebook[ psCells,
							DockedCells -> {
								Cell[ BoxData[ ToBoxes[ Row[ actionRow[ "log.txt", Hold[ ruleNames], Hold[ makeAlternatives], Hold[ kbS]], Spacer[ 5]]]], "Hint", Background -> TMAcolor[ 1], Deployed -> True],
								Cell[ BoxData[ ToBoxes[ Dynamic[ status]]], "Text", ShowStringCharacters -> False, Deployed -> True]
							},
							StyleDefinitions -> makeColoredStylesheet[ "Dialog"],
							Magnification -> CurrentValue[ First[ getTheoremaCommander[]], Magnification],
							ShowCellBracket -> False,
							Editable -> False,
							WindowElements -> {"VerticalScrollBar", "HorizontalScrollBar", "StatusArea"},
							WindowTitle -> "Proof Commander"]
				];
				newNodes = Catch[ While[ True,
					dr = DialogInput[ nb, WindowSize -> 700,
							NotebookEventActions -> Join[
									{
										"WindowClose" :> DialogReturn[ $Canceled],
										"ReturnKeyDown" :> If[ filteredRule > 0, DialogReturn[ filteredRule]],
										{"KeyDown", FromCharacterCode[ 8]} :> If[ StringLength[ filterString] > 0,
																					status = makeStatus[ statusText, filterString = StringDrop[ filterString, -1], rules, Hold[ filteredRule]]
																			  ],
										{"KeyDown", FromCharacterCode[ 127]} :> (status = makeStatus[ statusText, filterString = "", rules, Hold[ filteredRule]])
									},
									Map[ With[ {k = FromCharacterCode[ #]},
											{"KeyDown", k} :> (status = makeStatus[ statusText, filterString = filterString <> k, rules, Hold[ filteredRule]])
										]&,
										Range[32, 126]
									]
								]
						];
					Switch[ dr,
						$Canceled|$Failed,
						Throw[$Aborted],
						
						$tryagain[ _],
						status = statusText = Text[ translate[ "psNotAutomatically"] <> " " <> translate[ "makeInfStep"]];
						If[ TrueQ[ First[ dr]] && Last[ threshold] =!= 100,
							threshold[[-1]] = 100;
							updateThreshold[ ps, threshold]
						];
						Throw[ Null],
						
						$removeKB,
						dr = {createNode[ Theorema`Provers`$FullInteractiveStrat$removeKB, toBeProved[ goal -> goal@ps, kb -> Pick[ kb@ps, kbS], Sequence@@Drop[ ps, 3]], psOrig, makeAlternatives]};
						makeAlternatives = False;
						Throw[dr],
						
						$move,
						If[ psNB === Null, psNB = proofsitNB[ id@ps]];
						If[ psNB === $Failed,
							status = statusText = errorText[];
							filterString = "",
							$selectedProofStep = id@ps;
							dr = FISDialogInput[ psNB, WindowTitle -> translate[ "choosePS"]];
							If[ ListQ[ dr], 
								$interactiveProofSitSel = True;
								$lastChoice = dr;
								(* Since the current PRFSIT is not really changed (only settings/thresholds), no alternatives are created. *)
								makeAlternatives = False;
								Throw[ {createNode[ ps, psOrig, False]}], 
								status = statusText = errorText[ translate[ "noNewPS"]];
								filterString = ""
							]
						],
						
						$move[ _, _, _],
						If[ TrueQ[ Last[ dr]] && Last[ threshold] =!= 100,
							threshold[[-1]] = 100;
							updateThreshold[ ps, threshold]
						];
						dr = getNeighborID[ id@ps, First[ dr], dr[[2]]];
						If[ dr === $Failed,
							status = statusText = errorText[ translate[ "noPSFound"]];
							filterString = "",
							$interactiveProofSitSel = True;
							$lastChoice = dr;
							makeAlternatives = False;
							Throw[ {createNode[ ps, psOrig, False]}]
						],
						
						$adjustSettings,
						If[ setNB === Null, setNB = settingsNB[ ps]];
						If[ setNB =!= $Failed,
							dr = FISDialogInput[ setNB, WindowTitle -> translate[ "changeProverSettings"]];
							If[ ListQ[ dr] && Length[ dr] === 7,
								status = statusText = Text[ translate[ "settingsChanged"] <> " " <> translate[ "makeInfStep"]];
								ps = Replace[ ps, MapThread[ ((#1 -> _) -> (#1 -> #2)) &, {{Theorema`Common`rules, ruleActivity, rulePriority, strategy}, Drop[dr, -3]}], {1}];
								$interactiveProofSitSel = dr[[5]];
								$interactiveNewProofSitFilter = dr[[6]];
								If[ TrueQ[ Last[ dr]],
									(*rule set changed;update menu*)
									rules = Cases[ dr[[3]], ((Rule|RuleDelayed)[ r_, p_Integer] /; p >= Last[ threshold]) :> r];
									ruleNames = rulesToString[ rules, 80]
								],
								status = statusText = errorText[ translate[ "settingsNotChanged"]];
								filterString = ""
							]
						],
						
						$adjustThreshold,
						If[ thresNB === Null, thresNB = thresholdNB[ threshold]];
						If[ thresNB =!= $Failed, 
							dr = FISDialogInput[ thresNB, WindowTitle -> translate[ "changeThresholds"]];
							If[ MatchQ[ dr, {__}], 
								status = statusText = Text[ translate[ "thresholdsChanged"] <> " " <> translate[ "makeInfStep"]];
								If[ threshold =!= dr, updateThreshold[ ps, threshold = dr]], 
								status = errorText[ translate[ "thresholdsNotChanged"]];
								filterString = ""
							]
						],
						
						_Integer?Positive,
						(*try to apply inference rule*)
						dr = inferenceRule[ rules[[dr]]];
						Switch[ dr,
							_inferenceRule,
							status = statusText = errorText[ translate[ "invalidRule"]];
							filterString = "",
							_,
							$applyAllPossibleInferences = True;
							$goalActivated = goalSelected;
							$knowledgeActivated = Map[ key, Pick[ kb@ps, kbS]];
							dr = Replace[
									DeleteCases[ ReplaceList[ ps, dr], $Failed],
									{
										Theorema`Provers`Common`Private`ORNODE$[ Theorema`Provers`Common`Private`PRFINFO$[ proveAlternatives, ___], nodes__, pending] :> nodes,
										{nodes___} :> nodes
									},
									{1}
								];
							$applyAllPossibleInferences = False;
							$goalActivated = True;
							$knowledgeActivated = Null;
							(* Throw away all failed/disproved branches. *)
							dr = DeleteCases[ Map[ propagateProofValues,
													Cases[ dr, (_Theorema`Provers`Common`Private`ANDNODE$|_Theorema`Provers`Common`Private`ORNODE$|_Theorema`Provers`Common`Private`TERMINALNODE$)]],
											_[ ___, failed|disproved]
								];
							With[ {tmp = Cases[dr, _[ ___, proved], {1}, 1]},
								If[ tmp =!= {},
									(* If one branch succeeded, we only take this one. *)
									dr = tmp
								]
							];
							Switch[ Length[ dr],
								0,
								status = statusText = errorText[ translate[ "noApplicableRule"]];
								filterString = "",
								1,
								Throw[ dr],
								_,
								rNB = ruleNB[ {formula@goal@ps, Map[ formula, kb@ps]}, dr, Hold[ makeAlternatives]];
								If[ rNB === $Failed,
									status = statusText = errorText[ "Failure."],
									With[ {tmp = FISDialogInput[ rNB, WindowTitle -> translate[ "chooseSteps"]]},
										If[ IntegerQ[ tmp] && tmp >= 1 && tmp <= Length[ dr],
											Throw[ {dr[[tmp]]}],
											status = statusText = errorText[ translate[ "noNewSteps"]];
											filterString = ""
										]
									]
								]
							]
						]
					]
				]
			]];
			Switch[ newNodes,
				$Aborted,
				(* We mark the PRFSIT where the proof was aborted, such that we can continue here later. *)
				newNodes = createNode[ Append[ ps, "Aborted" -> True], psOrig, False];
				$proofAborted = True,
					
				{},
				newNodes = makeTERMINALNODE[ makePRFINFO[ name -> noApplicableRule, used -> {List@@ps}], failed],
					
				{_},
				newNodes = If[ makeAlternatives,
								$lastChoice = id@First[ newNodes];
								makeORNODE[ makePRFINFO[ name -> proofAlternatives, used -> used@newNodes, generated -> generated@newNodes],
									Append[ newNodes, psOrig]
								], 
								First[ newNodes]
							],
								
				{__},
				$lastChoice = id@First[ newNodes];
				newNodes = makeORNODE[ makePRFINFO[ name -> proofAlternatives, used -> used@newNodes, generated -> generated@newNodes], 
								If[ makeAlternatives,
									Append[ newNodes, psOrig], 
									newNodes
								]
							],
							
				_,
				(*one more loop iteration*)
				newNodes = {}
			]
		];
		newNodes
	]
fullInteractiveStrategy[ args___] := unexpected[ fullInteractiveStrategy, {args}]

SetAttributes[ selectablePSitCells, HoldRest];
selectablePSitCells[ PRFSIT$[ g_FML$, kb_List, ___], gv_, av_] :=
	Module[ {gc, ac, lab = makeLabel[ label@g]},
		gc = {
				Cell[ BoxData[ RowBox[ {ToBoxes[ Style[ Checkbox[ Dynamic[gv]], Deployed -> True]], ToBoxes[ Spacer[4]], selectableExpressionBox[ g]}]], "Goal"],
				Cell[ lab, "GoalLabel", Deployed -> True]
			};
		ac = MapIndexed[ Function[ {k, index},
						With[ {i = First[ index]},
							lab = makeLabel[ label@k];
							{
								Cell[ BoxData[ RowBox[ {ToBoxes[ Style[ Checkbox[ Dynamic[ av[[i]]]], Deployed -> True]], ToBoxes[ Spacer[ 4]], selectableExpressionBox[ k]}]], "Assumption"],
								Cell[ lab, "AssumptionLabel", Deployed -> True]
							}
						],
						{HoldFirst}
					],
					kb
				];
		{
			Cell[ translate[ "ps"], "Subsubsection", CellDingbat -> Cell[ BoxData[ ToBoxes[ Checkbox[ Dynamic[ allTrue[ Prepend[ av, gv], Identity], (gv = #; av = Table[ #, {Length[ av]}])&]]]]], Deployed -> True],
			GridBox[ Join[
						{gc},
						If[ ac === {},
							{{
								Cell[ TextData[ StyleBox[ translate[ "noKnowledge"], Italic, Gray]], "Text", Deployed -> True],
								Cell[ RowBox[ {}], Deployed -> True]
							}},
							ac
						]
					],
					ColumnAlignments -> Left,
					RowLines -> {True, False}
				]
		}
	]
	
actionRow[ filename_String, Hold[ ruleNames_], Hold[ ma_], Hold[ av_]] :=
	With[ {i = id@$currentPS},
		{
			Tooltip[ Toggler[ Dynamic[ ma], {True -> Style[ "\[Or]", Larger, Bold], False -> Style[ "\[Or]", Larger, TMAcolor[ 13]]}],
					translate[ "ttMakeAlternatives"]
			],
	
			Tooltip[ Button[ "Show Proof",
						(
							$TMAproofNotebook = tmaNotebookPut[ Notebook[ pObjCells[]], "Proof"];
							NotebookLocate[ {CurrentValue[ $TMAproofNotebook, "NotebookFileName"], i}]
						),
						Appearance -> "Frameless"
					],
					translate[ "showProofProgress"]
			],
	
			Tooltip[ Dynamic[ Refresh[ ActionMenu[ translate[ "inferenceRules"], ruleNames, Appearance -> "Frameless", Enabled -> (ruleNames =!= {})], TrackedSymbols :> {ruleNames}]], 
					translate[ "ttApplyRule"]
			],
	
			Tooltip[ ActionMenu[ translate[ "proofSearch"], {"\[LeftArrow] \[And]" :> DialogReturn[ $move[ Previous, And, False]],
													"\[Rule] \[And]" :> DialogReturn[ $move[ Next, And, False]],
													"\[LeftArrow] \[Or]" :> DialogReturn[ $move[ Previous, Or, False]],
													"\[Rule] \[Or]" :> DialogReturn[ $move[ Next, Or, False]],
													translate[ "choosePSMenuItem"] :> DialogReturn[ $move],
													translate[ "tryAgain"] :> DialogReturn[ $tryagain[ False]],
													translate[ "proveNowAuto"] :> DialogReturn[ $tryagain[ True]],
													translate[ "proveLaterAuto"] :> DialogReturn[ $move[ Next, And, True]]},
								Appearance -> "Frameless"],
					translate[ "ttProofSearch"]
			],
	
			Tooltip[ ActionMenu[ translate[ "settings"], {translate[ "adjustProver"] :> DialogReturn[ $adjustSettings],
													translate[ "adjustThresholds"] :> DialogReturn[ $adjustThreshold]},
								Appearance -> "Frameless"],
					translate[ "ttSettings"]
			],
	
			Tooltip[ ActionMenu[ translate[ "debugging"], {
												translate[ "inspectPO"] :>
													CreateDocument[
														{CellGroup[ {TextCell[ translate[ "curPS"], "Subsubsection"], $currentPS}, 1],
														CellGroup[ {TextCell[ translate[ "curPO"], "Subsubsection"], $TMAproofObject}, 1]},
														WindowTitle -> translate[ "PO"]
													],
												translate[ "inspectRewriteRules"] :> rewriteRulesDocument[ $currentPS],
												translate[ "showHiddenKnowledge"] :> knowledgeDocument[ $currentPS],
												translate[ "psToFile"] :> PutAppend[ $currentPS, filename],
												translate[ "poToFile"] :> PutAppend[ $TMAproofObject, filename],
												translate[ "saveProof"] :> saveProof[ i, "TheoremaProof.m"]},
								Appearance -> "Frameless"],
					translate[ "ttDebugging"]
			]
		}
	]

rewriteRulesDocument[ ps_PRFSIT$] :=
	Module[ {rules, rw = getOptionalComponent[ ps, "rewriting"]},
		rules = Replace[ rw,
					{
						((Rule|RuleDelayed)[ _String, {}]) :> Null,
						((Rule|RuleDelayed)[ cat_String, l_List]) :> CellGroup[ {TextCell[ "Rewriting/" <> cat, "Subsubsection"], l}, 1]
					},
					{1}
				];
		rules = Join[ rules,
					MapThread[
						With[ {r = Cases[ ps, ((Rule|RuleDelayed)[ #1, l_List]) :> l, {1}, 1]},
							If[ r === {} || (First[ r] === {}),
								Null,
								CellGroup[ {TextCell[ #2, "Subsubsection"], First[ r]}, 1]
							]
						]&,
						{{kbRules, goalRules, substRules, defRules}, {"Forward", "Backward", "Substitution", "Definition"}}
					]
				];
		CreateDocument[ DeleteCases[ rules, Null], WindowTitle -> translate[ "rewriteRules"]]
	]
	
knowledgeDocument[ PRFSIT$[ _, k_List, rest___]] :=
	Module[ {forms, rw = getOptionalComponent[ {rest}, "rewriting"], kk = Alternatives@@Map[ key, k]},
		forms = Join[ Join@@rw[[All, 2]],
					Join@@Map[
						With[ {r = Cases[ {rest}, ((Rule|RuleDelayed)[ #, l_List]) :> l, {1}, 1]},
							If[ r === {},
								r,
								First[ r]
							]
						]&,
						{kbRules, goalRules, substRules, defRules}
					]
				];
		forms = DeleteCases[ DeleteDuplicates[ DeleteCases[ Map[ extractFormulaFromRule, forms], Null], (key[ #1] === key[ #2] &)], FML$[ kk, __]];
		If[ forms === {},
			Null,
			
			NotebookPut[ Notebook[
				Map[ Cell[ BoxData[ theoremaBoxes[ formula[ #]]],
							"FormalTextInputFormula",
							Deployed -> True,
							ShowCellBracket -> False,
							CellFrameLabels -> {{None, makeLabel[ label[ #]]}, {None, None}}
						]&,
						forms
				], 
				StyleDefinitions -> makeColoredStylesheet[ "Notebook"],
				WindowTitle -> translate[ "hiddenKnowledge"]
			]]
		]
	]
	
extractFormulaFromRule[ {_, l_, ___}] := extractFormulaFromRule[ l]
extractFormulaFromRule[ (Rule|RuleDelayed)[ _, r_]] :=
	Module[ {list},
		list = Cases[ Hold[ r], HoldPattern[ Sow[ fml:FML$[ _, _, __], "ref"]] :> fml, Infinity, 1];
		If[ list === {},
			Null,
			First[ list]
		]
	]
	
saveProof[ i_, file_String] :=
	Module[ {po, p = Position[ $TMAproofObject, _PRFSIT$?(id[ #] === i&), {0, Infinity}, 1]},
		po = If[ p === {},
			$TMAproofObject,
			p = First[ p];
			po = Insert[ $TMAproofObject, "Aborted" -> True, Append[ p, -1]]
		];
		Put[ Definition[ $formulaLabel], po, file];
	]

(*
	'getRulesPartitionedFilter[ ps, pr, filter, threshold ]' first retrieves all inference rule from 'ps', then removes
	the ones matching 'filter' or appearing in 'pr', and then partitions the remaining ones into 'n+1' subslists, where 'n' is the length of 'threshold':
	- The first sublist contains the name-tag pairs of all *activated* rules from list 'pr'.
	- The 'i'-th sublist, for 1 < i <= n, contains precisely the *implementations* of the *activated* rules with priority
		between 'threshold[[i-2]]' (inclusive) and 'Min[ threshold[[i-1]], threshold[[n]]]' (exclusive); 'threshold[[0]]' is defined as '0'.
	- The 'n+1'-st sublist contains the *names* of *all* rules with priority >= 'threshold[[n]]'.
*)
getRulesPartitionedFilter[ ps_PRFSIT$, pr_List, filter_, threshold:{___, m_}] := 
	Module[{rules, act, prio, names, partition = {}, pl, pf, prev = 0},
		{rules, act, prio} = ruleSetup@ps;
		pf = Cases[ pr, {r_Symbol, ___} /; TrueQ[ Replace[ r, act]]];
		(* Get name-activation-priority triples of all (active and inactive) rules not in 'filter' and not in 'pf'. *)
		names = Cases[ rules,
						{r_Symbol?(!MemberQ[ pf, {#, ___}]&), True|False, True|False, _Integer, PatternSequence[]|PatternSequence[ Except[ filter], ___]} :>
								{r, Replace[ r, act], Replace[ r, prio]},
						Infinity
				];
		pl = Cases[ names, {r_, _, p_ /; p >= m} :> r];
		names = SortBy[ Cases[ names, {r_, True, p_ /; p < m} :> {r, p}], Last];
		Scan[ (
				AppendTo[ partition, DeleteCases[ Cases[ names, {r_, p_ /; prev <= p && p < #} :> inferenceRule[ r]], _inferenceRule]];
				prev = #
			)&,
			threshold
		];
		Prepend[ Append[ partition, pl], pf]
	]
getRulesPartitionedFilter[ args___] := unexpected[ getRulesPartitionedFilter, {args}]

FISDialogInput[ Notebook[ data_, opts1___?OptionQ], opts2___?OptionQ] :=
	tmaDialogInput[ Notebook[ data], "Dialog", opts2, opts1]

proofsitNB[ i_] :=
	Module[ {psPos, openPS, curPos = Position[ $TMAproofObject, _PRFSIT$?(id[ #] === i &), {0, Infinity}, 1, Heads -> False]}, 
		If[ curPos === {},
			$Failed,
			curPos = First[curPos];
			psPos = positionRelevantSits[ $TMAproofObject];
			If[ Length[ psPos] < 2,
				$Failed, 
				openPS = Extract[ $TMAproofObject, psPos];
				Notebook[
					MapThread[ proofsitButtons[ #1, #2, curPos, #3] &, {openPS, psPos, Array[ Identity, Length[ psPos]]}],
					DockedCells -> Cell[ BoxData[ ToBoxes[
									Row[ { Tooltip[
												Button[ "<<", DialogReturn[ $Canceled], Appearance -> "Frameless"],
												translate[ "ttCancel"]
											], 
											Spacer[ 10], 
											Tooltip[
												Button[ "OK",
													With[ {out = Part[ psPos, Position[ openPS, _?(id[ #] === $selectedProofStep &), {1}, 1, Heads -> False][[1, 1]]]}, 
														If[ out === curPos,
															DialogReturn[ $Canceled],
															DialogReturn[ out]
														]
													],
													Appearance -> "Frameless", ImageSize -> 70
												],
												translate[ "ttOK"]
											]
										}]
									]],
									"Hint",
									Background -> TMAcolor[ 1]
								]
				]
			]
		]
	]

proofsitButtons[ ps_PRFSIT$, p_List, p_List, _Integer] :=
	With[ {i = id@ps},
		Cell[ CellGroupData[ {Cell[ TextData[ {
					Cell[ BoxData[ ToBoxes[ RadioButton[ Dynamic[ $selectedProofStep], i]]]],
			        "  " <> translate[ "curPS"]
				}], "Section", ShowGroupOpener -> False],
				pSitCells[ ps]
				},
				Dynamic[ If[ $selectedProofStep === i, Open, Closed]]
			]
		]
	]
proofsitButtons[ ps_PRFSIT$, p1_List, p2_List, num_Integer] :=
	With[ {l1 = Length[ p1], l2 = Length[ p2], i = id@ps},
		Module[ {common, sym}, 
			If[ l1 >= l2,
				common = Position[  Transpose[ {Take[ p1, l2], p2}], {x_, y_} /; x =!= y, {1}, 1, Heads -> False];
				common = If[ common === {}, p2, Take[ p2, common[[1, 1]] - 1]],
				common = Position[ Transpose[ {p1, Take[ p2, l1]}], {x_, y_} /; x =!= y, {1}, 1, Heads -> False];
				common = If[ common === {}, p1, Take[ p1, common[[1, 1]] - 1]]
			];
			sym = Switch[ Extract[ $TMAproofObject, AppendTo[ common, 0]],
					Theorema`Provers`Common`Private`ANDNODE$,
					"\[And]",
					Theorema`Provers`Common`Private`ORNODE$,
					"\[Or]",
					_,
					"?"
				];
			Cell[ CellGroupData[ {Cell[ TextData[ {
						Cell[ BoxData[ ToBoxes[ RadioButton[ Dynamic[ $selectedProofStep], i]]]],
						"  ", translate[ "open proof situation"],
						" #" <> ToString[ num] <> " (" <> sym <> ")"
					}], "Section", ShowGroupOpener -> False],
					pSitCells[ ps]
					},
					Dynamic[ If[ $selectedProofStep === i, Open, Closed]]
				]
			]
		]
	]
	
getNeighborID[ i_, dir:(Previous|Next), type:(Or|And)] :=
	With[ {t = Switch[ type, Or, Theorema`Provers`Common`Private`ORNODE$, _, Theorema`Provers`Common`Private`ANDNODE$]}, 
		Module[ {pos = Position[ $TMAproofObject, _PRFSIT$?(id[#] === i &), {0, Infinity}, 1, Heads -> False], node, branches, bi, p}, 
			If[ pos === {},
				$Failed,
				pos = First[ pos];
				node = Catch[ While[ pos =!= {},
						bi = Last[ pos];
						pos = Most[ pos];
						With[ {n = Extract[ $TMAproofObject, pos]}, 
							If[ MatchQ[ n, t[ _, __, pending]], 
								branches = Switch[ dir,
											Previous, 
											Reverse[ List@@Rest[ Take[ n, bi - 1]]],
											_, 
											List@@Most[ Drop[ n, bi]]
									];
	          
								p = Position[ branches, _?((proofValue[ #] === pending) &), {1}, 1, Heads -> False];
								If[ p =!= {},
									p = p[[1, 1]];
									Switch[ dir, Previous, p = bi - p, _, p += bi];
									AppendTo[ pos, p];
									Throw[ n[[p]]]
								]
							]
						]
					];
					Throw[ $Failed]
				];
				If[ node === $Failed,
					$Failed,
					(*'pos' is the position of 'node' in the proof object.*)
					Catch[ While[ MatchQ[ node, _Theorema`Provers`Common`Private`ANDNODE$|_Theorema`Provers`Common`Private`ORNODE$], 
							Switch[ dir,
								Previous, 
								p = Position[ List@@Rest[ Most[ node]], _?(proofValue[ #] === pending &), {1}, Heads -> False];
								If[ p === {},
									pos = $Failed;
									Throw[ False],
									p = p[[-1, 1]] + 1
								],
								_, 
								p = Position[ List@@Rest[ Most[ node]], _?(proofValue[ #] === pending &), {1}, 1, Heads -> False];
								If[ p === {},
									pos = $Failed;
									Throw[ False],
									p = p[[1, 1]] + 1
								]
							];
							AppendTo[ pos, p];
							node = node[[p]]
						];
						If[ !MatchQ[ node, _PRFSIT$], pos = $Failed]
					];
					pos
				]
			]
		]
	]

thresholdNB[ threshold_List] :=
	Module[ {t, m, nb},
		If[ MatchQ[ threshold, {__}],
			t = Most[ threshold];
			m = Last[ threshold],
			t = {};
			m = 5
		];
		nb = {
			Button[ translate[ "RestoreDefaults"], (m = Last[ $defaultThresholds]; t = Most[ $defaultThresholds])],
			Text[ Style[ translate[ "thresholdInter"], Bold]],
			InputField[ Dynamic[ m], Expression, FieldSize -> Small],
			
			Text[ Style[ translate[ "thresholdsAuto"], Bold]],
			InputField[ Dynamic[ t], Expression, FieldSize -> Small]
		};
		
		Notebook[ Map[ Cell[ BoxData[ ToBoxes[ #]], Selectable -> False, ShowStringCharacters -> False]&, nb],
			DockedCells -> Cell[ BoxData[ ToBoxes[ Row[ {
								Tooltip[ Button[ "<<", DialogReturn[ $Canceled], Appearance -> "Frameless"], translate[ "ttCancel"]],
								Spacer[ 10],
								Tooltip[ Button[ "OK",
											If[ t === Null, t = {}];
											If[ MatchQ[ m, _Integer?NonNegative] && MatchQ[ t, {___Integer?NonNegative}],
												DialogReturn[ Append[ t, m]]
											],
											Appearance -> "Frameless", ImageSize -> 70
										], translate[ "ttOK"]]
							}]]],
							"Hint",
							Background -> TMAcolor[ 1]
						]
		]
	]

settingsNB[ PRFSIT$[ _, _List, _String, rest___]] :=
	Module[ {nb, view, opts = Cases[ {rest}, (Rule|RuleDelayed)[ _Symbol, _]], allRules, rsOrig, rs, ra, rp, strat, ruleA, ruleP, 
    		selectInter = Switch[ $interactiveProofSitSel, True|False, $interactiveProofSitSel, _, True],
    		filterInter = Switch[ $interactiveNewProofSitFilter, True|False, $interactiveNewProofSitFilter, _, False]},
    	{rsOrig, ra, rp, strat} = Replace[ {rules, ruleActivity, rulePriority, strategy} /. 
      						opts, {(rules|ruleActivity|rulePriority|strategy) -> Null}, {1}];
		If[ rsOrig =!= Null && ra =!= Null && rp =!= Null && strat =!= Null,
			rs = rsOrig;
			Scan[ (ruleA[ First[ #]] = Last[ #])&, ra];
			Scan[ (ruleP[ First[ #]] = Last[ #])&, rp];
			nb = {
				Text[ Style[ translate["pRules"], Bold]], 
				Tooltip[ PopupMenu[ Dynamic[ rs], Map[ MapAt[ translate, #, {2}]&, $registeredRuleSets]], 
					Apply[ Function[ x, MessageName[ x, "usage", $TmaLanguage], {HoldFirst}], rs]
				], 
				
				Row[ {Text[ Style[ translate[ "pRulesSetup"], Bold]], Spacer[ 10], 
					Button[ Text[ translate[ "RestoreDefaults"]], setRulesDefaults[ rs, ruleA, ruleP, {}, {}]]}
				], 
				
				Dynamic[ Refresh[
					If[ rs =!= rsOrig, setRulesDefault[ rs, ruleA, ruleP, ra, rp]];
					{view, allRules} = structViewRules[ rs, ruleA, ruleP];
					If[ view === {}, translate[ "noRules"], view], 
					TrackedSymbols :> {rs}]
				],
				
				Text[ Style[ translate[ "pStrat"], Bold]], 
				Tooltip[ PopupMenu[Dynamic[ strat], Map[ MapAt[ translate, #, {2}]&, $registeredStrategies]], 
					With[ {ss = strat}, MessageName[ ss, "usage", $TmaLanguage]]
				], 
				
				Text[ Style[ translate[ "pInteractive"], Bold]], 
				Grid[ {{Checkbox[ Dynamic[ selectInter]], Text[ translate[ "interactiveProofSitSel"]]},
					   {Checkbox[ Dynamic[ filterInter]], Text[ translate[ "interactiveNewProofSitFilter"]]}}, 
					Alignment -> {Left}
				]
			};
			
			Notebook[ Map[ Cell[ BoxData[ ToBoxes[ #]], Selectable -> False, ShowStringCharacters -> False]&, nb],
				DockedCells -> Cell[ BoxData[ ToBoxes[ Row[ {
									Tooltip[ Button[ "<<", DialogReturn[ $Canceled], Appearance -> "Frameless"], translate[ "ttCancel"]],
									Spacer[ 10],
									Tooltip[ Button[ "OK", DialogReturn[
											Join[ {rs}, toActivityPriorityLists[ allRules, ruleA, ruleP], {strat, selectInter, filterInter, rs =!= rsOrig}]
										], Appearance -> "Frameless", ImageSize -> 70], translate[ "ttOK"]]
								}]]],
								"Hint",
								Background -> TMAcolor[ 1]
							]
			],
			
			$Failed
		]
	]

structViewRules[ Hold[ rs_], ruleA_, ruleP_] := structViewRules[ rs, {}, True, ruleA, ruleP]
structViewRules[ {category_String}, ___] := Sequence[]
structViewRules[ {category_String, r__}, tags_, open_, ruleA_, ruleP_] :=
	Module[ {sub, compTags, structControl}, 
		sub = Map[ structViewRules[ #, tags, False, ruleA, ruleP] &, {r}];
		If[ sub === {}, Return[ {{}, {}}]];
		sub = Transpose[ sub];
		compTags = DeleteDuplicates[ Join@@Last[ sub]];
		structControl = "Theorema`Provers`Strategies`Private`$ruleStructState$" <> ToString[ Hash[ category]];
		If[ open && MatchQ[ ToExpression[ structControl], _Symbol], 
			ToExpression[ structControl <> "=True"]
		];
		{OpenerView[ {structViewRules[ category, compTags, False, ruleA, ruleP], Column[ First[ sub]]}, 
				ToExpression[ "Dynamic[" <> structControl <> "]"]
			],
		compTags}
	]
structViewRules[ {r_Symbol, True|False, True|False, _Integer, ___}, _, _, ruleA_, ruleP_] :=
	{
		Style[ Row[ {Row[ {Tooltip[ Checkbox[ Dynamic[ ruleA[ r]], BaselinePosition -> Baseline], 
								translate[ "ruleActive"]
							],
							Spacer[ 5],
							Tooltip[ PopupMenu[ Dynamic[ ruleP[ r]], Table[ i, {i, 1, 100}], BaselinePosition -> Baseline, ImageSize -> {45, 16}], 
									translate[ "rulePriority"]
								]
						}
					], 
					Text[ MessageName[ r, "usage", $TmaLanguage]]
				},
				Spacer[ 7]
			], 
			LineBreakWithin -> False],
		{r}
    }
structViewRules[ category_String, tags_, _, ruleA_, ruleP_] :=
	Row[ {Tooltip[ Checkbox[ Dynamic[
								allTrue[ tags, ruleA], 
								setAll[ tags, ruleA, #]&
							], 
							BaselinePosition -> Baseline
					],
					translate[ "ruleActive"]
			], 
			Text[ translate[ category]]
		},
		Spacer[ 5]
	]

setRulesDefault[ Hold[ rs_Symbol], ruleA_, ruleP_, ra_List, rp_List] :=
	Module[ {list}, 
		list = Cases[ rs, {_Symbol, True|False, True|False, _Integer, ___}, Infinity];
		Scan[ With[ {r = First[ #]}, 
				If[ !MatchQ[ r /. ra, True|False], ruleA[ r] = #[[2]]];
				If[ !MatchQ[ r /. rp, _Integer], ruleP[ r] = #[[4]]]
			]&,
			list
		]
	]

toActivityPriorityLists[ allRules_List, ruleA_, ruleP_] :=
	Transpose[ Map[ {# -> ruleA[ #], # -> ruleP[ #]}&, allRules]]
	
ruleNB[ k_List, sits_List, Hold[ ma_]] :=
	Module[ {menu, out = 1}, 
		If[ sits === {},
			$Failed,
			(*all subproofs are pending*)
			menu = {
				Tooltip[ Toggler[ Dynamic[ ma], {True -> Style[ "\[Or]", Larger, Bold], False -> Style[ "\[Or]", Larger, TMAcolor[ 13]]}], 
						translate[ "ttMakeAlternatives"]
				],

				Tooltip[ Button[ "<<", DialogReturn[ $Canceled], Appearance -> "Frameless"],
						translate[ "ttCancel"]
				],

				Tooltip[ Button[ "OK", DialogReturn[ out], ImageSize -> 70, Appearance -> "Frameless"], 
						translate[ "ttOK"]
				],
				
				Tooltip[ Button[ "<", --out, Enabled -> Dynamic[ out > 1], Appearance -> "Frameless"],
						translate[ "ttGoPrev"]
				],

				Tooltip[ Button[ ">", ++out, Enabled -> Dynamic[ out < Length[ sits]], Appearance -> "Frameless"],
						translate[ "ttGoNext"]
				]
			};

			Notebook[ {Cell[ BoxData[ TabViewBox[
					MapIndexed[
						With[ {i = First[ #2]},
							{i, ToString[ i] -> proofToBoxes[ #, k]}
						]&,
						sits
					],
					Dynamic[ out]
				]]]},
				DockedCells -> Cell[ BoxData[ ToBoxes[ Row[ menu, Spacer[ 10]]]], "Hint", Background -> TMAcolor[ 1]]
			]
		]
	]
	
proofToBoxes[ expr_, k_List] :=
	Module[ {out = proofToBoxes[ expr, pending, k]}, 
		If[ Length[ {out}] > 1, out = {out}];
		out = out //. Cell[ CellGroupData[ {d___}, ___]] :> d;
		If[ Length[ {out}] > 1, out = {out}];
		If[ ListQ[ out],
			out = TagBox[ GridBox[ Map[ List, out], GridBoxAlignment -> {"Columns" -> {{Left}}}], "Column"]
		];
		out
	]
proofToBoxes[ Theorema`Provers`Common`Private`PRFINFO$[ name_, u_, g_, id_String, rest___?OptionQ], pending, _] :=
	proofStepTextId[ id, name, u, g, rest, pending]
proofToBoxes[ Theorema`Provers`Common`Private`PRFINFO$[ _, _, _, _, ___?OptionQ], _, _] := {}
proofToBoxes[ ps_PRFSIT$, _, k_List] := pSitDifferences[ ps, k]
proofToBoxes[ (Theorema`Provers`Common`Private`ANDNODE$|Theorema`Provers`Common`Private`ORNODE$)[ pi_Theorema`Provers`Common`Private`PRFINFO$, subnodes__, pVal_], _, k_List] :=
	Module[ {header, sub = {}},
		header = proofToBoxes[ pi, pVal, k];
		If[ Length[ {subnodes}] === 1,
			sub = {proofToBoxes[ subnodes, pVal, k]},
			sub = Replace[ Prepend[ Riffle[
										MapIndexed[ subProofToBoxes[ pi, #1, #2, k]&, {subnodes}], 
										RowBox[ {}]
									],
									RowBox[ {}]
							], {d___} :> d, {1}
				]
		];
		Sequence@@Join[ header, sub]
	]
proofToBoxes[ Theorema`Provers`Common`Private`TERMINALNODE$[ _, _], _, _] := {}
proofToBoxes[ args___] := unexpected[ proofToBoxes, {args}]

subProofToBoxes[ Theorema`Provers`Common`Private`PRFINFO$[ name_, used_List, gen_List, rest___], node_, pos:{i_}, k_List] :=
	Switch[ proofValue@node,
		proved,
		Theorema`Provers`Private`textCell[ StyleBox[ "\[Checkmark] ", Bold], translate[ "subproof"] <> " \[NumberSign]", i, translate[ "succeeded"]],
		failed, 
		Theorema`Provers`Private`textCell[ StyleBox[ "\[WarningSign] ", Bold], translate[ "subproof"] <> " \[NumberSign]", i, translate[ "failed"]],
		_,
		Join[ subProofHeaderId[ id@node, name, used, gen, rest, pending, pos], {proofToBoxes[ node, pending, k]}]
	]
	
pSitDifferences[ PRFSIT$[ g1_FML$, k1_List, ___], {g2_, k2_List}] :=
	Module[ {gc, ac, lab, open = False, h = Theorema`Provers`Private`textCell[ StyleBox[ translate[ "openPS"], Deployed -> True]]},
		lab = makeLabel[ label@g1];
		gc = {
				Cell[ TextData[ If[ formula@g1 === g2, "", "\[FilledRightTriangle]"]], "Text", Deployed -> True],
				Cell[ BoxData[ selectableExpressionBox[ g1]], "Goal", Editable -> False],
				Cell[ lab, "GoalLabel", Deployed -> True]
			};
		ac = Map[ Function[ k,
						lab = makeLabel[ label@k];
						{
							Cell[ TextData[ If[MemberQ[ k2, formula@k], "", "\[FilledRightTriangle]"]], "Text", Deployed -> True],
							Cell[ BoxData[ selectableExpressionBox[ k]], "Assumption", Editable -> False],
							Cell[ lab, "AssumptionLabel", Deployed -> True]
						}
					],
					k1
				];
		StyleBox[ PaneSelectorBox[ {
			False -> GridBox[ {{OpenerBox[ Dynamic[ open]], h}}, GridBoxAlignment -> {"Columns" -> {{Left}}}, BaselinePosition -> {1, 1}],
			True -> GridBox[ {{OpenerBox[ Dynamic[open]], h},
								{"", GridBox[ Join[ {{Cell[ RowBox[ {}], Deployed -> True],
									Theorema`Provers`Private`textCell[ StyleBox[ translate[ "goalText"], Deployed -> True]],
									Cell[ RowBox[ {}], Deployed -> True]},
									gc,
									{Cell[ RowBox[ {}], Deployed -> True],
									If[ ac === {},
										Theorema`Provers`Private`textCell[ StyleBox[ translate[ "kbNoText"], Deployed -> True]],
										Theorema`Provers`Private`textCell[ StyleBox[ translate[ "kbText"], Deployed -> True]]
									],
									Cell[ RowBox[ {}], Deployed -> True]}},
									ac
								], ColumnAlignments -> Left, Editable -> False]}}, BaselinePosition -> {1, 1}, GridBoxAlignment -> {"Columns" -> {{Left}}},
						Editable -> False]
			},
			Dynamic[open], BaselinePosition -> Baseline, ImageSize -> Automatic, DefaultBaseStyle -> "OpenerView"], Deployed -> False
		]
	]

selectableExpressionBox[ fml_FML$] :=
	With[ {orig = getOptionalComponent[ fml, "origForm"], box = selectableExpressionBox[ formula@fml]},
		If[ orig === {},
			StyleBox[ box, Selectable -> True],
		(*else*)
			TooltipBox[ box, theoremaBoxes[ orig]]
		]
	]
selectableExpressionBox[ expr_] :=
	Module[ {fixmap, findex = 0, varmap, vindex = 0, metamap, mindex = 0, v},
		StyleBox[
			theoremaBoxes[
				expr /.
					{
						fix_FIX$ :> (fixmap[ ToString[ ++findex]] = fix; IFIX$[ findex]),
						var_VAR$ :> (varmap[ ToString[ ++vindex]] = var; IVAR$[ vindex]),
						meta_META$ :> (metamap[ ToString[ ++mindex]] = meta; IMETA$[ mindex])
					}
			] /.
				{
					RowBox[ {"IFIX$", "[", i_String, "]"}] :>
						With[ {fix = fixmap[ i]},
						With[ {fb = ToBoxes[ fix, TheoremaForm]},
							InterpretationBox[ fb, fix]
						]],
					RowBox[ {"IMETA$", "[", i_String, "]"}] :>
						With[ {meta = metamap[ i]},
						With[ {mb = ToBoxes[ meta, TheoremaForm]},
							InterpretationBox[ mb, meta]
						]],
					RowBox[ {"IVAR$", "[", i_String, "]"}] :>
						(
							v = varmap[ i];
							With[ {vb = ToBoxes[ v, TheoremaForm]},
								v = First[ v];
								v = Switch[ v,
									SEQ0$[ _Symbol],
									RowBox[ {dropPrefixSuffix[ SymbolName[ First[ v]]], "..."}],
									
									SEQ1$[ _Symbol],
									RowBox[ {dropPrefixSuffix[ SymbolName[ First[ v]]], ".."}],
									
									_Symbol,
									dropPrefixSuffix[ SymbolName[ v]]
								];
								TagBox[ InterpretationBox @@ {vb, v}, "Boxes"]	(* 'TagBox' is needed, because 'v' is a *box* and not an expression *)
							]
						)
				},
			Selectable -> True
		]
	]

dropPrefixSuffix[ s_String] :=
	With[ {l = StringLength[ s]},
		If[ l > 4 && StringTake[ s, 4] === "VAR$",
			If[ l > 7 && StringTake[ s, -3] === "$TM",
				StringTake[ s, {5, l - 3}],
				StringDrop[ s, 4]
			],
			If[ l > 3 && StringTake[ s, -3] === "$TM",
				StringDrop[ s, -3],
				s
			]
		]
	]

errorText[] := errorText[ translate[ "failure"]]
errorText[ t_] := Text[ t, Background -> LightRed]

makeStatus[ statusText_, "", _List, Hold[ filter_Symbol]] := (filter = 0; statusText)
makeStatus[ _, filterString_String, rules_List, Hold[ filter_Symbol]] :=
	Module[ {patt = StringSplit[ filterString], i = 0, ruleName},
		patt = StringExpression@@Append[ Prepend[
						Riffle[ patt, BlankNullSequence[] ~~ " "],
						Alternatives[ StartOfString, StringExpression[ BlankNullSequence[], " "]]
					], BlankNullSequence[]
				];
		filter = 0;
		Catch[
			Scan[ With[ {name = MessageName[ #, "usage", $TmaLanguage]},
					++i;
					If[ StringMatchQ[ name, patt, IgnoreCase -> True],
						If[ filter > 0,
							filter = 0;
							Throw[ Null],
							filter = i;
							ruleName = name
						]
					]
				]&,
				rules
			]
		];
		Switch[ filter,
			_Integer?Positive,
			Text[ "\[EnterKey]: " <> ruleName, Background -> LightBlue],
			0,
			Text[ "Filter: " <> StringReplace[ filterString, " " -> "\[SpaceIndicator]"]]
		]
	]

rulesToString[ rules_List, l:(_Integer?Positive|Infinity)] :=
	SortBy[ MapIndexed[ With[ {s = MessageName[ #1, "usage", $TmaLanguage], i = First[ #2]},
				RuleDelayed[
					If[ StringLength[ s] <= l,
						s,
						StringTake[ s, l - 1] <> "\[Ellipsis]"
					],
					DialogReturn[ i]
				]
			]&,
			rules
		],
		First
	]

SetAttributes[ updateThreshold, HoldFirst];
updateThreshold[ ps_, threshold_List] :=
	With[ {pos = Position[ ps, (Rule|RuleDelayed)[ "$FullInteractiveStrat$threshold", _], {1}, 1, Heads -> False]},
		If[ pos === {},
			AppendTo[ ps, "$FullInteractiveStrat$threshold" -> threshold],
			ps = ReplacePart[ ps, First[ pos] -> ("$FullInteractiveStrat$threshold" -> threshold)]
		];
	]
	
(*
	Attention! 'createNode' heavily depends on the representation of 'PRFSIT$' in a particular way.
	If this changes, 'createNode' does not yield correct results any longer.
*)
createNode[ ps_, psOrig_, alternatives_] :=
	createNode[ Theorema`Provers`$FullInteractiveStrat$voidStep, ps, psOrig, alternatives]
createNode[ _, ps_PRFSIT$, psOrig_PRFSIT$, True] :=
	Module[ {i = id@ps, p = ps}, 
		If[ i === id@psOrig,
			i = ToString[ Unique[ "PRFSIT$"]];
			p[[3]] = i
		];
		$lastChoice = i;
		makeORNODE[ makePRFINFO[ name -> proofAlternatives, used -> used@p, generated -> generated@p], {p, psOrig}]
	]
createNode[ _, node:(_Theorema`Provers`Common`Private`ANDNODE$|_Theorema`Provers`Common`Private`ORNODE$|_Theorema`Provers`Common`Private`TERMINALNODE$), psOrig_PRFSIT$, True] :=
	(
		$lastChoice = id@node;
		makeORNODE[ makePRFINFO[ name -> proofAlternatives, used -> used@node, generated -> generated@node], {node, psOrig}]
	)
createNode[ rule_, ps_PRFSIT$, _PRFSIT$, False] :=
	makeANDNODE[ makePRFINFO[name -> rule, used -> {}, generated -> {}], ps]
createNode[ _, node:(_Theorema`Provers`Common`Private`ANDNODE$|_Theorema`Provers`Common`Private`ORNODE$|_Theorema`Provers`Common`Private`TERMINALNODE$), _PRFSIT$, False] :=
	node

	
registerStrategy[ "Full-Interactive Strategy", fullInteractiveStrategy]

End[]

EndPackage[]