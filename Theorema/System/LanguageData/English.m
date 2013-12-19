(* ::Package:: *)

(* Mathematica package *)

With[ {lang = "English"},
(* System Messages *)
	MessageName[Theorema, "unexpectedArgs", lang] = "Function `1` called with unexpected arguments `2`.";
	MessageName[Theorema, "missingTranslation", lang] = "Missing translation for string `1` into language `2`.";

(* Theorema`System`Utilities` *)
	MessageName[unexpected, "usage", lang] = "unexpected[ f, {args}] terminates the evaluation of f[args] due to unexpected/invalid arguments.";
	MessageName[replaceAllExcept, "usage", lang] = "replaceAllExcept[ expr, rules, expt] applies rule(s) to all subparts of 'expr' except those contained in the list 'expt'.";
	MessageName[replaceRepeatedExcept, "usage", lang] = "replaceRepeatedExcept[ expr, rules, expt] applies rule(s) repeatedly to all subparts of 'expr' except those contained in the list 'expt'.";
	MessageName[joinHold, "usage", lang] = "joinHold[Hold[a],Hold[b]] produces Hold[a,b].";
	MessageName[applyHold, "usage", lang] = "applyHold[Hold[a],Hold[b]] produces Hold[a[b]].";
	MessageName[notification, "usage", lang] = "notification[text] displays 'text' as a user notification.";
	MessageName[getOptionalComponent, "usage", lang] = "getOptionalComponent[ ds, key] is a generic accessor function for optional components in a datastructure.";

(* Theorema`Language`Syntax` *)
	MessageName[theoremaDisplay, "usage", lang] = "theoremaDisplay[expr] displays expr in Theorema syntax using the definitions for MakeBoxes[ expr, TheoremaForm].";	
	MessageName[theoremaBoxes, "usage", lang] = "theoremaBoxes[expr] generates boxes for expr in Theorema syntax using the definitions for MakeBoxes[ expr, TheoremaForm].";	
	MessageName[isQuantifierFormula, "usage", lang] = "isQuantifierFormula[ e] is true iff e is built up by a logical quantifier.";	
	MessageName[isConnectiveFormula, "usage", lang] = "isConnectiveFormula[ e] is true iff e is built up by a logical connective.";	
	MessageName[isAtomicExpression, "usage", lang] = "isAtomicExpression[ e] is true iff e is neither a quantifier nor a connective formula.";	
	MessageName[makeSet, "usage", lang] = "makeSet[s] constructs a set from s during the phase of parsing an expression.";	
	MessageName[makeTuple, "usage", lang] = "makeTuple[t] constructs a tuple from t during the phase of parsing an expression.";	
	MessageName[$parseTheoremaExpressions, "usage", lang] = "whether to parse expressions with their Theorema meaning ...";
	MessageName[$parseTheoremaGlobals, "usage", lang] = "whether to parse expressions with their Theorema meaning in a global declaration ...";

(* Theorema`Language`Session` *)
	MessageName[$TheoremaArchives, "usage", lang] = "List of currently loaded Theorema archives.";
	MessageName[$tmaEnv, "usage", lang] = "Collection of environments evaluated in the current session, i.e. the knowledge base.";
	MessageName[$tmaArch, "usage", lang] = "Collection of environments evaluated in the current archive.";
	MessageName[$tmaArchTree, "usage", lang] = "Tree representation of the archive used in the commander.";
	MessageName[$tmaArchNeeds, "usage", lang] = "The list of subarchives needed by current archive.";
	MessageName[$formulaCounterName,"usage", lang] = "Name of formulaCounter in the notebook options in CounterAssignments parameter.";
	MessageName[cellIDLabel, "usage", lang] = "cellIDLabel[cellID_Integer] returns string label for the given integer CellID value.";
	MessageName[getCellIDLabel, "usage", lang] = "getCellIDLabel[ cellTags] finds the cellID label in cellTags.";
	MessageName[getCleanCellTags,"usage", lang] = "getCleanCellTags[cellTags] returns all CellTags except tags used as cell/formula keys in cell/formula identification.";
	MessageName[getKeyTags,"usage", lang] = "getKeyTags[cellTags] returns all CellTags used as cell/formula keys in cell/formula identification.";
	MessageName[cellTagsToString,"usage", lang] = "cellTagsToString[cellTags] converts a list of cell tags into a single string.";
	MessageName[makeLabel,"usage", lang] = "makeLabel[s] formats a string as a formula label.";
	MessageName[inArchive,"usage",lang] = "inArchive[] returns True when we are currently processing an archive.";
	MessageName[archiveName,"usage",lang] = "archiveName[f] returns the short archive name (=context name) for an archive stored in file \*StyleBox[\"f\", \"TI\"].";
	MessageName[loadArchive, "usage", lang] = "loadArchive[name] loads the specified archive into the current session.";
	MessageName[processEnvironment, "usage", lang] = "processEnvironment[ expr] ...";
	MessageName[processComputation, "usage", lang] = "processComputation[ expr] ...";
	MessageName[findSelectedFormula, "usage", lang] = "findSelectedFormula[ sel] ...";
	MessageName[kbSelectProve, "usage", lang] = "kbSelectProve[ f] indicates whether the formula labeled f should go into the KB for a proof.";
	MessageName[kbSelectCompute, "usage", lang] = "kbSelectCompute[ f] indicates whether the formula labeled f should be used in a computation.";
	MessageName[kbSelectSolve, "usage", lang] = "kbSelectCompute[ f] indicates whether the formula labeled f should go into the KB for solve.";
	MessageName[makeTmaExpression, "usage", lang] = "makeTmaExpression[ e] turns e into an expression in Theorema language.";
	MessageName[computeInProof, "usage", lang] = "computeInProof[expr] computes expr within a proof.";

(* Theorema`Language`FormulaManipulation` *)
	MessageName[freeVariables, "usage", lang] = "";	
	MessageName[rngVariables, "usage", lang] = "";	
	MessageName[rngConstants, "usage", lang] = "";	
	MessageName[specifiedVariables, "usage", lang] = "";
	MessageName[splitAnd, "usage", lang] = "";	
	MessageName[makeConjunction, "usage", lang] = "";	
	MessageName[makeDisjunction, "usage", lang] = "";	
	MessageName[simplifiedAnd, "usage", lang] = "";	
	MessageName[simplifiedOr, "usage", lang] = "";	
	MessageName[simplifiedImplies, "usage", lang] = "";	
	MessageName[simplifiedForall, "usage", lang] = "";	
	MessageName[thinnedExpression, "usage", lang] = "";
	(* We need "markVariables" in Computation/Language for the local version of "Let" *)
	MessageName[markVariables, "usage", lang] = "";	
	MessageName[substituteFree, "usage", lang] = "";	
	MessageName[isSequenceFree, "usage", lang] = "";
	MessageName[isQuantifierFree, "usage", lang] = "";	
	MessageName[isLogQuantifierFree, "usage", lang] = "";	
	MessageName[isVariableFree, "usage", lang] = "";
	MessageName[isGround, "usage", lang] = "";
	MessageName[getDefInstances, "usage", lang] = "";	
	MessageName[checkAllConds, "usage", lang] = "";	
	MessageName[transferToComputation, "usage", lang] = "";	
	MessageName[formulaListToRules, "usage", lang] = "";	
	MessageName[formulaToRules, "usage", lang] = "";	
	MessageName[replaceAndTrack, "usage", lang] = "";	
	MessageName[replaceListAndTrack, "usage", lang] = "";	
	MessageName[replaceAllAndTrack, "usage", lang] = "";	
	MessageName[replaceRepeatedAndTrack, "usage", lang] = "";	
	MessageName[filterRules, "usage", lang] = "";	
	MessageName[FML$, "usage", lang] = "FML$[ key, form, lab, opt] represents a Theorema formula including its key, label, and optional components.";
	MessageName[makeFML, "usage", lang] = "makeFML[ fmldata] is the constructor for the FML$ datastructure.";
	MessageName[key, "usage", lang] = "key is an option for the formula constructor makeFML and a selector for the FML$ datastructure.";
	MessageName[formula, "usage", lang] = "formula is an option for the formula constructor makeFML and a selector for the FML$ datastructure.";
	MessageName[label, "usage", lang] = "label is an option for the formula constructor makeFML and a selector for the FML$ datastructure.";
	MessageName[simplify, "usage", lang] = "simplify is an option for the formula constructor makeFML deciding whether the constructed formula should be simplified by computation immediately.";
	MessageName[id, "usage", lang] = "id is an option for the constructors makePRFINFO/makePRFSIT/toBeProved and a selector for the FML$/PRFINFO$/PRFSIT$ datastructures.";
	MessageName[source, "usage", lang] = "source is a selector for the FML$ datastructure.";
	MessageName[makeGoalFML, "usage", lang] = "makeGoalFML[ fmldata] generates a FML$ with a goal-specific label.";
	MessageName[makeAssumptionFML, "usage", lang] = "makeAssumptionFML[ fmldata] generates a FML$ with an assumption-specific label.";
	MessageName[initFormulaLabel, "usage", lang] = "initFormulaLabel[ ] initializes the formula labels used in a proof.";
	MessageName[formulaReference, "usage", lang] = "formulaReference[ fml] gives a hyperlink to the formula.";
	MessageName[arbitraryButFixed, "usage", lang] = "arbitraryButFixed[ expr, rng] substitutes all free occurrences of variables specified by the range rng in expr by a new constant.";
	MessageName[introduceMeta, "usage", lang] = "introduceMeta[ expr, rng] substitutes all free occurrences of variables specified by the range rng in expr by a fresh meta variable.";
	MessageName[instantiateExistGoalInteractive, "usage", lang] = "instantiateExistGoalInteractive[ expr, rng] substitutes all free occurrences of variables specified by the range rng in expr by a term obtained from a user dialog.";
	MessageName[rngToCondition, "usage", lang] = "rngToCondition[rng] transforms the range specification rng into a list of conditions.";
	MessageName[joinKB, "usage", lang] = "joinKB[ kb1_List, kb2_List] joins the two knowledge bases and deletes duplicate entries. kb1 should be new formulas, kb2 is assumed to be an existing kb without duplicates.";
	MessageName[appendKB, "usage", lang] = "appendKB[ kb_List, fml] appends fml to the knowledge base kb and deletes duplicate entries.";
	MessageName[prependKB, "usage", lang] = "prependKB[ kb_List, fml] prepends fml to the knowledge base kb and deletes duplicate entries.";
	MessageName[appendToKB, "usage", lang] = "appendToKB[ sym, fml] sets sym to the result of appending fml to sym and deleting duplicate entries.";
	MessageName[prependToKB, "usage", lang] = "prependToKB[ sym, fml] sets sym to the result of prepending fml to sym and deleting duplicate entries.";
	MessageName[trimKBforRewriting, "usage", lang] = "trimKBforRewriting[ k] processes the formulas in k and generates rewrite rules from appropriate candidates.";
	
(* Theorema`Computation`Language` *)
	MessageName[setComputationContext, "usage", lang] = "setComputationContext[ c] sets the context for the next computation to c.";
	MessageName[cleanupComputation, "usage", lang] = "cleanupComputation[ ] removes all user defined function from computation context.";
	MessageName[buiActComputation, "usage", lang] = "buiActComputation[ f] indicates whether the builtin f is active during computation.";
	MessageName[buiActProve, "usage", lang] = "buiActProve[ f] indicates whether the builtin f is active in a computation done during proving.";
	MessageName[buiActSolve, "usage", lang] = "buiActSolve[ f] indicates whether the builtin f is active in a computation done during solving.";
	
(* Theorema`Interface`GUI` *)
	MessageName[$kbStruct, "usage", lang] = "Structured knowledge base to be displayed in the KB browser";
	MessageName[updateKBBrowser, "usage", lang] = "";
	MessageName[displayKBBrowser, "usage", lang] = "";
	MessageName[$initLabel, "usage", lang] = "Initial label of each formula. Serves as a hint for user to provide system with her own label.";
	MessageName[$labelSeparator, "usage", lang] = "Separator between different labels assigned to one formula.";
	MessageName[$cellTagKeySeparator, "usage", lang] = "Separator between key and value in a cellTag.";
	MessageName[printComputationInfo, "usage", lang] = "Print info about global knowledge used inside a computation";
	MessageName[makeColoredStylesheet, "usage", lang] = "Generate a colored stylesheet from a template using the color scheme chosen in the preferences.";
	MessageName[tmaNotebookPut, "usage", lang] = "Theorema version of Mathematica's NotebookPut.";
	MessageName[tmaDialogInput, "usage", lang] = "Theorema version of Mathematica's DialogInput.";
	MessageName[getExistGoalInstanceDialog, "usage", lang] = "The dialog window asking for an instantiation.";
	MessageName[nextProofSitDialog, "usage", lang] = "The dialog window for choosing the next proof situation.";
	
(* Theorema`Interface`Language` *)
	MessageName[translate, "usage", lang] = "translate[s_String,lang_String] gives string s in language lang.";
	MessageName[availableLanguages, "usage", lang] = "availableLanguages[] gives all available languages.";

(* Theorema`Provers` *)
	MessageName[proofStepTextId, "usage", lang] = "proofStepTextId[ stepID_, lang_, data___] generates the cell expression explaining the proof step stepID in language lang.";
	MessageName[subProofHeaderId, "usage", lang] = "subProofHeaderId[ name_, lang_, pos_] generates the cell expression used as header for the subproof at position pos.";

(* Theorema`Provers`Common` *)
	MessageName[callProver, "usage", lang] = "callProver[ prover_, goal_, kb_] calls prover with goal and kb, returns a proof value, a proof object, and the time elapsed.";
	MessageName[simplifyProof, "usage", lang] = "simplifyProof[ proof_, {branches_, steps_, formulae_}] simplifies 'proof' according to the specified settings.";
	MessageName[displayProof, "usage", lang] = "displayProof[ proofObject_] displays proofObject.";
	MessageName[$TMAproofObject, "usage", lang] = "$TMAproofObject is the global proof object.";
	MessageName[$TMAproofTree, "usage", lang] = "$TMAproofTree is the global proof tree for visualization.";
	MessageName[$TMAproofSearchRunning, "usage", lang] = "$TMAproofSearchRunning indicates (by True/False) whether a proof search is currently running.";
	MessageName[showProofNavigation, "usage", lang] = "showProofNavigation[ proofObject_] shows a tree navigation through a proof.";
	MessageName[$registeredRuleSets, "usage", lang] = "$registeredRuleSets is a list of available provers in the Theorema system.";
	MessageName[$registeredStrategies, "usage", lang] = "$registeredStrategies is a list of available strategies in the Theorema system.";
	MessageName[registerRuleSet, "usage", lang] = "registerRuleSet[ n_, p_, r_] registers prover p under the name n consisting of rules r.";
	MessageName[registerStrategy, "usage", lang] = "registerStrategy[ n_, s_] registers strategy s under the name n.";
	MessageName[makeANDNODE, "usage", lang] = "makeANDNODE[ info_, {branches_}] constructs a node in the proof tree using proofinfo info to prove all the given branches.";
	MessageName[makeORNODE, "usage", lang] = "makeORNODE[ info_, {branches_}] constructs a node in the proof tree using proofinfo info to prove at least one of the given branches.";
	MessageName[makePRFINFO, "usage", lang] = "makePRFINFO[ ...] constructor for PRFINFO$ data staructure.";
	MessageName[isProofNode, "usage", lang] = "isProofNode[ p] is True iff p is a valid node to be inserted into a proof tree.";
	MessageName[name, "usage", lang] = "name is an option for the constructor makePRFINFO and a selector for the PRFINFO$ datastructure.";
	MessageName[used, "usage", lang] = "used is an option for the constructor makePRFINFO and a selector for the PRFINFO$ datastructure.";
	MessageName[generated, "usage", lang] = "generated is an option for the constructor makePRFINFO and a selector for the PRFINFO$ datastructure.";
	MessageName[makePRFSIT, "usage", lang] = "makePRFSIT[ ...] constructor for PRFSIT$ data staructure.";
	MessageName[toBeProved, "usage", lang] = "toBeProved[ ...] constructs a new proof situation and checks for proof success immediately.";
	MessageName[$TMAcheckSuccess, "usage", lang] = "$TMAcheckSuccess decides whether proof success is automatically checked when a new subgoal is constructed.";
	MessageName[type, "usage", lang] = "type is a selector for proof node datastructures.";
	MessageName[goal, "usage", lang] = "goal is an option for the constructors makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[kb, "usage", lang] = "kb is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[ruleSetup, "usage", lang] = "ruleSetup is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[rules, "usage", lang] = "rules is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[ruleActivity, "usage", lang] = "ruleActivity is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[rulePriority, "usage", lang] = "rulePriority is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[strategy, "usage", lang] = "strategy is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[kbRules, "usage", lang] = "kbRules is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[goalRules, "usage", lang] = "goalRules is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[substRules, "usage", lang] = "substRules is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[defRules, "usage", lang] = "defRules is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[makeTERMINALNODE, "usage", lang] = "makeTERMINALNODE[ info_, v_] constructs a terminal node with info and value v.";
	MessageName[getActiveRulesFilter, "usage", lang] = "getActiveRulesFilter[ ...] .";
	MessageName[getActiveRulesType, "usage", lang] = "getActiveRulesType[ ...] .";
	MessageName[applyAllRules, "usage", lang] = "applyAllRules[ ...] .";
	MessageName[ruleTextActive, "usage", lang] = "Specifies, whether the proof text for the rule will be activated. (ruleTextActive)";
	MessageName[PRFOBJ$, "usage", lang] = "PRFOBJ$[ ...] represents a Theorema proof object.";
	MessageName[PRFSIT$, "usage", lang] = "PRFSIT$[ ...] represents a Theorema proof situation.";
	MessageName[inferenceRule, "usage", lang] = "inferenceRule[ name] stores the inference rule named name.";
	MessageName[proofStatusIndicator, "usage", lang] = "proofStatusIndicator[ status, name] gives a graphical indication of the proof status. If name is given, it is interpreted as the name of a proof rule, and its description is given in a tooltip.";
	MessageName[proved, "usage", lang] = "proved is a possible proof value.";
	MessageName[disproved, "usage", lang] = "disproved is a possible proof value.";
	MessageName[failed, "usage", lang] = "failed is a possible proof value.";
	MessageName[pending, "usage", lang] = "pending is a possible proof value.";
	MessageName[$selectedProofStep, "usage", lang] = "$selectedProofStep refers to the id of the proof step that is selected in the current proof notebook.";
	MessageName[$proofCellStatus, "usage", lang] = "$proofCellStatus determines the status (open/closed) of nested cells in the proof notebook.";
	MessageName[$proofAborted, "usage", lang] = "$proofAborted is a flag that is checked whether the user tried to abort the running proof.";
	MessageName[$currentSearchLevel, "usage", lang] = "$currentSearchLevel gives the search depth level of the last proof step performed.";
	MessageName[$interactiveProofSitSel, "usage", lang] = "$interactiveProofSitSel indicates whether interactive selection of proof situations is activated.";
	MessageName[$interactiveNewProofSitFilter, "usage", lang] = "$interactiveNewProofSitFilter indicates whether interactive filtering of proof situations is activated.";
	MessageName[pSitCells, "usage", lang] = "pSitCells[ ps] generates a cell representation of the proof situation ps to be rendered in a notebook.";
	MessageName[pObjCells, "usage", lang] = "pObjCells[ po] generates a cell representation of the proof object po (default: $TMAproofObject) to be rendered in a notebook.";
	MessageName[$rewriteRules, "usage", lang] = "is a global variable used to accumulate newly generated rewrite rules corresponding to formulas in the KB.";
	MessageName[$generated, "usage", lang] = "is a global variable used to accumulate newly generated rewrite rules corresponding to formulas in the KB.";
	MessageName[$autoGenerateRules, "usage", lang] = "is a global switch to turn on/off automatic generation of rewrite rules when new formulas go into the KB.";
	MessageName[performProofStep, "usage", lang] = "performProofStep[ prog_] is a wrapper to be used on the rhs of an inference rule, where prog is the actual program that performs the step.";

]
