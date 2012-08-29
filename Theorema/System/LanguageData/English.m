(* Mathematica package *)

With[ {lang = "English"},
(* System Messages *)
	MessageName[Theorema, "unexpectedArgs", lang] = "Function `1` called with unexpected arguments `2`.";
	MessageName[Theorema, "missingTranslation", lang] = "Missing translation for string `1` into language `2`.";

(* Theorema`System`Utilities` *)
	MessageName[unexpected, "usage", lang] = "unexpected[ f, {args}] terminates the evaluation of f[args] due to unexpected/invalid arguments.";
	MessageName[replaceAllExcept, "usage", lang] = "replaceAllExcept[ expr, rules, expt] applies rule(s) to all subparts of 'expr' except those contained in the list 'expt'.";
	MessageName[joinHold, "usage", lang] = "joinHold[Hold[a],Hold[b]] produces Hold[a,b].";
	MessageName[applyHold, "usage", lang] = "applyHold[Hold[a],Hold[b]] produces Hold[a[b]].";
	MessageName[joinKB, "usage", lang] = "joinKB[ kb1_List, kb2_List] joins the two knowledge bases and deletes duplicate entries.";
	MessageName[notification, "usage", lang] = "notification[text] displays 'text' as a user notification.";

(* Theorema`Language`Syntax` *)
	MessageName[theoremaDisplay, "usage", lang] = "theoremaDisplay[expr] displays expr in Theorema syntax using the definitions for MakeBoxes[ expr, TheoremaForm].";	
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

(* Theorema`Language`FormulaManipulation` *)
	MessageName[freeVariables, "usage", lang] = "";	
	MessageName[variables, "usage", lang] = "";	
	MessageName[specifiedVariables, "usage", lang] = "";
	MessageName[splitAnd, "usage", lang] = "";	
	MessageName[makeConjunction, "usage", lang] = "";	
	MessageName[makeDisjunction, "usage", lang] = "";	
	MessageName[substituteFree, "usage", lang] = "";	
	MessageName[transferToComputation, "usage", lang] = "";	
	MessageName[FML$, "usage", lang] = "FML$[ key, form, lab] represents a Theorema formula including its key and label.";
	MessageName[makeFML, "usage", lang] = "makeFML[ fmldata] is the constructor for the FML$ datastructure.";
	MessageName[key, "usage", lang] = "key is an option for the formula constructor makeFML and a selector for the FML$ datastructure.";
	MessageName[formula, "usage", lang] = "formula is an option for the formula constructor makeFML and a selector for the FML$ datastructure.";
	MessageName[label, "usage", lang] = "label is an option for the formula constructor makeFML and a selector for the FML$ datastructure.";
	MessageName[id, "usage", lang] = "id is an option for the constructors makePRFINFO/makePRFSIT and a selector for the FML$/PRFINFO$/PRFSIT$ datastructures.";
	MessageName[source, "usage", lang] = "source is a selector for the FML$ datastructure.";
	MessageName[initFormulaLabel, "usage", lang] = "initFormulaLabel[ ] initializes the formula labels used in a proof.";
	MessageName[formulaReference, "usage", lang] = "formulaReference[ fml] gives a hyperlink to the formula.";

(* Theorema`Computation`Language` *)
	MessageName[setComputationContext, "usage", lang] = "setComputationContext[ c] sets the context for the next computation to c.";
	MessageName[cleanupComputation, "usage", lang] = "cleanupComputation[ ] removes all user defined function from computation context.";
	
(* Theorema`Interface`GUI` *)
	MessageName[$kbStruct, "usage", lang] = "Structured knowledge base to be displayed in the KB browser";
	MessageName[updateKBBrowser, "usage", lang] = "";
	MessageName[displayKBBrowser, "usage", lang] = "";
	MessageName[$initLabel, "usage", lang] = "Initial label of each formula. Serves as a hint for user to provide system with her own label.";
	MessageName[$labelSeparator, "usage", lang] = "Separator between different labels assigned to one formula.";
	MessageName[$cellTagKeySeparator, "usage", lang] = "Separator between key and value in a cellTag.";
	MessageName[printComputationInfo, "usage", lang] = "Print info about global knowledge used inside a computation";
	
(* Theorema`Interface`Language` *)
	MessageName[translate, "usage", lang] = "translate[s_String,lang_String] gives string s in language lang.";
	MessageName[availableLanguages, "usage", lang] = "availableLanguages[] gives all available languages.";

(* Theorema`Provers` *)
	MessageName[ proofStepText, "usage", lang] = "proofStepText[ stepID_, lang_, data___] generates the cell expression explaining the proof step stepID in language lang.";
	MessageName[ subProofHeader, "usage", lang] = "subProofHeader[ name_, lang_, pos_] generates the cell expression used as header for the subproof at position pos.";

(* Theorema`Provers`Common` *)
	MessageName[callProver, "usage", lang] = "callProver[ prover_, goal_, kb_] calls prover with goal and kb, returns a proof value and proof object.";
	MessageName[displayProof, "usage", lang] = "displayProof[ proofObject_] displays proofObject.";
	MessageName[$TMAproofObject, "usage", lang] = "$TMAproofObject is the global proof object.";
	MessageName[$TMAproofTree, "usage", lang] = "$TMAproofTree is the global proof tree for visualization.";
	MessageName[showProofNavigation, "usage", lang] = "showProofNavigation[ proofObject_] shows a tree navigation through a proof.";
	MessageName[$registeredRuleSets, "usage", lang] = "$registeredRuleSets is a list of available provers in the Theorema system.";
	MessageName[$registeredStrategies, "usage", lang] = "$registeredStrategies is a list of available strategies in the Theorema system.";
	MessageName[registerRuleSet, "usage", lang] = "registerRuleSet[ n_, p_, r_] registers prover p under the name n consisting of rules r.";
	MessageName[registerStrategy, "usage", lang] = "registerStrategy[ n_, s_] registers strategy s under the name n.";
	MessageName[makeANDNODE, "usage", lang] = "makeANDNODE[ info_, {subgoals_}] constructs a node in the proof tree using proofinfo info to prove all the given subgoals.";
	MessageName[makeORNODE, "usage", lang] = "makeORNODE[ info_, {subgoals_}] constructs a node in the proof tree using proofinfo info to prove at least one of the given subgoals.";
	MessageName[makePRFINFO, "usage", lang] = "makePRFINFO[ ...] constructor for PRFINFO$ data staructure.";
	MessageName[name, "usage", lang] = "name is an option for the constructor makePRFINFO and a selector for the PRFINFO$ datastructure.";
	MessageName[used, "usage", lang] = "used is an option for the constructor makePRFINFO and a selector for the PRFINFO$ datastructure.";
	MessageName[generated, "usage", lang] = "generated is an option for the constructor makePRFINFO and a selector for the PRFINFO$ datastructure.";
	MessageName[makePRFSIT, "usage", lang] = "makePRFSIT[ ...] constructor for PRFSIT$ data staructure.";
	MessageName[goal, "usage", lang] = "goal is an option for the constructor makePRFSIT and a selector for the PRFSIT$ datastructure.";
	MessageName[kb, "usage", lang] = "kb is an option for the constructor makePRFSIT and a selector for the PRFSIT$ datastructure.";
	MessageName[facts, "usage", lang] = "facts is an option for the constructor makePRFSIT and a selector for the PRFSIT$ datastructure.";
	MessageName[renewID, "usage", lang] = "renewID[ node] assigns a new and unique ID to node.";
	MessageName[proofFails, "usage", lang] = "proofFails[ ...] .";
	MessageName[proofSucceeds, "usage", lang] = "proofSucceeds[ ...] .";
	MessageName[proofDisproved, "usage", lang] = "proofDisproved[ ...] .";
	MessageName[getActiveRules, "usage", lang] = "getActiveRules[ ...] .";
	MessageName[ PRFOBJ$, "usage", lang] = "PRFOBJ$[ ...] represents a Theorema proof object.";
	MessageName[ PRFSIT$, "usage", lang] = "PRFSIT$[ ...] represents a Theorema proof situation.";
	MessageName[ inferenceRule, "usage", lang] = "inferenceRule[ name] stores the inference rule named name.";
	MessageName[ proofStatusIndicator, "usage", lang] = "proofStatusIndicator[ status] gives a graphical indication of the proof status.";

]
