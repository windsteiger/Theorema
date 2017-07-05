(* Theorema 
    Copyright (C) 1995-2014 The Theorema Group

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

(*
   *********************************************************************************************
   -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- 
   *********************************************************************************************
 
     If you modify this file, then insert the new translation in correct alphabetical 
     order (case-insensitive).

     ALSO, YOU MUST add a corresponding entry for each other language, either
      1) in the section named "UNTRANSLATED" at the end of the language file 
         (in case you cannot or do not want to provide a translation) or
      2) in correct alphabetical order (case-insensitive) in case you immediately provide 
         a translation.
      
   *********************************************************************************************
   -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- 
   *********************************************************************************************
 *)
 
With[ {lang = "English"},
	
	MessageName[ addKnowledgeWhileProving, "usage", lang] = "addKnowledgeWhileProving[ new_List] adds all formulas in new to the list of formulas to be written in the proof info/file of the current proof.";
	MessageName[ allTmaNotebooks, "usage", lang] = "allTmaNotebooks[] returns a list of all Theorema Notebooks in the current session.";
	MessageName[ allTrue, "usage", lang] = "allTrue[ l, f] checks whether f always yields True when applied to the elements of list l.";
	MessageName[ alphaEquivalent, "usage", lang] = "alphaEquivalent[ a, b] checks whether 'a' and 'b' are \[Alpha]-equivalent to each other.";
	MessageName[ analyzeVars, "usage", lang] = "analyzeVars[ expr] analyzes the occurrences of all variables appearing in 'expr' (free and bound).";
	MessageName[ appendKB, "usage", lang] = "appendKB[ kb_List, fml] appends fml to the knowledge base kb and deletes duplicate entries.";
	MessageName[ appendToKB, "usage", lang] = "appendToKB[ sym, fml] sets sym to the result of appending fml to sym and deleting duplicate entries.";
	MessageName[ $applyAllPossibleInferences, lang, "usage"] = "Indicates whether inference rules should be applied in all possible ways or not in an interactive proof.";
	MessageName[ applyAllRules, "usage", lang] = "applyAllRules[ ...] .";
	MessageName[ applyHold, "usage", lang] = "applyHold[Hold[a],Hold[b]] produces Hold[a[b]].";
	MessageName[ arbitraryButFixed, "usage", lang] = "arbitraryButFixed[ expr, rng] substitutes all free occurrences of variables specified by the range rng in expr by a new constant.";
	MessageName[ archiveName,"usage",lang] = "archiveName[f] returns the short archive name (=context name) for an archive stored in file \*StyleBox[\"f\", \"TI\"].";
	MessageName[ $autoGenerateRules, "usage", lang] = "is a global switch to turn on/off automatic generation of rewrite rules when new formulas go into the KB.";
	MessageName[ availableLanguages, "usage", lang] = "availableLanguages[] gives all available languages.";

	MessageName[ boundVariables, "usage", lang] = "";
	MessageName[ buiActComputation, "usage", lang] = "buiActComputation[ f] indicates whether the builtin f is active during computation.";
	MessageName[ buiActProve, "usage", lang] = "buiActProve[ f] indicates whether the builtin f is active in a computation done during proving.";
	MessageName[ buiActSolve, "usage", lang] = "buiActSolve[ f] indicates whether the builtin f is active in a computation done during solving.";

	MessageName[ callProver, "usage", lang] = "callProver[ prover_, goal_, kb_] calls prover with goal and kb, returns a proof value, a proof object, and the time elapsed.";
	MessageName[ cellIDLabel, "usage", lang] = "cellIDLabel[cellID_Integer] returns string label for the given integer CellID value.";
	MessageName[ cellPosition, "usage", lang] = "cellPosition is an option for the formula constructor, specifying the position of the respective cell in the notebook (or Null if unknown).";
	MessageName[ $cellTagKeySeparator, "usage", lang] = "Separator between key and value in a cellTag.";
	MessageName[ cellTagsToString,"usage", lang] = "cellTagsToString[cellTags] converts a list of cell tags into a single string.";
	MessageName[ checkAllConds, "usage", lang] = "";
	MessageName[ cleanupComputation, "usage", lang] = "cleanupComputation[ ] removes all user defined function from computation context.";
	MessageName[ $codeEpilog, "usage", lang] = "$codeEpilog is evaluated after evaluating Theorema code cells.";
	MessageName[ $codeProlog, "usage", lang] = "$codeProlog is evaluated before evaluating Theorema code cells.";
	MessageName[ commutative, "usage", lang] = "";
	MessageName[ computeInProof, "usage", lang] = "computeInProof[expr] computes expr within a proof.";
	MessageName[ createNbRememberLocation, "usage", lang] = "createNbRememberLocation[] creates a new notebook and stores the location for the next notebook operation.";
	MessageName[ createPerNotebookDirectory, "usage", lang] = "createPerNotebookDirectory[ file] creates a cache directory for the notebook file.";
	MessageName[ $currentSearchLevel, "usage", lang] = "$currentSearchLevel gives the search depth level of the last proof step performed.";

	MessageName[ defaultFmlPre, "usage", lang] = "defaultFmlPre is the default pre-processing function for formulas.";
	MessageName[ defRules, "usage", lang] = "defRules is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[ displayComputation, "usage", lang] = "displayComputation[ ...] displays the computation represented by the global computation object ....";
	MessageName[ displayGlobalDeclarations, "usage", lang] = "displayGlobalDeclarations[ nb] ...";
	MessageName[ displayKBBrowser, "usage", lang] = "";
	MessageName[ displayProof, "usage", lang] = "displayProof[ proofObject_] displays proofObject.";
	MessageName[ disproved, "usage", lang] = "disproved is a possible proof value.";

	MessageName[ ensureNotebookIntegrity, "usage", lang] = "ensureNotebookIntegrity[ file] runs some consistency checks on the notebook file.";

	MessageName[ failed, "usage", lang] = "failed is a possible proof value.";
	MessageName[ filterRules, "usage", lang] = "";	
	MessageName[ findSelectedFormula, "usage", lang] = "findSelectedFormula[ sel] ...";
	MessageName[ FML$, "usage", lang] = "FML$[ key, form, lab, opt] represents a Theorema formula including its key, label, and optional components.";
	MessageName[ $formulaCounterName,"usage", lang] = "Name of formulaCounter in the notebook options in CounterAssignments parameter.";
	MessageName[ $formulaLabel, "usage", lang] = "Internal counter for automatically-generated formula labels in proofs; not to be confused with the counter for formula labels in notebooks!";
	MessageName[ formulaListToRules, "usage", lang] = "";	
	MessageName[ formulaReference, "usage", lang] = "formulaReference[ fml] gives a hyperlink to the formula.";
	MessageName[ formulaTags, "usage", lang] = "formulaTags is an option for the formula constructor, specifying the list of cell tags associated to the cell the formula originates from.";
	MessageName[ formulaToRules, "usage", lang] = "";	
	MessageName[ formula, "usage", lang] = "formula is an option for the formula constructor makeFML and a selector for the FML$ datastructure.";
	MessageName[ freeVariables, "usage", lang] = "freeVariables[ expr] returns all variables appearing free in 'expr'.";
	MessageName[ freshName, "usage", lang] = "freshName[ base, ex] returns either 'base' or a symbol with name 'base~~i' (where 'i' is a non-negative integer), such that the return value is not a member of list 'ex'. If 'base' is a list of symbols, a list of distinct new symbols is generated.";

	MessageName[ generated, "usage", lang] = "generated is an option for the constructor makePRFINFO and a selector for the PRFINFO$ datastructure.";
	MessageName[ $generated, "usage", lang] = "is a global variable used to accumulate newly generated rewrite rules corresponding to formulas in the KB.";
	MessageName[ getActiveRulesFilter, "usage", lang] = "getActiveRulesFilter[ ...] .";
	MessageName[ getActiveRulesType, "usage", lang] = "getActiveRulesType[ ...] .";
	MessageName[ getCellIDFromKey, "usage", lang] = "getCellIDFromKey[ key] extracts the cellID from the formula key.";
	MessageName[ getCellIDLabel, "usage", lang] = "getCellIDLabel[ cellTags] finds the cellID label in cellTags.";
	MessageName[ getCleanCellTags,"usage", lang] = "getCleanCellTags[cellTags] returns all CellTags except tags used as cell/formula keys in cell/formula identification.";
	MessageName[ getDefInstances, "usage", lang] = "";
	MessageName[ getExistGoalInstanceDialog, "usage", lang] = "The dialog window asking for an instantiation.";
	MessageName[ getKeyTags,"usage", lang] = "getKeyTags[cellTags,file] returns all CellTags used as cell/formula keys in cell/formula identification.";
	MessageName[ getOptionalComponent, "usage", lang] = "getOptionalComponent[ ds, key] is a generic accessor function for optional components in a datastructure.";
	MessageName[ getTheoremaCommander, "usage", lang] = "getTheoremaCommander[] returns the Theorema commander notebook.";
	MessageName[ $goalActivated, lang, "usage"] = "Indicates whether the goal of the current proof situation is activated in an interactive proof.";
	MessageName[ goalRules, "usage", lang] = "goalRules is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[ goal, "usage", lang] = "goal is an option for the constructors makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";

	MessageName[ id, "usage", lang] = "id is an option for the constructors makePRFINFO/makePRFSIT/toBeProved and a selector for the FML$/PRFINFO$/PRFSIT$ datastructures.";
	MessageName[ inArchive,"usage",lang] = "inArchive[] returns True when we are currently processing an archive.";
	MessageName[ inEnvironment,"usage",lang] = "inEnvironment[] returns True when we are currently processing an environment.";
	MessageName[ inferenceRule, "usage", lang] = "inferenceRule[ name] stores the inference rule named name.";
	MessageName[ initFormulaLabel, "usage", lang] = "initFormulaLabel[ ] initializes the formula labels used in a proof.";
	MessageName[ $initLabel, "usage", lang] = "Initial label of each formula. Serves as a hint for user to provide system with her own label.";
	MessageName[ $inputEpilog, "usage", lang] = "$inputEpilog is evaluated after evaluating Theorema input cells.";
	MessageName[ $inputProlog, "usage", lang] = "$inputProlog is evaluated before evaluating Theorema input cells.";
	MessageName[ instantiateExistGoalInteractive, "usage", lang] = "instantiateExistGoalInteractive[ expr, rng] substitutes all free occurrences of variables specified by the range rng in expr by a term obtained from a user dialog.";
	MessageName[ instantiateMeta, "usage", lang] = "";
	MessageName[ instantiation, "usage", lang] = "";
	MessageName[ $interactiveNewProofSitFilter, "usage", lang] = "$interactiveNewProofSitFilter indicates whether interactive filtering of proof situations is activated.";
	MessageName[ $interactiveProofSitSel, "usage", lang] = "$interactiveProofSitSel indicates whether interactive selection of proof situations is activated.";
	MessageName[ introduceMeta, "usage", lang] = "introduceMeta[ expr, rng] substitutes all free occurrences of variables specified by the range rng in expr by a fresh meta variable.";
	MessageName[ isAtomicExpression, "usage", lang] = "isAtomicExpression[ e] is true iff e is neither a quantifier nor a connective formula.";	
	MessageName[ isAtomicTerm, "usage", lang] = "isAtomicTerm[ t] is true iff t is a variable or a constant.";	
	MessageName[ isConnectiveFormula, "usage", lang] = "isConnectiveFormula[ e] is true iff e is built up by a logical connective.";	
	MessageName[ isFree, "usage", lang] = "isFree[ var, expr] returns True iff 'var' appears free in 'expr'.";
	MessageName[ isGround, "usage", lang] = "";
	MessageName[ isIndividual, "usage", lang] = "";
	MessageName[ isLiteralExpression, "usage", lang] = "isLiteralExpression[ e] is true iff e is an atomic or a negated atomic expression.";	
	MessageName[ isLogQuantifierFree, "usage", lang] = "";	
	MessageName[ isMathematicalConstant, "usage", lang] = "";
	MessageName[ isNonEmptySequence, "usage", lang] = "";
	MessageName[ isNonNumberAtomicTerm, "usage", lang] = "isAtomicTerm[ t] is true iff t is an atomic term but not a number.";	
	MessageName[ isProofNode, "usage", lang] = "isProofNode[ p] is True iff p is a valid node to be inserted into a proof tree.";
	MessageName[ isQuantifier, "usage", lang] = "isQuantifier[ e] is True iff e is a quantifier (e.g. 'Forall$TM').";
	MessageName[ isQuantifierFormula, "usage", lang] = "isQuantifierFormula[ e] is true iff e is built up by a logical quantifier.";	
	MessageName[ isQuantifierFree, "usage", lang] = "";
	MessageName[ isVariableFree, "usage", lang] = "";
	MessageName[ isVariableRange, "usage", lang] = "isVariableRange[ r] is True iff r is a (built-in or user-defined) variable range, e.g. 'SIMPRNG$'";

	MessageName[ joinHold, "usage", lang] = "joinHold[Hold[a],Hold[b]] produces Hold[a,b].";
	MessageName[ joinKB, "usage", lang] = "joinKB[ kb1_List, kb2_List] joins the two knowledge bases and deletes duplicate entries. kb1 should be new formulas, kb2 is assumed to be an existing kb without duplicates.";

	MessageName[ kbRules, "usage", lang] = "kbRules is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[ kbSelectCompute, "usage", lang] = "kbSelectCompute[ f] indicates whether the formula labeled f should be used in a computation.";
	MessageName[ kbSelectProve, "usage", lang] = "kbSelectProve[ f] indicates whether the formula labeled f should go into the KB for a proof.";
	MessageName[ kbSelectSolve, "usage", lang] = "kbSelectCompute[ f] indicates whether the formula labeled f should go into the KB for solve.";
	MessageName[ $kbStruct, "usage", lang] = "Structured knowledge base to be displayed in the KB browser";
	MessageName[ kb, "usage", lang] = "kb is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[ key, "usage", lang] = "key is an option for the formula constructor makeFML and a selector for the FML$ datastructure.";
	MessageName[ $knowledgeActivated, lang, "usage"] = "List of keys of formulas in the knowledge base of the current proof situation which are activated in an interactive proof.";

	MessageName[ $labelSeparator, "usage", lang] = "Separator between different labels assigned to one formula.";
	MessageName[ label, "usage", lang] = "label is an option for the formula constructor makeFML and a selector for the FML$ datastructure.";
	MessageName[ $lastChoice, "usage", lang] = "The position of the node in the current proof tree the user interactively chose to continue with last.";
	MessageName[ loadArchive, "usage", lang] = "loadArchive[name] loads the specified archive into the current session.";

	MessageName[ makeANDNODE, "usage", lang] = "makeANDNODE[ info_, {branches_}] constructs a node in the proof tree using proofinfo info to prove all the given branches.";
	MessageName[ makeAssumptionFML, "usage", lang] = "makeAssumptionFML[ fmldata] generates a FML$ with an assumption-specific label.";
	MessageName[ makeColoredStylesheet, "usage", lang] = "Generate a colored stylesheet from a template using the color scheme chosen in the preferences.";
	MessageName[ makeConjunction, "usage", lang] = "";	
	MessageName[ makeDisjunction, "usage", lang] = "";	
	MessageName[ makeFML, "usage", lang] = "makeFML[ fmldata] is the constructor for the FML$ datastructure.";
	MessageName[ makeGoalFML, "usage", lang] = "makeGoalFML[ fmldata] generates a FML$ with a goal-specific label.";
	MessageName[ makeLabel,"usage", lang] = "makeLabel[s] formats a string as a formula label.";
	MessageName[ makeORNODE, "usage", lang] = "makeORNODE[ info_, {branches_}] constructs a node in the proof tree using proofinfo info to prove at least one of the given branches.";
	MessageName[ makePRFINFO, "usage", lang] = "makePRFINFO[ ...] constructor for PRFINFO$ data staructure.";
	MessageName[ makePRFSIT, "usage", lang] = "makePRFSIT[ ...] constructor for PRFSIT$ data staructure.";
	MessageName[ makeSet, "usage", lang] = "makeSet is an auxiliary symbol needed to create sets and lists in 'freshNames'. It does not do anything by itself.";
	MessageName[ makeTERMINALNODE, "usage", lang] = "makeTERMINALNODE[ info_, v_] constructs a terminal node with info and value v.";
	MessageName[ makeTmaExpression, "usage", lang] = "makeTmaExpression[ e] turns e into an expression in Theorema language.";
	MessageName[ makeTmaExpressionFromBoxes, "usage", lang] = "makeTmaExpressionFromBoxes[ box] turns box into an expression in Theorema language.";
	MessageName[ markVariables, "usage", lang] = "";	
	MessageName[ matches, "usage", lang] = "";
	MessageName[ maximumUnifiers, "usage", lang] = "";
	MessageName[ maximumWidth, "usage", lang] = "";

	MessageName[ name, "usage", lang] = "name is an option for the constructor makePRFINFO and a selector for the PRFINFO$ datastructure.";
	MessageName[ $nbFileNameCounterName,"usage", lang] = "Name of notebook-filename counter in the notebook options in CounterAssignments parameter.";
	MessageName[ nextProofSitDialog, "usage", lang] = "The dialog window for choosing the next proof situation.";
	MessageName[ notification, "usage", lang] = "notification[text] displays 'text' as a user notification.";

	MessageName[ $omdocExport, "usage", lang] = "$omdocExport tells whether an archive is exported to OmDoc when saved.";
	MessageName[ openNbRememberLocation, "usage", lang] = "openNbRememberLocation[] opens a notebook and stores the location for the next notebook operation.";

	MessageName[ $parseTheoremaExpressions, "usage", lang] = "whether to parse expressions with their Theorema meaning ...";
	MessageName[ $parseTheoremaGlobals, "usage", lang] = "whether to parse expressions with their Theorema meaning in a global declaration ...";
	MessageName[ $parseTheoremaQuoted, "usage", lang] = "whether to parse quoted expressions with their Theorema meaning ...";
	MessageName[ pending, "usage", lang] = "pending is a possible proof value.";
	MessageName[ performProofStep, "usage", lang] = "performProofStep[ prog_] is a wrapper to be used on the rhs of an inference rule, where prog is the actual program that performs the step.";
	MessageName[ pObjCells, "usage", lang] = "pObjCells[ po] generates a cell representation of the proof object po (default: $TMAproofObject) to be rendered in a notebook.";
	MessageName[ positionRelevantSits, "usage", lang] = "positionRelevantSits[ po] returns the positions of all relevant pending proof situations in po.";
	MessageName[ prependKB, "usage", lang] = "prependKB[ kb_List, fml] prepends fml to the knowledge base kb and deletes duplicate entries.";
	MessageName[ prependToKB, "usage", lang] = "prependToKB[ sym, fml] sets sym to the result of prepending fml to sym and deleting duplicate entries.";
	MessageName[ preprocess, "usage", lang] = "preprocess is an option for the formula constructor, specifying the function to be applied to the formula at the very beginning.";
	MessageName[ PRFOBJ$, "usage", lang] = "PRFOBJ$[ ...] represents a Theorema proof object.";
	MessageName[ PRFSIT$, "usage", lang] = "PRFSIT$[ ...] represents a Theorema proof situation.";
	MessageName[ printComputationInfo, "usage", lang] = "Print info about global knowledge used inside a computation";
	MessageName[ processComputation, "usage", lang] = "processComputation[ expr] ...";
	MessageName[ processEnvironment, "usage", lang] = "processEnvironment[ expr] ...";
	MessageName[ $proofAborted, "usage", lang] = "$proofAborted is a flag that is checked whether the user tried to abort the running proof.";
	MessageName[ $proofCellStatus, "usage", lang] = "$proofCellStatus determines the status (open/closed) of nested cells in the proof notebook.";
	MessageName[ proofStatusIndicator, "usage", lang] = "proofStatusIndicator[ status, name] gives a graphical indication of the proof status. If name is given, it is interpreted as the name of a proof rule, and its description is given in a tooltip.";
	MessageName[ proofStepTextId, "usage", lang] = "proofStepTextId[ stepID_, lang_, data___] generates the cell expression explaining the proof step stepID in language lang.";
	MessageName[ proofValue, "usage", lang] = "proofValue[ obj] returns the proof value (i.e. pending, failed or proved) of the given proof-object, -situation or -node.";
	MessageName[ propagateProofValues, "usage", lang] = "propagateProofValues[ node] propagates the proof values of node's successors to node itself, depending on the type of node (ANDNODE, ORNODE).";
	MessageName[ proved, "usage", lang] = "proved is a possible proof value.";
	MessageName[ pSitCells, "usage", lang] = "pSitCells[ ps] generates a cell representation of the proof situation ps to be rendered in a notebook.";

	MessageName[ $registeredRuleSets, "usage", lang] = "$registeredRuleSets is a list of available provers in the Theorema system.";
	MessageName[ $registeredStrategies, "usage", lang] = "$registeredStrategies is a list of available strategies in the Theorema system.";
	MessageName[ registerQuantifier, "usage", lang] = "registerQuantifier is a function used to register a new quantifier for parsing and pretty-printing.";
	MessageName[ registerRange, "usage", lang] = "registerRange is a function used to register a new variable range for parsing and pretty-printing.";
	MessageName[ registerRuleSet, "usage", lang] = "registerRuleSet[ n_, p_, r_] registers prover p under the name n consisting of rules r.";
	MessageName[ registerStrategy, "usage", lang] = "registerStrategy[ n_, s_] registers strategy s under the name n.";
	MessageName[ removeEnvironment,"usage", lang] = "removeEnvironment[ nb] removes an entire environment from the notebook nb.";
	MessageName[ removeRedundantBoxes,"usage", lang] = "removeRedundantBoxes[ expr] removes redundant boxes (e.g. certain TagBoxes) from the given box-expression.";
	MessageName[ renameBound, "usage", lang] = "renameBound[ expr:(_[ _RNG$, ___]), new] renames the variables bound by the outermost quantifier in 'expr' by 'new'. Other bound variables might be renamed as well, in order to avoid name clashes; this is taken care of by 'substituteFree'.";
	MessageName[ replaceAllAndTrack, "usage", lang] = "";	
	MessageName[ replaceAllExcept, "usage", lang] = "replaceAllExcept[ expr, rules, expt] applies rule(s) to all subparts of 'expr' except those contained in the list 'expt'.";
	MessageName[ replaceAndTrack, "usage", lang] = "";	
	MessageName[ replaceListAndTrack, "usage", lang] = "";	
	MessageName[ replaceRepeatedAndTrack, "usage", lang] = "";	
	MessageName[ replaceRepeatedExcept, "usage", lang] = "replaceRepeatedExcept[ expr, rules, expt] applies rule(s) repeatedly to all subparts of 'expr' except those contained in the list 'expt'.";
	MessageName[ resyncGlobals, "usage", lang] = "resyncGlobals[ nb] re-synchronizes globals in notebook nb.";
	MessageName[ $rewriteRules, "usage", lang] = "is a global variable used to accumulate newly generated rewrite rules corresponding to formulas in the KB.";
	MessageName[ rngConstants, "usage", lang] = "";	
	MessageName[ rngToCondition, "usage", lang] = "rngToCondition[rng] transforms the range specification rng into a list of conditions.";
	MessageName[ rngVariables, "usage", lang] = "";	
	MessageName[ ruleActivity, "usage", lang] = "ruleActivity is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[ rulePriority, "usage", lang] = "rulePriority is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[ ruleSetup, "usage", lang] = "ruleSetup is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[ rules, "usage", lang] = "rules is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[ ruleTextActive, "usage", lang] = "Specifies, whether the proof text for the rule will be activated. (ruleTextActive)";

	MessageName[ selectableExpressionBox, "usage", lang] = "";
	MessageName[ $selectedProofStep, "usage", lang] = "$selectedProofStep refers to the id of the proof step that is selected in the current proof notebook.";
	MessageName[ sequenceFlatten, "usage", lang] = "sequenceFlatten[ expr] flattens all SEQ$-expressions appearing in the given expression, keeping only an all-enclosing outermost SEQ$.";
	MessageName[ sequenceType, "usage", lang] = "sequenceType[ expr] returns the type of the given expression in terms of whether it is a sequence of expressions or an individual expression.";
	MessageName[ sequenceTypeEqual, "usage", lang] = "sequenceTypeEqual[ a, b] checks whether 'a' and 'b' have the same (valid) sequence-type.";
	MessageName[ sequenceTypeMatchQ, "usage", lang] = "sequenceTypeMatchQ[ a, b] checks whether the sequence type of 'b' matches the one of 'a'. Typically used for checking whether a variable ('b') can be instantiated by a particular term ('a').";
	MessageName[ setAll, "usage", lang] = "setAll[ l, f, val] sets the value of function f at each element of list l to val.";
	MessageName[ setComputationContext, "usage", lang] = "setComputationContext[ c] sets the context for the next computation to c.";
	MessageName[ setComputationEnvironment, "usage", lang] = "setComputationEnvironment[ f] sets the environment values for sa computation from the values stored in file f.";
	MessageName[ showProofNavigation, "usage", lang] = "showProofNavigation[ proofObject_] shows a tree navigation through a proof.";
	MessageName[ simplifiedAnd, "usage", lang] = "";	
	MessageName[ simplifiedForall, "usage", lang] = "";	
	MessageName[ simplifiedImplies, "usage", lang] = "";	
	MessageName[ simplifiedOr, "usage", lang] = "";	
	MessageName[ simplifiedProofInfo, "usage", lang] = "";	
	MessageName[ simplifyProof, "usage", lang] = "simplifyProof[ proof_, {branches_, steps_, formulae_}] simplifies 'proof' according to the specified settings.";
	MessageName[ simplify, "usage", lang] = "simplify is an option for the formula constructor makeFML deciding whether the constructed formula should be simplified by computation immediately.";
	MessageName[ sourceFile, "usage", lang] = "sourceFile is a selector for the FML$ datastructure.";
	MessageName[ source, "usage", lang] = "source is a selector for the FML$ datastructure.";
	MessageName[ specialBrackets, "usage", lang] = "specialBrackets is a list of special brackets, used for parsing, pretty-printing and creating buttons in the Commander.";
	MessageName[ specifiedVariables, "usage", lang] = "";
	MessageName[ standardFormQuantifier, "usage", lang] = "standardFormQuantifier[ form] merges all leading universal quantifiers in form.";
	MessageName[ strategy, "usage", lang] = "strategy is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";
	MessageName[ subProofHeaderId, "usage", lang] = "subProofHeaderId[ name_, lang_, pos_] generates the cell expression used as header for the subproof at position pos.";
	MessageName[ substituteFree, "usage", lang] = "";	
	MessageName[ substRules, "usage", lang] = "substRules is an option for the constructor makePRFSIT/toBeProved and a selector for the PRFSIT$ datastructure.";

	MessageName[ $tcKBBrowseSelection, "usage", lang] = "$tcKBBrowseSelection[ task] gives the filename of the notebook that should be displayed in the kb browser of task.";
	MessageName[ $TheoremaArchives, "usage", lang] = "List of currently loaded Theorema archives.";
	MessageName[ theoremaBoxes, "usage", lang] = "theoremaBoxes[expr] generates boxes for expr in Theorema syntax using the definitions for MakeBoxes[ expr, TheoremaForm].";	
	MessageName[ theoremaDisplay, "usage", lang] = "theoremaDisplay[expr] displays expr in Theorema syntax using the definitions for MakeBoxes[ expr, TheoremaForm].";	
	MessageName[ thinnedExpression, "usage", lang] = "";
	MessageName[ $tmaArchNeeds, "usage", lang] = "The list of subarchives needed by current archive.";
	MessageName[ $tmaArchTree, "usage", lang] = "Tree representation of the archive used in the commander.";
	MessageName[ $tmaArch, "usage", lang] = "Collection of environments evaluated in the current archive.";
	MessageName[ $TMAcheckSuccess, "usage", lang] = "$TMAcheckSuccess decides whether proof success is automatically checked when a new subgoal is constructed.";
	MessageName[ $TmaCompInsertPos, "usage", lang] = "$TmaCompInsertPos is the position in the global computation object, where the next subcomputation must be inserted.";
	MessageName[ $tmaCompPost, "usage", lang] = "$TmaCompPost is a function that is applied to the result of a computation after it has been renamed to the standard context.";
	MessageName[ $tmaCompPre, "usage", lang] = "$TmaCompPre is a function that is applied to an expression entered into a computation cell before it is evaluated.";
	MessageName[ $TMAcomputationDemoMode, "usage", lang] = "$TMAcomputationDemoMode is true if computations should run in demo-mode.";
	MessageName[ $TmaComputationObject, "usage", lang] = "$TmaComputationObject is the global computation object.";
	MessageName[ $TMAcurrentEvalNB, "usage", lang] = "$TMAcurrentEvalNB is the notebook in which the current evaluation has been initiated.";
	MessageName[ tmaDialogInput, "usage", lang] = "Theorema version of Mathematica's DialogInput.";
	MessageName[ $tmaEnv, "usage", lang] = "Collection of environments evaluated in the current session, i.e. the knowledge base.";
	MessageName[ $tmaFmlPost, "usage", lang] = "$TmaFmlPost is a function that is applied to a FML$-structure before it is stored in '$tmaEnv'.";
	MessageName[ $tmaFmlPre, "usage", lang] = "$tmaFmlPre is a function that is applied to a formula entered into a formula cell before it is turned into a FML$-structure.";
	MessageName[ $TmaLanguage, "usage", lang] = "The language used in the Theorema interface.";
	MessageName[ $TMALogFile, "usage", lang] = "The currently active log-file.";
	MessageName[ $tmaNbUpdateQueue, "usage", lang] = "The notebook update queue contains a list of timestamps when a notebook was last evaluated.";
	MessageName[ tmaNotebookPut, "usage", lang] = "Theorema version of Mathematica's NotebookPut.";
	MessageName[ $TMAproofNotebook, "usage", lang] = "$TMAproofNotebook is the notebook object containing the current proof.";
	MessageName[ $TMAproofObject, "usage", lang] = "$TMAproofObject is the global proof object.";
	MessageName[ $TMAproofSearchRunning, "usage", lang] = "$TMAproofSearchRunning indicates (by True/False) whether a proof search is currently running.";
	MessageName[ $TMAproofTree, "usage", lang] = "$TMAproofTree is the global proof tree for visualization.";
	MessageName[ $tmaUserRangeToCondition, "usage", lang] = "$tmaUserRangeToCondition is a list of rules that transform user-defined ranges into lists of conditions.";
	MessageName[ toBeProved, "usage", lang] = "toBeProved[ ...] constructs a new proof situation and checks for proof success immediately.";
	MessageName[ $traceUserDef, "usage", lang] = "Global variable. If True, then user definitions are traced and appear in the computation object.";
	MessageName[ trackCondition, "usage", lang] = "Track the evaluation of a condition during computation.";
	MessageName[ trackResult, "usage", lang] = "Track the evaluation of the result during computation.";
	MessageName[ transferToComputation, "usage", lang] = "";	
	MessageName[ translate, "usage", lang] = "translate[s_String,lang_String] gives string s in language lang.";
	MessageName[ trimKBforRewriting, "usage", lang] = "trimKBforRewriting[ k] processes the formulas in k and generates rewrite rules from appropriate candidates.";
	MessageName[ type, "usage", lang] = "type is a selector for proof node datastructures.";

	MessageName[ unexpected, "usage", lang] = "unexpected[ f, {args}] terminates the evaluation of f[args] due to unexpected/invalid arguments.";
	MessageName[ unifiable, "usage", lang] = "";
	MessageName[ unification, "usage", lang] = "";
	MessageName[ updateKBBrowser, "usage", lang] = "";
	MessageName[ used, "usage", lang] = "used is an option for the constructor makePRFINFO and a selector for the PRFINFO$ datastructure.";

	MessageName[ writeLog, "usage", lang] = "writeLog[ expr__] writes expr to the currently active log-file.";
]
