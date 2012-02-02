(* Mathematica package *)

With[ {lang = "English"},
(* System Messages *)
	MessageName[Theorema, "unexpectedArgs", lang] = "Function `1` called with unexpected arguments `2`.";
	MessageName[Theorema, "missingTranslation", lang] = "Missing translation for string `1` into language `2`.";

(* Theorema`System`Messages` *)
	MessageName[unexpected, "usage", lang] = "unexpected[ f, {args}] terminates the evaluation of f[args] due to unexpected arguments.";

(* Theorema`Language`Parser` *)
	MessageName[specifiedVariables, "usage", lang] = "";
	MessageName[$parseTheoremaExpressions, "usage", lang] = "whether to parse expressions with their Theorema meaning ...";
	MessageName[$parseTheoremaGlobals, "usage", lang] = "whether to parse expressions with their Theorema meaning in a global declaration ...";

(* Theorema`Language`Session` *)
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
	MessageName[inArchive,"usage",lang] = "inArchive[] returns True when we are currently processing an archive.";
	MessageName[archiveName,"usage",lang] = "archiveName[f] returns the short archive name (=context name) for an archive stored in file f.";
	MessageName[processEnvironment, "usage", lang] = "processEnvironment[ expr] ...";
	MessageName[processComputation, "usage", lang] = "processComputation[ expr] ...";
	MessageName[findSelectedFormula, "usage", lang] = "findSelectedFormula[ sel] ...";

(* Theorema`Language`FormulaManipulation` *)
	MessageName[makeSet, "usage", lang] = "";	
	MessageName[freeVariables, "usage", lang] = "";	
	MessageName[splitAnd, "usage", lang] = "";	
	MessageName[makeConjunction, "usage", lang] = "";	
	MessageName[makeDisjunction, "usage", lang] = "";	
	MessageName[substituteFree, "usage", lang] = "";	


(* Theorema`Computation`Language` *)
	MessageName[setComputationContext, "usage", lang] = "setComputationContext[ c] sets the context for the next computation to c.";
	
(* Theorema`Utilities` *)
	MessageName[replaceAllExcept, "usage", lang] = "replaceAllExcept[ expr, rules, expt] applies rule(s) to all subparts of 'expr' except those contained in the list 'expt'.";
	MessageName[joinHold, "usage", lang] = "joinHold[Hold[a],Hold[b]] produces Hold[a,b].";
	MessageName[applyHold, "usage", lang] = "applyHold[Hold[a],Hold[b]] produces Hold[a[b]].";
	MessageName[joinKB, "usage", lang] = "joinKB[ kb1_List, kb2_List] joins the two knowledge bases and deletes duplicate entries.";
	MessageName[notification, "usage", lang] = "notification[text] displays 'text' as a user notification.";

(* Theorema`Interface`GUI` *)
	MessageName[$theoremaGUI, "usage", lang] = "Theorema GUI structure";
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


]
