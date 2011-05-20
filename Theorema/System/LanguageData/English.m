(* Mathematica package *)

With[ {lang = "English"},
(* System Messages *)
	MessageName[Theorema, "unexpectedArgs", lang] = "Function `1` called with unexpected arguments `2`.";
	MessageName[Theorema, "missingTranslation", lang] = "Missing translation for string `1` into language `2`.";

(* Theorema`System`Messages` *)
	MessageName[unexpected, "usage", lang] = "unexpected[ f, {args}] terminates the evaluation of f[args] due to unexpected arguments.";

(* Theorema`Language`Parser` *)
	MessageName[processEnvironment, "usage", lang] = "processEnvironment[ expr] ...";
	MessageName[processComputation, "usage", lang] = "processComputation[ expr] ...";
	MessageName[specifiedVariables, "usage", lang] = "";
	MessageName[$parseTheoremaExpressions, "usage", lang] = "whether to parse expressions with their Theorema meaning ...";

(* Theorema`Language`Session` *)
	MessageName[$tmaEnv, "usage", lang] = "Collection of environments evaluated in the current session, i.e. the knowledge base.";
	MessageName[$tmaArch, "usage", lang] = "Collection of environments evaluated in the current archive.";
	MessageName[$formulaCounterName,"usage", lang] = "Name of formulaCounter in the notebook options in CounterAssignments parameter.";
	MessageName[getCellIDLabel, "usage", lang] = "getCellIDLabel[cellID_Integer] returns string label for the given integer CellID value.";
	MessageName[getCleanCellTags,"usage", lang] = "getCleanCellTags[cellTags] returns all CellTags except tags used for cell identification: CellID_12345 and NotebookName_abcde.";
	
(* Theorema`Tools` *)
	MessageName[replaceAllExcept, "usage", lang] = "replaceAllExcept[ expr, rules, expt] applies rule(s) to all subparts of 'expr' except those contained in the list 'expt'.";
	MessageName[joinHold, "usage", lang] = "joinHold[Hold[a],Hold[b]] produces Hold[a,b].";
	MessageName[applyHold, "usage", lang] = "applyHold[Hold[a],Hold[b]] produces Hold[a[b]]";

(* Theorema`Interface`GUI` *)
	MessageName[$theoremaGUI, "usage", lang] = "Theorema GUI structure";
	MessageName[updateKBBrowser, "usage", lang] = "";
	MessageName[displayKBBrowser, "usage", lang] = "";
	MessageName[$initLabel, "usage", lang] = "Initial label of each formula. Serves as a hint for user to provide system with her own label.";
	MessageName[$labelSeparator, "usage", lang] = "Separator of different labels assigned to one formula.";
	MessageName[printComputationInfo, "usage", lang] = "Print info about global knowledge used inside a computation";
	
(* Theorema`Interface`Language` *)
	MessageName[translate, "usage", lang] = "translate[s_String,lang_String] gives string s in language lang.";
	MessageName[availableLanguages, "usage", lang] = "availableLanguages[] gives all available languages.";


]
