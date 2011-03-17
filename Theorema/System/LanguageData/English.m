(* Mathematica package *)

With[ {lang = "English"},
(* System Messages *)
	MessageName[Theorema, "unexpectedArgs", lang] = "Function `1` called with unexpected arguments `2`.";
	MessageName[Theorema, "missingTranslation", lang] = "Missing translation for string `1` into language `2`.";

(* Theorema`System`Messages` *)
	MessageName[unexpected, "usage", lang] = "unexpected[ f, {args}] terminates the evaluation of f[args] due to unexpected arguments.";

(* Theorema`Language`Parser` *)
	MessageName[processEnvironment, "usage", lang] = "processEnvironment[ expr] ...";
	MessageName[specifiedVariables, "usage", lang] = "";

(* Theorema`Language`Session` *)
	MessageName[inEnvironment, "usage", lang] = "initEnvironment[] evaluates to 'True' inside an environment ...";

(* Theorema`Tools` *)
	MessageName[replaceAllExcept, "usage", lang] = "replaceAllExcept[ expr, rules, expt] applies rule(s) to all subparts of 'expr' except those contained in the list 'expt'.";
	MessageName[joinHold, "usage", lang] = "joinHold[Hold[a],Hold[b]] produces Hold[a,b].";
	MessageName[applyHold, "usage", lang] = "applyHold[Hold[a],Hold[b]] produces Hold[a[b]]";

]
