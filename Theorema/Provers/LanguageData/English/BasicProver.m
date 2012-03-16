
With[ {lang = "English"},

MessageName[ basicProver, "usage", lang] := "The prover that handles the basic language constructs from the Theorema language, standard propositional and predicate logic.";
MessageName[ quantifierRules, "usage", lang] := "The prover that handles quantifiers.";
MessageName[ applyOnce, "usage", lang] := "This strategy applies a matching inference rule once.";
MessageName[ trySeveral, "usage", lang] := "This strategy tries several rules at the same time.";

translate[ "Quantifier Rules", lang] := "Quantifier Rules";
translate[ "Basic Prover", lang] := "Basic Prover";
translate[ "connectives", lang] := "Logical connectives";
translate[ "equality", lang] := "Logical equality";
translate[ "Apply once", lang] := "Apply once";
translate[ "Try several", lang] := "Try several";

proofStepText[ "andGoal", lang, used_, generated_, ___] := {textCell[ "For proving ", referenceCell[ First[ used]], " we prove the individual conjuncts."]};

subProofHeader[ "andGoal", lang, used_, generated_, {p_}] := {textCell[ "Proof of ", referenceCell[ Part[ generated, p]], ":"],
	textCell[ "We need to prove "],
	goalCell[ Part[ generated, p], "."]
	};
 

] (* With *)

