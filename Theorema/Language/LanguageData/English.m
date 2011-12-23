
With[ {lang = "English"},
	MessageName[QU$, "usage", lang] = "A marker introduced during the parsing process that temporarily marks quantified variables.";
	MessageName[VAR$, "usage", lang] = "";
	MessageName[RNG$, "usage", lang] = "";
	MessageName[SIMPRNG$, "usage", lang] = "SIMPRNG$[ x_] usually denotes that the variable x ranges over the universe.";
	MessageName[SETRNG$, "usage", lang] = "SETRNG$[ x_, s_] denotes that the variable x ranges over the set s.";
	MessageName[PREDRNG$, "usage", lang] = "PREDRNG$[ x_, p_] denotes that the variable x satisfies the predicate p.";
	MessageName[equalDef$TM, "usage", lang] = "";
	MessageName[iff$TM, "usage", lang] = "";
	MessageName[implies$TM, "usage", lang] = "";
	MessageName[and$TM, "usage", lang] = "";
	MessageName[or$TM, "usage", lang] = "";
	MessageName[forall$TM, "usage", lang] = "";
	MessageName[exists$TM, "usage", lang] = "";
	MessageName[globalForall$TM, "usage", lang] = "globalForall$TM[ rng_, cond_, decl_] is a datastructure representing a (nested) global universal variable, where 
	\*StyleBox[\"decl\", FontSlant -> \"Italic\"] contains further global declarations. globalForall$TM[ rng_, cond_] is a single global universal variable.";
	MessageName[globalImplies$TM, "usage", lang] = "globalImplies$TM[ cond_, decl_] is a datastructure representing a (nested) global condition, where
	\*StyleBox[\"decl\", FontSlant -> \"Italic\"] contains further global declarations. globalImplies$TM[ cond_] is a single global condition.";
]

