TabView[{"knowledge" -> Pane[Row[{}, ", "], 500], 
  "built-in" -> Column[{Style["Sets", "ComponentEmpty"], 
     Style["Tuples", "ComponentEmpty"], OpenerView[
      {"Arithmetic", Column[{Row[{"\[Checkmark] ", Style["Equal", 
            "ComponentActive"]}], Row[{Style["Plus", "ComponentInactive"], 
           ",", Style["Minus", "ComponentInactive"], ",", 
           Style["Times", "ComponentInactive"], ",", Style["MultInverse", 
            "ComponentInactive"], ",", Style["Power", "ComponentInactive"], 
           ",", Style["Radical", "ComponentInactive"], ",", 
           Style["Factorial", "ComponentInactive"], ",", Style["Less", 
            "ComponentInactive"], ",", Style["LessEqual", 
            "ComponentInactive"], ",", Style["Greater", "ComponentInactive"], 
           ",", Style["GreaterEqual", "ComponentInactive"], ",", 
           Style["AbsValue", "ComponentInactive"], ",", Style["SumOf", 
            "ComponentInactive"], ",", Style["ProductOf", 
            "ComponentInactive"]}]}]}, True], 
     OpenerView[{"Logic", Column[{Row[{"\[Checkmark] ", Style["Not", 
            "ComponentActive"], ",", Style["And", "ComponentActive"], ",", 
           Style["Or", "ComponentActive"], ",", Style["Implies", 
            "ComponentActive"], ",", Style["Iff", "ComponentActive"], ",", 
           Style["Equal", "ComponentActive"]}], 
         Row[{Style["Forall", "ComponentInactive"], ",", Style["Exists", 
            "ComponentInactive"], ",", Style["Let", "ComponentInactive"], 
           ",", Style["Componentwise", "ComponentInactive"], ",", 
           Style["Such", "ComponentInactive"], ",", Style["SuchUnique", 
            "ComponentInactive"]}]}]}, True], Style["Domains", 
      "ComponentEmpty"], Style["Programming", "ComponentEmpty"]}], 
  "prover" -> TabView[{"Selected Rules" -> 
      Pane[Column[{Style[Row[{"(1)", Spacer[2], Tooltip["\:270d", "Specifies, \
whether the proof text for the rule will be activated. (ruleTextActive)"], 
            Spacer[5], "Knowledge base contains contradicting formulae"}], 
          LineBreakWithin -> False], Style[Row[{"(1)", Spacer[2], 
            Tooltip["\:270d", "Specifies, whether the proof text for the rule \
will be activated. (ruleTextActive)"], Spacer[5], "The proof goal is True"}], 
          LineBreakWithin -> False], Style[Row[{"(1)", Spacer[2], 
            Tooltip["\:270d", "Specifies, whether the proof text for the rule \
will be activated. (ruleTextActive)"], Spacer[5], 
            "Knowledge base contains a formula False"}], LineBreakWithin -> 
           False], Style[Row[{"(1)", Spacer[2], Tooltip["\:270d", "Specifies, \
whether the proof text for the rule will be activated. (ruleTextActive)"], 
            Spacer[5], "Knowledge base contains the proof goal"}], 
          LineBreakWithin -> False], Style[Row[{"(2)", Spacer[2], 
            Tooltip["\:270d", "Specifies, whether the proof text for the rule \
will be activated. (ruleTextActive)"], Spacer[5], 
            "Knowledge base contains two contradicting universally quantified \
formulas."}], LineBreakWithin -> False], Style[Row[{"(2)", Spacer[2], 
            Tooltip["\:270d", "Specifies, whether the proof text for the rule \
will be activated. (ruleTextActive)"], Spacer[5], "Knowledge base contains a \
universally quantified formulae that contradicts some other formula."}], 
          LineBreakWithin -> False], Style[Row[{"(4)", Spacer[2], 
            Tooltip["\:270d", "Specifies, whether the proof text for the rule \
will be activated. (ruleTextActive)"], Spacer[5], "Elementary substitution \
based on equalities and equivalences in the knowledge base"}], 
          LineBreakWithin -> False], Style[Row[{"(5)", Spacer[2], 
            Tooltip["\:270d", "Specifies, whether the proof text for the rule \
will be activated. (ruleTextActive)"], Spacer[5], 
            "Prove implication directly"}], LineBreakWithin -> False], 
         Style[Row[{"(5)", Spacer[2], Tooltip["\:270d", "Specifies, whether \
the proof text for the rule will be activated. (ruleTextActive)"], Spacer[5], 
            "Prove disjunction"}], LineBreakWithin -> False], 
         Style[Row[{"(5)", Spacer[2], Tooltip["\:2751", "Specifies, whether \
the proof text for the rule will be activated. (ruleTextActive)"], Spacer[5], 
            "Split a conjunction in the knowledge base"}], 
          LineBreakWithin -> False], Style[Row[{"(6)", Spacer[2], 
            Tooltip["\:270d", "Specifies, whether the proof text for the rule \
will be activated. (ruleTextActive)"], Spacer[5], 
            "Split a conjunction in the goal"}], LineBreakWithin -> False], 
         Style[Row[{"(9)", Spacer[2], Tooltip["\:270d", "Specifies, whether \
the proof text for the rule will be activated. (ruleTextActive)"], Spacer[5], 
            "Instantiate meta-variables by unification"}], 
          LineBreakWithin -> False], Style[Row[{"(10)", Spacer[2], 
            Tooltip["\:270d", "Specifies, whether the proof text for the rule \
will be activated. (ruleTextActive)"], Spacer[5], 
            "Prove equivalence by double implication"}], LineBreakWithin -> 
           False], Style[Row[{"(10)", Spacer[2], Tooltip["\:270d", "Specifies\
, whether the proof text for the rule will be activated. (ruleTextActive)"], 
            Spacer[5], "Prove existentially quantified goal by introducing \
meta variables"}], LineBreakWithin -> False], 
         Style[Row[{"(10)", Spacer[2], Tooltip["\:270d", "Specifies, whether \
the proof text for the rule will be activated. (ruleTextActive)"], Spacer[5], 
            "Prove universally quantified goal"}], LineBreakWithin -> False], 
         Style[Row[{"(11)", Spacer[2], Tooltip["\:270d", "Specifies, whether \
the proof text for the rule will be activated. (ruleTextActive)"], Spacer[5], 
            "Skolemize existentially quantified knowledge"}], 
          LineBreakWithin -> False], Style[Row[{"(19)", Spacer[2], 
            Tooltip["\:270d", "Specifies, whether the proof text for the rule \
will be activated. (ruleTextActive)"], Spacer[5], 
            "Case distinction based on a disjunction in the knowledge base"}]\
, LineBreakWithin -> False], Style[Row[{"(22)", Spacer[2], Tooltip["\:270d", 
             "Specifies, whether the proof text for the rule will be \
activated. (ruleTextActive)"], Spacer[5], "Goal rewriting based on \
(quantified) implications and equivalences in the knowledge base"}], 
          LineBreakWithin -> False], Style[Row[{"(25)", Spacer[2], 
            Tooltip["\:270d", "Specifies, whether the proof text for the rule \
will be activated. (ruleTextActive)"], Spacer[5], "Knowledge rewriting based \
on (quantified) implications and equivalences in the knowledge base"}], 
          LineBreakWithin -> False], Style[Row[{"(30)", Spacer[2], 
            Tooltip["\:270d", "Specifies, whether the proof text for the rule \
will be activated. (ruleTextActive)"], Spacer[5], 
            "Prove negation by contradiction"}], LineBreakWithin -> False], 
         Style[Row[{"(35)", Spacer[2], Tooltip["\:270d", "Specifies, whether \
the proof text for the rule will be activated. (ruleTextActive)"], Spacer[5], 
            "Instantiate universally quantified knowledge with new constants"}\
], LineBreakWithin -> False], Style[Row[{"(40)", Spacer[2], 
            Tooltip["\:270d", "Specifies, whether the proof text for the rule \
will be activated. (ruleTextActive)"], Spacer[5], 
            "Instantiate new universally quantified knowledge"}], 
          LineBreakWithin -> False], Style[Row[{"(80)", Spacer[2], 
            Tooltip["\:270d", "Specifies, whether the proof text for the rule \
will be activated. (ruleTextActive)"], Spacer[5], 
            "Handle implicit function definitions"}], LineBreakWithin -> 
           False], Style[Row[{"(80)", Spacer[2], Tooltip["\:270d", "Specifies\
, whether the proof text for the rule will be activated. (ruleTextActive)"], 
            Spacer[5], "Expand explicit definitions"}], LineBreakWithin -> 
           False], Style[Row[{"(100)", Spacer[2], Tooltip["\:270d", "Specifie\
s, whether the proof text for the rule will be activated. (ruleTextActive)"], 
            Spacer[5], "Prove by contradiction"}], LineBreakWithin -> 
           False]}], ImageSize -> {360, 200}, Scrollbars -> {False, True}], 
     "Proof Strategy" -> "Apply once + Level saturation", 
     "Proof Search Limits" -> Column[{Labeled[30, "Search Depth:", Left], 
        Labeled[360, "Search Time:", Left]}], "Proof Simplification" -> 
      Column[{"Eliminate failing/pending branches", Null, Null}], 
     "Interactive Proving" -> Column[{Null, Null, Null}], 
     "Proof Cells" -> "automatic", "statistics" -> 
      Column[{Labeled[1.848107`6.417242109826637, 
         "Time spent for finding the proof:", Left], 
        Labeled[0.023407`4.51986075296666, 
         "Time spent for simplifying the proof:", Left]}]}, 
    AutoAction -> True, ControlPlacement -> Left], 
  "Restore settings" -> Row[{"Really restore all relevant settings to the \
values they had when this action was performed last time?", 
     Button["OK", Theorema`Interface`GUI`Private`setProveEnv["/home/wwindste/\
Theorema.2/Theorema/Theorema/Documentation/English/TheoremaNotebooks/FirstTou\
r/p443431148-2.m"]]}, Spacer[5]]}, ImageSize -> Automatic]
