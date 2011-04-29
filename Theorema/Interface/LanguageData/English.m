(* Mathematica package *)

With[ {lang = "English"},
(* Theorema Commander *)
    translate["tcLangTabLabel", lang] = "Language";
    	translate["tcLangTabEnvTabLabel", lang] = "environments";
    		translate["tcLangTabEnvTabButtonDefLabel", lang] = "New Definition";
    		translate["tcLangTabEnvTabButtonThmLabel", lang] = "New Theorem";
    		translate["tcLangTabEnvTabButtonFormLabel", lang] = "New Formula";
    	translate["tcLangTabMathTabLabel", lang] = "math";
     		translate["AND1", lang] = "\!\(\*FormBox[FrameBox[\"left\"], SelectionPlaceholder]\) and \!\(\*FormBox[FrameBox[\"right\"], SelectionPlaceholder]\)";   	
     		translate["AND2", lang] = translate["AND1", lang];   	
     		translate["OR1", lang] = "\!\(\*FormBox[FrameBox[\"left\"], SelectionPlaceholder]\) or \!\(\*FormBox[FrameBox[\"right\"], SelectionPlaceholder]\)";   	
     		translate["OR2", lang] = translate["OR1", lang];   	
     		translate["IMPL1", lang] = "\!\(\*FormBox[FrameBox[\"left\"], SelectionPlaceholder]\) implies \!\(\*FormBox[FrameBox[\"right\"], SelectionPlaceholder]\)";   	
     		translate["IMPL2", lang] = translate["IMPL1", lang];   	
     		translate["EQUIV1", lang] = "\!\(\*FormBox[FrameBox[\"left\"], SelectionPlaceholder]\) iff \!\(\*FormBox[FrameBox[\"right\"], SelectionPlaceholder]\)";   	
     		translate["EQUIV2", lang] = translate["EQUIV1", lang];   	
     		translate["EQUIVDEF", lang] = "\!\(\*FormBox[FrameBox[\"left\"], SelectionPlaceholder]\) iff \!\(\*FormBox[FrameBox[\"right\"], SelectionPlaceholder]\) (by def.)";   	
     		translate["EQDEF", lang] = "\!\(\*FormBox[FrameBox[\"left\"], SelectionPlaceholder]\) = \!\(\*FormBox[FrameBox[\"right\"], SelectionPlaceholder]\) (by def.)";   	
     		translate["FORALL1", lang] = "for all \!\(\*FormBox[FrameBox[\"rg\"], Placeholder]\): \!\(\*FormBox[FrameBox[\"expr\"], SelectionPlaceholder]\)";   	
     		translate["FORALL2", lang] = "for all \!\(\*FormBox[FrameBox[\"rg\"], Placeholder]\) satisfying \!\(\*FormBox[FrameBox[\"cond\"], Placeholder]\): \!\(\*FormBox[FrameBox[\"expr\"], SelectionPlaceholder]\)";   	
     		translate["EXISTS1", lang] = "exists \!\(\*FormBox[FrameBox[\"rg\"], Placeholder]\) s.t. \!\(\*FormBox[FrameBox[\"expr\"], SelectionPlaceholder]\)";   	
     		translate["EXISTS2", lang] = "exists \!\(\*FormBox[FrameBox[\"rg\"], Placeholder]\) satisfying \!\(\*FormBox[FrameBox[\"cond\"], Placeholder]\) s.t. \!\(\*FormBox[FrameBox[\"expr\"], SelectionPlaceholder]\)";   	
     		translate["CONN2STRONGTooltip", lang] = "left, right ... formula\nstrong binding";   	
     		translate["CONN2WEAKTooltip", lang] = "left, right ... formula\nweak binding";   	
     		translate["EQUIVDEFTooltip", lang] = "left, right ... formula\npredicate definition";   	
     		translate["EQDEFTooltip", lang] = "left, right ... term\nfunction definition";   	
     		translate["QUANT1Tooltip", lang] = "rg ... ranges for the quantified variables\nexpr ... quantified expression";   	
     		translate["QUANT2Tooltip", lang] = "rg ... ranges for the quantified variables\ncond ... condition on the variables\nexpr ... quantified expression";   	
     		translate["tcLangTabMathTabBS", lang] = "Button style:";   	
     		translate["tcLangTabMathTabBSnat", lang] = "natural";   	
     		translate["tcLangTabMathTabBSform", lang] = "formal";   	
    translate["tcProveTabLabel", lang] = "Prove";
    	translate["tcProveTabKBTabLabel", lang] = "KB";
    	translate["tcProveTabBuiltinTabLabel", lang] = "built-in";
    translate["tcComputeTabLabel", lang] = "Compute";
    	translate["tcComputeTabSetupTabLabel", lang] = "Setup";
    		translate["tcComputeTabSetupTabButtonCompLabel", lang] = "New Computation";
    	translate["tcComputeTabKBTabLabel", lang] = "KB";
    	translate["tcComputeTabBuiltinTabLabel", lang] = "built-in";
    translate["tcPreferencesTabLabel", lang] = "Preferences";
	    translate["tcPrefLanguage", lang] = "Language";
    translate["not available", lang] = "not available";
    translate["No knowledge available", lang] = "No knowledge available";
    
    translate["Sets", lang] = "Sets";
    translate["Arithmetic", lang] = "Arithmetic";
    translate["Builtins used in computation", lang] = "Builtins used in computation";
]
