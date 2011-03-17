(* Mathematica package *)

With[ {lang = "English"},
(* Theorema Commander *)
    translate["tcLangTabLabel", lang] = "Language";
    	translate["tcLangTabEnvTabLabel", lang] = "environments";
    		translate["tcLangTabEnvTabButtonDefLabel", lang] = "New Definition";
    		translate["tcLangTabEnvTabButtonThmLabel", lang] = "New Theorem";
    	translate["tcLangTabMathTabLabel", lang] = "math";
     		translate["FORALL1", lang] = "for all \!\(\*FormBox[FrameBox[\"rg\"], Placeholder]\): \!\(\*FormBox[FrameBox[\"expr\"], SelectionPlaceholder]\)";   	
     		translate["FORALL2", lang] = "for all \!\(\*FormBox[FrameBox[\"rg\"], Placeholder]\) satisfying \!\(\*FormBox[FrameBox[\"cond\"], Placeholder]\): \!\(\*FormBox[FrameBox[\"expr\"], SelectionPlaceholder]\)";   	
     		translate["EXISTS1", lang] = "exists \!\(\*FormBox[FrameBox[\"rg\"], Placeholder]\) s.t. \!\(\*FormBox[FrameBox[\"expr\"], SelectionPlaceholder]\)";   	
     		translate["EXISTS2", lang] = "exists \!\(\*FormBox[FrameBox[\"rg\"], Placeholder]\) satisfying \!\(\*FormBox[FrameBox[\"cond\"], Placeholder]\) s.t. \!\(\*FormBox[FrameBox[\"expr\"], SelectionPlaceholder]\)";   	
     		translate["QUANT1Tooltip", lang] = "rg ... ranges for the quantified variables\nexpr ... quantified expression";   	
     		translate["QUANT2Tooltip", lang] = "rg ... ranges for the quantified variables\ncond ... condition on the variables\nexpr ... quantified expression";   	
     		translate["tcLangTabMathTabBS", lang] = "Button style:";   	
     		translate["tcLangTabMathTabBSnat", lang] = "natural";   	
     		translate["tcLangTabMathTabBSform", lang] = "formal";   	
    translate["tcProveTabLabel", lang] = "Prove";
    	translate["tcProveTabKBTabLabel", lang] = "KB";
    	translate["tcProveTabBuiltinTabLabel", lang] = "built-in";
    translate["tcComputeTabLabel", lang] = "Compute";
    	translate["tcComputeTabKBTabLabel", lang] = "KB";
    	translate["tcComputeTabBuiltinTabLabel", lang] = "built-in";
    translate["tcPreferencesTabLabel", lang] = "Preferences";
	    translate["tcPrefLanguage", lang] = "Language";
    translate["not available", lang] = "not available";
    translate["No knowledge available", lang] = "No knowledge available";
]
