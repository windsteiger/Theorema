(* Mathematica package *)

With[ {lang = "English"},
(* Theorema Commander *)
    translate["tcLangTabLabel", lang] = "Language";
    	translate["tcLangTabMathTabLabel", lang] = "math";
     		translate["AND1", lang] = "\!\(\*FormBox[FrameBox[\"left\"], SelectionPlaceholder]\) and \!\(\*FormBox[FrameBox[\"right\"], SelectionPlaceholder]\)";   	
     		translate["AND2", lang] = translate["AND1", lang];   	
     		translate["OR1", lang] = "\!\(\*FormBox[FrameBox[\"left\"], SelectionPlaceholder]\) or \!\(\*FormBox[FrameBox[\"right\"], SelectionPlaceholder]\)";   	
     		translate["OR2", lang] = translate["OR1", lang];   	
     		translate["IMPL1", lang] = "\!\(\*FormBox[FrameBox[\"left\"], SelectionPlaceholder]\) implies \!\(\*FormBox[FrameBox[\"right\"], SelectionPlaceholder]\)";   	
     		translate["IMPL2", lang] = translate["IMPL1", lang];   	
     		translate["EQUIV1", lang] = "\!\(\*FormBox[FrameBox[\"left\"], SelectionPlaceholder]\) iff \!\(\*FormBox[FrameBox[\"right\"], SelectionPlaceholder]\)";   	
     		translate["EQUIV2", lang] = translate["EQUIV1", lang];   	
     		translate["EQ1", lang] = "\!\(\*FormBox[FrameBox[\"left\"], SelectionPlaceholder]\) equals \!\(\*FormBox[FrameBox[\"right\"], SelectionPlaceholder]\)";   	
     		translate["EQ2", lang] = translate["EQ1", lang];   	
     		translate["EQUIVDEF", lang] = "\!\(\*FormBox[FrameBox[\"left\"], SelectionPlaceholder]\) iff \!\(\*FormBox[FrameBox[\"right\"], SelectionPlaceholder]\) (by def.)";   	
     		translate["EQDEF", lang] = "\!\(\*FormBox[FrameBox[\"left\"], SelectionPlaceholder]\) = \!\(\*FormBox[FrameBox[\"right\"], SelectionPlaceholder]\) (by def.)";   	
     		translate["FORALL1", lang] = "for all \!\(\*FormBox[FrameBox[\"rg\"], Placeholder]\): \!\(\*FormBox[FrameBox[\"expr\"], SelectionPlaceholder]\)";   	
     		translate["FORALL2", lang] = "for all \!\(\*FormBox[FrameBox[\"rg\"], Placeholder]\) satisfying \!\(\*FormBox[FrameBox[\"cond\"], Placeholder]\): \!\(\*FormBox[FrameBox[\"expr\"], SelectionPlaceholder]\)";   	
     		translate["EXISTS1", lang] = "exists \!\(\*FormBox[FrameBox[\"rg\"], Placeholder]\) s.t. \!\(\*FormBox[FrameBox[\"expr\"], SelectionPlaceholder]\)";   	
     		translate["EXISTS2", lang] = "exists \!\(\*FormBox[FrameBox[\"rg\"], Placeholder]\) satisfying \!\(\*FormBox[FrameBox[\"cond\"], Placeholder]\) s.t. \!\(\*FormBox[FrameBox[\"expr\"], SelectionPlaceholder]\)";   	
     		translate["CONN2Tooltip", lang] = "left, right ... formula\n";   	
     		translate["CONN2STRONGTooltip", lang] = "left, right ... formula\nstrong binding";   	
     		translate["CONN2WEAKTooltip", lang] = "left, right ... formula\nweak binding";   	
     		translate["EQUIVDEFTooltip", lang] = "left, right ... formula\npredicate definition";   	
     		translate["EQDEFTooltip", lang] = "left, right ... term\nfunction definition";   	
     		translate["QUANT1Tooltip", lang] = "rg ... ranges for the quantified variables\nexpr ... quantified expression";   	
     		translate["QUANT2Tooltip", lang] = "rg ... ranges for the quantified variables\ncond ... condition on the variables\nexpr ... quantified expression";   	
     		translate["tcLangTabMathTabBS", lang] = "Button style:";   	
     		translate["tcLangTabMathTabBSnat", lang] = "natural";   	
     		translate["tcLangTabMathTabBSform", lang] = "formal";   	
    	translate["tcLangTabEnvTabLabel", lang] = "environments";
    		translate["tcLangTabEnvTabButtonDefLabel", lang] = "Definition";
    		translate["tcLangTabEnvTabButtonThmLabel", lang] = "Theorem";
    		translate["tcLangTabEnvTabButtonLmaLabel", lang] = "Lemma";
    		translate["tcLangTabEnvTabButtonPrpLabel", lang] = "Proposition";
    		translate["tcLangTabEnvTabButtonCorLabel", lang] = "Corollary";
    		translate["tcLangTabEnvTabButtonCnjLabel", lang] = "Conjecture";
    		translate["tcLangTabEnvTabButtonAlgLabel", lang] = "Algorithm";
    		translate["tcLangTabEnvTabButtonExmLabel", lang] = "Example";
    		translate["tcLangTabEnvTabButtonFormLabel", lang] = "New Formula";
    	translate["tcLangTabArchTabLabel", lang] = "archives";
    		translate["tcLangTabArchTabSectionCreate", lang] = "Creating Archives";
    		translate["tcLangTabArchTabButtonArchLabel", lang] = "New Archive";
    		translate["tcLangTabArchTabButtonInfoLabel", lang] = "Archive Info";
    		translate["tcLangTabArchTabButtonCloseLabel", lang] = "Close Archive";
    		translate["tcLangTabArchTabSectionLoad", lang] = "Loading Archives";
    		translate["tcLangTabArchTabNoArchSel", lang] = "No archives selected";
    		translate["tcLangTabArchTabButtonSelectLabel", lang] = "Select Archives ...";
    		translate["tcLangTabArchTabButtonLoadLabel", lang] = "Load";
    translate["tcProveTabLabel", lang] = "Prove";
    	translate["tcProveTabGoalTabLabel", lang] = "goal";
    	translate["tcProveTabKBTabLabel", lang] = "knowledge";
    	translate["tcProveTabBuiltinTabLabel", lang] = "built-in";
    	translate["tcProveTabProverTabLabel", lang] = "prover";
    	translate["tcProveTabSubmitTabLabel", lang] = "submit";
    translate["tcComputeTabLabel", lang] = "Compute";
    	translate["tcComputeTabSetupTabLabel", lang] = "Setup";
    		translate["tcComputeTabSetupTabButtonCompLabel", lang] = "New Computation";
    	translate["tcComputeTabKBTabLabel", lang] = "KB";
    	translate["tcComputeTabBuiltinTabLabel", lang] = "built-in";
    translate["tcSolveTabLabel", lang] = "Solve";
    	translate["tcSolveTabKBTabLabel", lang] = "KB";
    translate["tcPreferencesTabLabel", lang] = "Preferences";
	    translate["tcPrefLanguage", lang] = "Language";
	    translate["tcPrefArchiveDir", lang] = "Archive Directory";
    translate["nA", lang] = "not available";
    translate["noKnowl", lang] = "No knowledge available";
	translate["noGoal", lang] = "Select a whole cell (cell bracket) containing the proof goal";
	    
    translate["Sets", lang] = "Sets";
    translate["Arithmetic", lang] = "Arithmetic";
    translate["Builtins used in computation", lang] = "Builtins used in computation";

(* General *)
	translate["outsideSession", lang] = "An evaluation of this type of cell is not expected in the current type of session";
	translate["archLabelNeeds", lang] = "needs: ";
	translate["archLabelPublic", lang] = "public: ";
	    
(* Theorema`Language`Session` *)
    translate["notUniqueLabel", lang] = "These labels are not unique in the notebook: ``\n\nThis is just a warning, you can continue,\nbut referencing formulae from this notebook\nmight turn out to be confusing.";
    translate["fileTypeArchive", lang] = "Theorema archive";
    translate["noArchName", lang] = "No archive name available for chosen archive. Check file content.";

]
