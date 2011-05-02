(* Mathematica package *)

With[ {lang = "German"},
(* Theorema Commander *)
    translate["tcLangTabLabel", lang] = "Sprache";
    	translate["tcLangTabEnvTabLabel", lang] = "Umgebungen";
    		translate["tcLangTabEnvTabButtonDefLabel", lang] = "Neue Definition";
    		translate["tcLangTabEnvTabButtonThmLabel", lang] = "Neues Theorem";
    		translate["tcLangTabEnvTabButtonFormLabel", lang] = "Neue Formel";
    	translate["tcLangTabMathTabLabel", lang] = "Mathematik";
     		translate["FORALL1", lang] = "f\[UDoubleDot]r alle \!\(\*FormBox[FrameBox[\"rg\"], Placeholder]\) gilt \!\(\*FormBox[FrameBox[\"expr\"], SelectionPlaceholder]\)";   	
     		translate["FORALL2", lang] = "f\[UDoubleDot]r alle \!\(\*FormBox[FrameBox[\"rg\"], Placeholder]\) mit \!\(\*FormBox[FrameBox[\"cond\"], Placeholder]\) gilt \!\(\*FormBox[FrameBox[\"expr\"], SelectionPlaceholder]\)";   	
     		translate["EXISTS1", lang] = "es existieren \!\(\*FormBox[FrameBox[\"rg\"], Placeholder]\), sodass \!\(\*FormBox[FrameBox[\"expr\"], SelectionPlaceholder]\)";   	
     		translate["EXISTS2", lang] = "es existieren \!\(\*FormBox[FrameBox[\"rg\"], Placeholder]\) mit \!\(\*FormBox[FrameBox[\"cond\"], Placeholder]\), sodass \!\(\*FormBox[FrameBox[\"expr\"], SelectionPlaceholder]\)";   	
     		translate["QUANT1Tooltip", lang] = "rg ... Laufbereiche der gebundenen Variablen\nexpr ... quantifizierter Ausdruck";   	
     		translate["QUANT2Tooltip", lang] = "rg ... Laufbereiche der gebundenen Variablen\ncond ... Bedingung an die Variablen\nexpr ... quantifizierter Ausdruck";   	
     		translate["tcLangTabMathTabBS", lang] = "Stil der Buttons:";   	
     		translate["tcLangTabMathTabBSnat", lang] = "nat\[UDoubleDot]rlich";   	
     		translate["tcLangTabMathTabBSform", lang] = "formal";   	
    translate["tcProveTabLabel", lang] = "Beweisen";
	    translate["tcProveTabKBTabLabel", lang] = "Wissen";
	    translate["tcProveTabBuiltinTabLabel", lang] = "eingebaut";
    translate["tcComputeTabLabel", lang] = "Rechnen";
	    translate["tcComputeTabKBTabLabel", lang] = "Wissen";
	    translate["tcComputeTabBuiltinTabLabel", lang] = "eingebaut";
    translate["tcPreferencesTabLabel", lang] = "Einstellungen";
	    translate["tcPrefLanguage", lang] = "Sprache";
    translate["not available", lang] = "nicht verf\[UDoubleDot]gbar";
    translate["No knowledge available", lang] = "Kein Wissen verf\[UDoubleDot]gbar";
   
    translate["Sets", lang] = "Mengen";
    translate["Arithmetic", lang] = "Arithmetik";
    translate["notUniqueLabel", lang] = "This label is not unique in the notebook: ";
]