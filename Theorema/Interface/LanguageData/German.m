(* Mathematica package *)

With[ {lang = "German"},
(* Theorema Commander *)
    translate["tcLangTabLabel", lang] = "Sprache";
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
    	translate["tcLangTabEnvTabLabel", lang] = "Umgebungen";
    		translate["tcLangTabEnvTabButtonDefLabel", lang] = "Neue Definition";
    		translate["tcLangTabEnvTabButtonThmLabel", lang] = "Neues Theorem";
    		translate["tcLangTabEnvTabButtonFormLabel", lang] = "Neue Formel";
    	translate["tcLangTabArchTabLabel", lang] = "Archive";
    		translate["tcLangTabArchTabButtonArchLabel", lang] = "Neues Archiv";
    		translate["tcLangTabArchTabButtonInfoLabel", lang] = "Archiv Info";
    		translate["tcLangTabArchTabButtonCloseLabel", lang] = "Archiv schlie\[SZ]en";
    translate["tcProveTabLabel", lang] = "Beweisen";
	    translate["tcProveTabKBTabLabel", lang] = "Wissen";
	    translate["tcProveTabBuiltinTabLabel", lang] = "eingebaut";
    translate["tcComputeTabLabel", lang] = "Rechnen";
	    translate["tcComputeTabKBTabLabel", lang] = "Wissen";
	    translate["tcComputeTabBuiltinTabLabel", lang] = "eingebaut";
    translate["tcPreferencesTabLabel", lang] = "Einstellungen";
	    translate["tcPrefLanguage", lang] = "Sprache";
	    translate["tcPrefArchiveDir", lang] = "Archiv Verzeichnis";
    translate["nA", lang] = "nicht verf\[UDoubleDot]gbar";
    translate["noKnowl", lang] = "Kein Wissen verf\[UDoubleDot]gbar";
   
    translate["Operators", lang] = "Operatoren";
    translate["Sets", lang] = "Mengen";
    translate["Tuples", lang] = "Tupel";
    translate["Arithmetic", lang] = "Arithmetik";
    translate["Logic", lang] = "Logik";
    translate["Domains", lang] = "Bereiche und Datentypen";
    translate["Programming", lang] = "Mathematica Programmierung";
    translate["notUniqueLabel", lang] = "This label is not unique in the notebook: ";
    
    translate["archLabelNeeds", lang] = "verwendet:";
	translate["archLabelPublic", lang] = "\[ODoubleDot]ffentlich:";
    translate["fileTypeArchive", lang] = "Theorema Archiv";

]