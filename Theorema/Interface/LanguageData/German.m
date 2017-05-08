(* Theorema 
    Copyright (C) 1995-2014 The Theorema Group

    This file is part of Theorema 2.0
    
    Theorema 2.0 is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Theorema 2.0 is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program. If not, see <http://www.gnu.org/licenses/>.
*)

(*
   *********************************************************************************************
   -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- 
   *********************************************************************************************
 
     If you modify this file, then a new entry must have been added to the file "English"
     in this directory already.

     In this file, either
      1) copy the english entry into the section named "UNTRANSLATED" at the end of this file 
	       or
      2) translate the english entry and add it in correct alphabetical order here 
         (case-insensitive).
      
   *********************************************************************************************
   -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- 
   *********************************************************************************************
 *)

With[ {lang = "German"},

(* TRANSLATED *)
    translate[ "0ANNOPTooltip", lang] = "\[SmallCircle] \[Ellipsis] Operatorsymbol";
    translate[ "1ANNOPTooltip", lang] = "\[SmallCircle] \[Ellipsis] Operatorsymbol\nA \[Ellipsis] Annotation";
    translate[ "2ANNOPTooltip", lang] = "\[SmallCircle] \[Ellipsis] Operatorsymbol\nA \[Ellipsis] Annotation\nB \[Ellipsis] Annotation";

	translate[ "abort", lang] = "Beweis abbrechen";
	translate[ "aboutTheorema", lang] = "Theorema wurde um 1995 von Bruno Buchberger konzipiert und initiiert und reflektiert seine Sicht, \"Mathematik \
zu betreiben\". Entwickelt wird es unter seiner Leitung durch die Theorema-Gruppe am Research Institute for Symbolic Computation (RISC), Johannes Kepler \
Universit\[ADoubleDot]t, Linz-Hagenberg, Austria. \
Theorema 2.0 ist eine wesentliche Weiterentwicklung, die haupts\[ADoubleDot]chlich durch Wolfgang Windsteiger vorangetrieben wird.";
    translate[ "ambiguousRange", lang] = "Der Bereich `` bezeichnet keine Variable in eindeutiger Weise.";
    translate[ "AND2", lang] = "\!\(\*FormBox[FrameBox[\"links\"], SelectionPlaceholder]\) und \!\(\*FormBox[FrameBox[\"rechts\"], SelectionPlaceholder]\)";   	
    translate[ "AND3", lang] = "\!\(\*FormBox[FrameBox[\"e1\"], SelectionPlaceholder]\) und \[Ellipsis] und \!\(\*FormBox[FrameBox[\"en\"], SelectionPlaceholder]\)";
	translate[ "apply color scheme", lang] = "Farbschema anwenden";
	translate[ "archiveNameDialogField", lang] = "W\[ADoubleDot]hlen Sie einen Namen f\[UDoubleDot]r das Archiv:";
	translate[ "archiveNameDialogHint", lang] = "Ein g\[UDoubleDot]ltiger Name muss mit ` enden";
	translate[ "archLabelBegin", lang] = "Beginn Archiv";
	translate[ "archLabelEnd", lang] = "Ende Archiv";
	translate[ "archLabelName", lang] = "Name:  ";
	translate[ "archLabelPublic", lang] = "\[CapitalODoubleDot]ffentlich: ";
    translate[ "Arithmetic", lang] = "Arithmetik";
	translate[ "auto", lang] = "automatisch";
	translate[ "availConst", lang] = "Verf\[UDoubleDot]gbare Konstante";

    translate[ "BuiComp", lang] = "In der Berechnung verwendete Builtins";
    translate[ "BuiProve", lang] = "Im Beweis verwendete Builtins";

    translate[ "cantCreateDir", lang] = "Das Verzeichnis `` kann nicht erstellt werden";
    translate[ "CASEDIST", lang] = "Unterscheide die F\[ADoubleDot]lle \!\(\*FormBox[FrameBox[\"c1\"], Placeholder]\) \[Ellipsis] \!\(\*FormBox[FrameBox[\"cn\"], Placeholder]\)";
    translate[ "CASEDISTTooltip", lang] = "e1, \[Ellipsis], en \[Ellipsis] Ausdr\[UDoubleDot]cke \nc1, \[Ellipsis], cn \[Ellipsis] Bedingungen";   	
	translate[ "closed", lang] = "alle geschlossen";
    translate[ "Computation", lang] = "Berechnung";
	translate[ "computationTime", lang] = "Rechenzeit";
    translate[ "CONN2Tooltip", lang] = "links, rechts \[Ellipsis] Aussage";   	
	translate[ "connArgM", lang] = "Junktor \"`1`\" wird auf `2` Argumente angewendet; es werden genau `3` Argumente erwartet.";
    translate[ "CONNTooltip", lang] = "e1, \[Ellipsis], en \[Ellipsis] Aussage";

    translate[ "TimeStamp", lang] = "Zeitpunkt";
    translate[ "Declarations", lang] = "Globale";
    translate[ "DemoMode", lang] = "Demo Modus";
	translate[ "Display with new settings", lang] = "Mit neuen Einstellungen anzeigen";
	translate[ "disproved", lang] = "widerlegt";
    translate[ "Domains", lang] = "Bereiche und Datenstrukturen";

	translate[ "elimBranches", lang] = "Erfolglose bzw. unerledigte Zweige eliminieren";
	translate[ "elimForm", lang] = "Nicht verwendete Aussagen eliminieren";
	translate[ "elimSteps", lang] = "\[CapitalUDoubleDot]berfl\[UDoubleDot]ssige Schritte eliminieren";
    translate[ "Environments", lang] = "Umgebungen";
    translate[ "EQ", lang] = "\!\(\*FormBox[FrameBox[\"links\"], SelectionPlaceholder]\) gleich \!\(\*FormBox[FrameBox[\"rechts\"], SelectionPlaceholder]\)";   	
    translate[ "EQDEF", lang] = "\!\(\*FormBox[FrameBox[\"links\"], SelectionPlaceholder]\) = \!\(\*FormBox[FrameBox[\"rechts\"], SelectionPlaceholder]\) (per Def.)";   	
    translate[ "EQDEFTooltip", lang] = "links, rechts \[Ellipsis] Term\nFunktionsdefinition";   	
    translate[ "EQUIV2", lang] = "\!\(\*FormBox[FrameBox[\"links\"], SelectionPlaceholder]\) gdw. \!\(\*FormBox[FrameBox[\"rechts\"], SelectionPlaceholder]\)";   	
    translate[ "EQUIV3", lang] = "\!\(\*FormBox[FrameBox[\"e1\"], SelectionPlaceholder]\) gdw. \[Ellipsis] gdw. \!\(\*FormBox[FrameBox[\"en\"], SelectionPlaceholder]\)";
    translate[ "EQUIVDEF", lang] = "\!\(\*FormBox[FrameBox[\"links\"], SelectionPlaceholder]\) gdw \!\(\*FormBox[FrameBox[\"rechts\"], SelectionPlaceholder]\) (per Def.)";   	
    translate[ "EQUIVDEFTooltip", lang] = "links, rechts \[Ellipsis] Aussage\nPr\[ADoubleDot]dikatendefinition";   	
    translate[ "EXISTS1", lang] = "es existieren \!\(\*FormBox[FrameBox[\"Ber\"], Placeholder]\) sodass \!\(\*FormBox[FrameBox[\"Auss\"], SelectionPlaceholder]\)";   	
    translate[ "EXISTS2", lang] = "es existieren \!\(\*FormBox[FrameBox[\"Ber\"], Placeholder]\) mit \!\(\*FormBox[FrameBox[\"Bed\"], Placeholder]\) sodass \!\(\*FormBox[FrameBox[\"A\"], SelectionPlaceholder]\)";   	

	translate[ "failed", lang] = "fehlgeschlagen";
    translate[ "fileTypeArchive", lang] = "Theorema Archiv";
    translate[ "fileTypeNotebook", lang] = "Theorema Notebook";
	translate[ "FilteredBy", lang] = "Gefiltert durch";
	translate[ "FilterKBWindow", lang] = "Durch Schl\[UDoubleDot]sselwort filtern";
	translate[ "Filter", lang] = "Filtern";
	translate[ "FilterRulesWindow", lang] = "Durch Schl\[UDoubleDot]sselwort filtern";
    translate[ "fit into window", lang] = "In das Fenster einpassen";
    translate[ "FORALL1", lang] = "f\[UDoubleDot]r alle \!\(\*FormBox[FrameBox[\"Ber\"], Placeholder]\) gilt \!\(\*FormBox[FrameBox[\"Auss\"], SelectionPlaceholder]\)";   	
    translate[ "FORALL2", lang] = "f\[UDoubleDot]r alle \!\(\*FormBox[FrameBox[\"Ber\"], Placeholder]\) mit \!\(\*FormBox[FrameBox[\"Bed\"], Placeholder]\) gilt \!\(\*FormBox[FrameBox[\"A\"], SelectionPlaceholder]\)";   	
    translate[ "Formulae", lang] = "Aussagen";

    translate[ "GABBREVTooltip", lang] = "Globale Abk\[UDoubleDot]rzung";   	
    translate[ "GCONDTooltip", lang] = "Globale Bedingung";   	
    translate[ "Global Declarations", lang] = "In dieser Zelle g\[UDoubleDot]ltige Globale";
    translate[ "GNULicense", lang] = StringForm[ "Copyright (\[Copyright]) 1995-`` Die Theorema-Gruppe\n\n\
Theorema 2.0 ist freie Software: es darf unter Einhaltung der Bedingungen der GNU General \
Public License wie von der Free Software Foundation publiziert, entweder Version 3 der Lizenz oder \
wahlweise jede sp\[ADoubleDot]tere Version, weitergegeben und/oder modifiziert werden.\n\n\
Theorema 2.0 wird in der Hoffnung weitergegeben, dass es n\[UDoubleDot]tzlich ist, es gibt allerdings \
keinerlei Garantie, nicht einmal eine Zusicherung allgemeiner Gebrauchstauglichkeit oder einer \
Eignung f\[UDoubleDot]r einen bestimmten Zweck. F\[UDoubleDot]r weiter Details verweisen wir auf \
die GNU General Public License.\n\nEine Kopie der Lizenz sollten Sie mit dem Programm erhalten haben, \
falls nicht, siehe <http://www.gnu.org/licenses/>.", ToString[ Date[][[1]]]];
    translate[ "GoalProve", lang] = "Beweisziel";
	translate[ "group/ungroup", lang] = "Gruppieren / Gruppierung aufheben";
    translate[ "GVARCONDTooltip", lang] = "Global universal gebundene Variable mit Bedingung";   	
    translate[ "GVARTooltip", lang] = "Global universal gebundene Variable";   	

    translate[ "hide proof", lang] = "Beweis ausblenden";
    translate[ "hideProofProgress", lang] = "Durch Klicken wird der Beweis ausgeblendet. Das Fenster nicht schlie\[SZ]en, da es dann nicht mehr wieder ge\[ODoubleDot]ffnet werden kann.";

    translate[ "IMPL2", lang] = "\!\(\*FormBox[FrameBox[\"links\"], SelectionPlaceholder]\) impliziert \!\(\*FormBox[FrameBox[\"rechts\"], SelectionPlaceholder]\)";   	
    translate[ "in place", lang] = "an der Stelle";
    translate[ "input", lang] = "Eingabe";
	translate[ "instantiate later", lang] = "Sp\[ADoubleDot]ter instanzieren";
	translate[ "instVar", lang] = "Zu instanzierende Variable";
	translate[ "interactiveInstantiate", lang] = "Quantoren interaktiv instanzieren";
	translate[ "interactiveNewProofSitFilter", lang] = "Neue Beweissituationen interaktiv instanzieren";
	translate[ "interactiveProofSitSel", lang] = "N\[ADoubleDot]chste Beweissituation interaktiv w\[ADoubleDot]hlen";
	translate[ "invalidExpr", lang] = "Der eingegebene Ausdruck ist ung\[UDoubleDot]ltig, da sein Sequence-Typ inkorrekt ist oder nicht bestimmt werden kann.";
	translate[ "invalidQuCondition", lang] = "Der Quantor \"``\" kann nicht mit einer zus\[ADoubleDot]tzlichen Bedingung verwendet werden.";
	translate[ "invalidQuRange", lang] = "Der Quantor \"`1`\" kann nicht zusammen mit dem Variablenbereich `2` verwendet werden.";
	translate[ "invalidQuSubscript", lang] = "Der Quantor \"``\" kann kein Subskript haben.";
	translate[ "invalidQuVarNum", lang] = "Der Quantor \"``\" kann nicht mit Multi-Variablenbereichen verwendet werden.";
	translate[ "invalidRange", lang] = "Jede gebundene Variable darf nur einmal unter dem Quantor vorkommen, der sie bindet; Diese Bedingung wird verletzt von ``.";
    
    translate[ "KBcomp", lang] = "In der Berechnung verwendetes Wissen";
    translate[ "KBprove", lang] = "Im Beweis verwendetes Wissen";
	translate[ "Keyword", lang] = "Schl\[UDoubleDot]sselwort";

    translate[ "LET", lang] = "Sei \!\(\*FormBox[FrameBox[\"a\"], Placeholder]\) kurz f\[UDoubleDot]r \!\(\*FormBox[FrameBox[\"x\"], Placeholder]\) in \!\(\*FormBox[FrameBox[\"A\"], SelectionPlaceholder]\)";
    translate[ "LETTooltip", lang] = "a \[Ellipsis] Variable als Abk\[UDoubleDot]rzung\nx \[Ellipsis] abgek\[UDoubleDot]rzter Ausdruck\nA \[Ellipsis] Ausdruck mit a anstelle von x";   	
    translate[ "Logic", lang] = "Logik";

    translate[ "Mark favourite", lang] := "Als Favorit markieren.\nDieser Beweis wird beim Anklicken von \"" <> translate[ "ShowSimplifiedProof", lang] <> "\" angezeigt";
    translate[ "more", lang] = "mehr \[Ellipsis]";

	translate[ "nA", lang] = "nicht verf\[UDoubleDot]gbar";
	translate[ "New", lang] = "Neu";
    translate[ "noArchName", lang] = "Archiv hat keinen Namen. Archivinhalt pr\[UDoubleDot]fen";
	translate[ "noGoal", lang] = "Selektieren Sie eine gesamte Zelle (Zellklammer), die das Beweisziel enth\[ADoubleDot]lt";
	translate[ "noKB", lang] = "Kein Wissen gew\[ADoubleDot]hlt";
    translate[ "noKnowl", lang] = "Kein Wissen verf\[UDoubleDot]gbar";
    translate[ "noNB", lang] = "Keine Notebookdatei verf\[UDoubleDot]gbar";
	translate[ "noRoot", lang] = "Wurzel des Baumes kann nicht identifiziert werden";
	translate[ "noRules", lang] = "Keine regeln gefunden";
    translate[ "Notebooks", lang] = "Notebooks";
	translate[ "notEval", lang] = "Aussage derzeit nicht evaluiert. Zum Auswerten klicken.";
    translate[ "NOT", lang] = "nicht \!\(\*FormBox[FrameBox[\"A\"], SelectionPlaceholder]\)";	
    translate[ "NOTTooltip", lang] = "A \[Ellipsis] Aussage\nlogische Verneinung";
    translate[ "notUniqueLabel", lang] = "Das Notebook `` enth\[ADoubleDot]lt mehrdeutige Labels: ``\n\nDies ist nur eine Warnung, es kann fortgesetzt werden,\nallerdings kann es zu Verwechslungen bei\nReferenzen in diesem Notebook kommen.";

	translate[ "OK", lang] = "OK";
	translate[ "OKnext", lang] = "OK, n\[ADoubleDot]chstes \[Ellipsis]";
    translate[ "OmDoc", lang] = "OmDoc";   	
	translate[ "open", lang] = "alle offen";
	translate[ "Open", lang] = "\[ODoubleDot]ffnen";
	translate[ "open proof situation", lang] = "Offene Beweissituation";
	translate[ "Operators", lang] = "Operatoren";
    translate[ "optimal size", lang] = "optimale Gr\[ODoubleDot]\[SZ]e";
    translate[ "OR2", lang] = "\!\(\*FormBox[FrameBox[\"links\"], SelectionPlaceholder]\) oder \!\(\*FormBox[FrameBox[\"rechts\"], SelectionPlaceholder]\)";   	
    translate[ "OR3", lang] = "\!\(\*FormBox[FrameBox[\"e1\"], SelectionPlaceholder]\) oder \[Ellipsis] oder \!\(\*FormBox[FrameBox[\"en\"], SelectionPlaceholder]\)";
    translate[ "OVEROP", lang] = "\[UDoubleDot]berskript-Operator";
    translate[ "OVERSUBOP", lang] = "\[UDoubleDot]ber- und subskript-Operator";

	translate[ "pending", lang] = "unerledigt";
	translate[ "pInteractive", lang] = "Interaktives Beweisen";
	translate[ "predArgN", lang] = "Pr\[ADoubleDot]dikat \"`1`\" wird auf `2` Argumente angewendet; H\[ODoubleDot]chstens `3` Argumente erwartet.";
	translate[ "preferences last saved", lang] = "Einstellungen zuletzt gesichert";
    translate[ "Programming", lang] = "Mathematica Programmierung";
	translate[ "proofCellStatus", lang] = "Beweiszellen";
	translate[ "proofFindTime", lang] = "Zeit zum Finden des Beweises";
    translate[ "Proof", lang] = "Beweis";
    translate[ "Proof of", lang] = "Beweis von";
	translate[ "proofOutput", lang] = "Beweis Ausgabe";
	translate[ "proofSimpTime", lang] = "Zeit zum Vereinfachen des Beweises";
	translate[ "proved", lang] = "bewiesen";
	translate[ "prove", lang] = "Beweisen!";
	translate[ "pRules", lang] = "Beweisregeln";
	translate[ "pRulesSetup", lang] = "Beweisregel-Einstellungen";
	translate[ "pSimp", lang] = "Beweisvereinfachung";
	translate[ "pStrat", lang] = "Beweisstrategie";

    translate[ "QUANT1Tooltip", lang] = "rg \[Ellipsis] Laufbereich der gebundenen Variablen\nexpr \[Ellipsis] Ausdruck";   	
    translate[ "QUANT2Tooltip", lang] = "rg \[Ellipsis] Laufbereich der gebundenen Variablen\ncond \[Ellipsis] Bedingung\nexpr \[Ellipsis] Ausdruck";
    translate[ "quote/unquote", lang] = "In Anf\[UDoubleDot]hrung setzen / Anf\[UDoubleDot]hrung aufheben";

	translate[ "replaceExistProof", lang] = "Bestehenden Beweis ersetzen";
    translate[ "ResetBui", lang] = "Built-ins zur\[UDoubleDot]cksetzen";
	translate[ "RestoreDefaults", lang] = "Auf Standardwerte setzen";
    translate[ "RestoreSettings", lang] = "Einstellungen zur\[UDoubleDot]cksetzen";
    translate[ "restoreSettingsBeforeComp", lang] = "Vor jeder Berechnung die Einstellungen zur\[UDoubleDot]cksetzen";
    translate[ "RestoreSettingsLong", lang] = "Einstellungen wirklich auf die Werte zur\[UDoubleDot]cksetzen, die bei letzmaliger Ausf\[UDoubleDot]hrung dieser Aktion verwendet wurden?";
    translate[ "result", lang] = "Resultat";
    translate[ "resyncGlobal", lang] = "Re-sync globals";
    translate[ "resyncGlobalTooltip", lang] = "Globale im aktiven Notebook neu synchronisieren. Kann nach manuellem Bearbeiten im Notebook notwendig werden.";
	translate[ "ruleActive", lang] = "Aktivieren/Deaktivieren der Beweisregel";
	translate[ "rulePriority", lang] = "Priorit\[ADoubleDot]t der Regel ist eine ganze Zahl zwischen 1 und 100. Niedriger Wert bedeutet hohe Priorit\[ADoubleDot]t";

	translate[ "save current settings", lang] = "Aktuelle Werte speichern";
	translate[ "sDepth", lang] = "Suchtiefe";
	translate[ "selBui", lang] = "Gew\[ADoubleDot]hlte Built-ins";
	translate[ "selectedRules",lang] = "Gew\[ADoubleDot]hlte Regeln";
	translate[ "selGoal", lang] = "Gew\[ADoubleDot]hltes Beweisziel";
	translate[ "selKB", lang] = "Gew\[ADoubleDot]hlteWissensbasis";
	translate[ "selProver", lang] = "Gew\[ADoubleDot]hlte Beweismethode";
    translate[ "Sets", lang] = "Mengen";
	translate[ "ShowAll", lang] = "Alles anzeigen";
    translate[ "ShowComputation", lang] = "Berechnung anzeigen";
    translate[ "ShowFullProof", lang] = "Vollst\[ADoubleDot]ndigen Beweis anzeigen";
    translate[ "ShowProof", lang] = "Beweis anzeigen";
    translate[ "showProofProgress", lang] = "Bisherigen Beweis anzeigen";
    translate[ "ShowSimplifiedProof", lang] = "Vereinfachten Beweis anzeigen";
    translate[ "SINGLEOP", lang] = "einfacher Operator";
	translate[ "sLimits", lang] = "Grenzen der Beweissuche";
	translate[ "statistics", lang] = "Statistik";
	translate[ "sTime", lang] = "Suchzeit";
    translate[ "SUBOP", lang] = "subskript-Operator";
    translate[ "SUBSUPEROP", lang] = "sub- und superskript-Operator";
    translate[ "SUPEROP", lang] = "superskript-Operator";

    translate[ "tcComputeTabBuiltinTabLabel", lang] = "built-in";
    translate[ "tcComputeTabKBTabLabel", lang] = "wissen";
    translate[ "tcComputeTabLabel", lang] = "Berechnen";
    translate[ "tcComputeTabNewTabLabel", lang] = "neu";
    translate[ "tcComputeTabSetupTabLabel", lang] = "einstellungen";
    translate[ "tcInformTabAboutTabLabel", lang] = "\[UDoubleDot]ber";
    translate[ "tcInformTabLabel", lang] = "informieren";
    translate[ "tcInformTabLicenseTabLabel", lang] = "lizenz";
    translate[ "tcInformTabSetupTabLabel", lang] = "einstellungen";   	
    translate[ "tcLangTabArchTabButtonCloseLabel", lang] = "Ende";
    translate[ "tcLangTabArchTabButtonInfoLabel", lang] = "Archiv Info";
    translate[ "tcLangTabArchTabButtonLoadLabel", lang] = "Laden";
    translate[ "tcLangTabArchTabButtonMakeLabel", lang] = "Notebook \[RightArrow] Archiv";
    translate[ "tcLangTabArchTabButtonSelectLabel", lang] = "Archive ausw\[ADoubleDot]hlen \[Ellipsis]";
    translate[ "tcLangTabArchTabNoArchSel", lang] = "Keine Archive ausgew\[ADoubleDot]hlt";
    translate[ "tcLangTabArchTabSectionCreate", lang] = "Archive erstellen";
    translate[ "tcLangTabArchTabSectionExport", lang] = "Archive exportieren";
    translate[ "tcLangTabArchTabSectionLoad", lang] = "Archive laden";
	translate[ "tcPrefAppearColorSchemes", lang] = "Farbschemata";
	translate[ "tcPrefAppear", lang] = "Erscheinung";
	translate[ "tcPrefAppearSuppressWelcome", lang] = "Willkommensschirm nicht anzeigen";
	translate[ "tcPrefAppearWelcome", lang] = "Willkommensschirm";
	translate[ "tcPrefArchiveDir", lang] = "Archivverzeichnis";
	translate[ "tcPrefLanguage", lang] = "Sprache";
    translate[ "tcProveTabBuiltinTabLabel", lang] = "built-in";
    translate[ "tcProveTabGoalTabLabel", lang] = "ziel";
    translate[ "tcProveTabInspectTabLabel", lang] = "pr\[UDoubleDot]fen";
    translate[ "tcProveTabKBTabLabel", lang] = "wissen";
    translate[ "tcProveTabLabel", lang] = "Beweisen";
    translate[ "tcProveTabProverTabLabel", lang] = "beweiser";
    translate[ "tcProveTabSubmitTabLabel", lang] = "absenden";
    translate[ "tcSessionTabLabel", lang] = "vorbereiten";
    translate[ "tcSessTabArchTabLabel", lang] = "archive";
    translate[ "tcSessTabComposeTabLabel", lang] = "erstellen";
    translate[ "tcSessTabEnvTabButtonAlgLabel", lang] = "Algorithmus";
    translate[ "tcSessTabEnvTabButtonAllDeclLabel", lang] = "Alle Globale";
    translate[ "tcSessTabEnvTabButtonAllFormLabel", lang] = "Alle Aussagen";
    translate[ "tcSessTabEnvTabButtonCorLabel", lang] = "Korollar";
    translate[ "tcSessTabEnvTabButtonDeclLabel", lang] = "Globale identifizieren";
    translate[ "tcSessTabEnvTabButtonDefLabel", lang] = "Definition";
    translate[ "tcSessTabEnvTabButtonExmLabel", lang] = "Beispiel";
    translate[ "tcSessTabEnvTabButtonLmaLabel", lang] = "Lemma";
    translate[ "tcSessTabEnvTabButtonPrpLabel", lang] = "Proposition";
    translate[ "tcSessTabEnvTabButtonThmLabel", lang] = "Theorem";
    translate[ "tcSessTabInspectTabLabel", lang] = "pr\[UDoubleDot]fen";
    translate[ "tcSessTabMathTabBSform", lang] = "formal";
    translate[ "tcSessTabMathTabBS", lang] = "Button-Stil";   	
    translate[ "tcSessTabMathTabBSnat", lang] = "nat\[UDoubleDot]rlich";   	
    translate[ "tcSolveTabBuiltinTabLabel", lang] = "built-in";
    translate[ "tcSolveTabKBTabLabel", lang] = "wissen";
    translate[ "tcSolveTabLabel", lang] = "L\[ODoubleDot]sen";
    translate[ "tcSolveTabSetupTabLabel", lang] = "einstellungen";
	translate[ "Theorema Commander", lang] = "Theorema Commander";
    translate[ "Theorema Environment", lang] = "Theorema Umgebung";
	translate[ "tooltipButtonGroupUngroup", lang] = "Den ausgew\[ADoubleDot]hlten Ausdruck gruppieren. Taste \[ShiftKey] dr\[UDoubleDot]cken, um eine Gruppierugn aufzuheben.";
    translate[ "tooltipButtonNoParen", lang] = "\nTastaturk\[UDoubleDot]rzel";   	
    translate[ "tooltipButtonParen", lang] = "\nTaste \[ShiftKey] dr\[UDoubleDot]cken, um die Klammern wegzulassen\nTastaturk\[UDoubleDot]rzel";
    translate[ "tooltipButtonGroupUngroup", lang] = "Den ausgew\[ADoubleDot]hlten Ausdruck in Anf\[UDoubleDot]hrung setzen. Taste \[ShiftKey] dr\[UDoubleDot]cken, um eine Anf\[UDoubleDot]hrung aufzuheben.";
    translate[ "Trace", lang] = "Berechnung verfolgen";
    translate[ "traceUserDef", lang] = "Benutzer-Definitionen verfolgen";
    translate[ "Tuples", lang] = "Tupel";

    translate[ "UNDEROVEROP", lang] = "unter- und \[UDoubleDot]berskript-Operator";
	translate[ "unknown proof node", lang] = "Unbekannter Beweisknoten";
	translate[ "Updating tags", lang] = "Notebook ``: Aktualisiere Source Tags \[Ellipsis]";

	translate[ "Virtual Keyboard", lang] = "Virtuelle Tastatur";

    translate[ "zoom in", lang] = "hineinzoomen";
    translate[ "zoom out", lang] = "herauszoomen";
    		
    translate[ "?", lang] = "?";
	translate[ "[]", lang] = "eckig geklammerter Ausdruck";
	translate[ "[[]]", lang] = "doppelt eckig geklammerter Ausdruck";
	translate[ "[|]", lang] = "schr\[ADoubleDot]g mit Balken geklammerter Ausdruck";
	translate[ "<>", lang] = "spitz geklammerter Ausdruck";
	translate[ "<<>>", lang] = "doppelt spitz geklammerter Ausdruck";
	translate[ "<|>", lang] = "spitz mit Balken geklammerter Ausdruck";
	translate[ "<.>", lang] = "spitz mit Punkt geklammerter Ausdruck";
	translate[ "<c>", lang] = "geschwungen-spitz geklammerter Ausdruck";
	translate[ "{}", lang] = "geschweift geklammerter Ausdruck";
	translate[ "{{}}", lang] = "doppelt geschweift geklammerter Ausdruck";
	translate[ "()", lang] = "rund geklammerter Ausdruck";
	translate[ "(())", lang] = "doppelt rund geklammerter Ausdruck";
	translate[ "(|)", lang] = "rund mit Balken geklammerter Ausdruck";
	translate[ "\[VerticalEllipsis]\[VerticalEllipsis]", lang] = "Folge von Ausdr\[UDoubleDot]cken";

(* UNTRANSLATED *)

]
