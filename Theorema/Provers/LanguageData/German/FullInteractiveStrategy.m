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
 
     If you modify this file, then insert the new translation in correct alphabetical 
     order (case-insensitive).

     ALSO, YOU MUST add a corresponding entry in the respective file for each other language, 
     either
      1) in the respective section named "UNTRANSLATED", note there are several such sections
         in the file (in case you cannot or do not want to provide a translation) or
      2) in correct alphabetical order (case-insensitive) in case you immediately provide 
         a translation.
      
   *********************************************************************************************
   -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- IMPORTANT -- 
   *********************************************************************************************
 *)
 
(* ::Section:: *)
(* Public Declaration Part: executes in Theorema`Provers` *)

With[ {lang = "German"},
(* TRANSLATED *)

(* UNTRANSLATED *)
	MessageName[ fullInteractiveStrategy, "usage", lang] = "The fully-interactive strategy allows the user to specify which inference rule should be applied in which way, i.e. gives the user full control over the proof search.";
	
	MessageName[ $FullInteractiveStrat$removeKB, "usage", lang] = "Remove formulas from the knowledge base";
	MessageName[ $FullInteractiveStrat$voidStep, "usage", lang] = "void";

] (* With *)


(* ::Section:: *)
(* Private Implementation Part: executes in Theorema`Provers`Private` *)

Begin["`Private`"]

With[ {lang = "German"},
(* TRANSLATED *)

(* UNTRANSLATED *)
	translate[ "adjustProver", lang] = "Adjust prover settings \[Ellipsis]";
	translate[ "adjustThresholds", lang] = "Adjust priority thresholds \[Ellipsis]";
	
	translate[ "changeProverSettings", lang] = "Change Prover Settings";
	translate[ "choosePS", lang] = "Choose Proof Situation";
	translate[ "choosePSMenuItem", lang] = "Choose situation \[Ellipsis]";
	translate[ "chooseSteps", lang] = "Choose Next Steps";
	translate[ "changeThresholds", lang] = "Change Priority Thresholds";
	translate[ "curPS", lang] = "Current Proof Situation";
	translate[ "curPO", lang] = "Current Proof Object";
	
	translate[ "debugging", lang] = "Debugging";
	
	translate[ "failed", lang] = " failed.";
	translate[ "failure", lang] = "Failure.";
	translate[ "Full-Interactive Strategy", lang] = "Fully-Interactive Strategy";
	
	translate[ "goal", lang] = "Goal";
	translate[ "goalText", lang] = "We have to prove:";
	
	translate[ "hiddenKnowledge", lang] = "Hidden Knowledge";
	
	translate[ "inferenceRules", lang] = "Inference Rules";
	translate[ "inspectPO", lang] = "Inspect proof object \[Ellipsis]";
	translate[ "inspectRewriteRules", lang] = "Inspect rewrite rules \[Ellipsis]";
	translate[ "invalidRule", lang] = "The requested inference rule is invalid.";
	
	translate[ "kb", lang] = "Knowledge Base";
	translate[ "kbNoText", lang] = "with no assumptions.";
	translate[ "kbText", lang] = "under the assumptions:";
	
	translate[ "makeInfStep", lang] = "Do an inference step.";
	
	translate[ "noApplicableRule", lang] = "The requested inference rule could not be applied.";
	translate[ "noKnowledge"] = "No knowledge available";
	translate[ "noNewPS", lang] = "No new proof situation chosen.";
	translate[ "noNewSteps", lang] = "No proof step was chosen.";
	translate[ "noPSFound", lang] = "No proof situation found.";
	
	translate[ "openPS", lang] = "Open proof situation";
	
	translate[ "PO", lang] = "Proof Object";
	translate[ "poToFile", lang] = "Proof object \[Rule] file";
	translate[ "proofSearch", lang] = "Proof Search";
	translate[ "proveLaterAuto", lang] = "Prove later automatically";
	translate[ "proveNowAuto", lang] = "Prove now automatically";
	translate[ "ps", lang] = "Proof Situation";
	translate[ "psNotAutomatically", lang] = "Proof situation could not be transformed automatically.";
	translate[ "psToFile", lang] = "Proof situation \[Rule] file";
	
	translate[ "rewriteRules", lang] = "Rewrite Rules";
	translate[ "ruleFailed", lang] = "Rule \"``\" was tried without success.";
	
	translate[ "saveProof", lang] = "Save proof";
	translate[ "settings", lang] = "Settings";
	translate[ "settingsChanged", lang] = "Settings changed.";
	translate[ "settingsNotChanged", lang] = "No settings changed.";
	translate[ "showHiddenKnowledge", lang] = "Show hidden knowledge \[Ellipsis]";
	translate[ "subproof", lang] = "Subproof";
	translate[ "succeeded", lang] = " already succeeded.";
	
	translate[ "thresholdsAuto", lang] = "Automatic Thresholds";
	translate[ "thresholdsChanged", lang] = "Thresholds changed.";
	translate[ "thresholdInter", lang] = "Interactive Threshold";
	translate[ "thresholdsNotChanged", lang] = "No thresholds changed.";
	translate[ "tryAgain", lang] = "Try again";
	translate[ "ttApplyRule", lang] = "Apply an inference rule";
	translate[ "ttCancel", lang] = "Cancel";
	translate[ "ttDebugging", lang] = "Tools for debugging";
	translate[ "ttGoNext", lang] = "Go to next";
	translate[ "ttGoPrev", lang] = "Go to previous";
	translate[ "ttMakeAlternatives", lang] = "Choose whether to create an OR-node or not";
	translate[ "ttOK", lang] = "Accept";
	translate[ "ttProofSearch", lang] = "Continue with a different proof situation";
	translate[ "ttSettings", lang] = "Change settings";
	
	proofStepText[ $FullInteractiveStrat$removeKB|$FullInteractiveStrat$voidStep, lang, ___] := {};
	
] (* With *)

End[]