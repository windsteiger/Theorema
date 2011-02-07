(* 
Theorema editor: W. Windsteiger
Author(s):       W. Windsteiger

What is the purpose of the Theorema editor? Read more in /ProgrammersDoc/Guidelines.nb#1871658360
*)

BeginPackage["Theorema`Language`Parser`"];


Begin["`Private`"]

	
(*
MakeTheoremaExpression[RowBox[{UnderscriptBox["\[ForAll]",rng_],form_}],f_]:=
With[({r=ToHoldingRangeBox[rng]}),
FormBox["MakeTheoremaExpression","InputForm"][RowBox[{"\!\(InputForm`Theorema`Language`Syntax`Parser`Private`\[LeftPointer]VARIABLES\[RightPointer]\)","[",(RowBox[{r,",",RowBox[{"ForAll","[",RowBox[{r,",","True",",",form}],"]"}]}]),"]"}],f]];

MakeBoxes[\[Trademark]ForAll[(\[Bullet]range|\[Bullet]\[Bullet]range)[rng___],True,op_[x___]],f_]:= 
RowBox[{UnderscriptBox["\[ForAll]",MakeRangeBoxes[\[Bullet]\[Bullet]range[rng],f]],MakeBoxes[op[x],f]}];

$TmaFreshNameKeywordPatterns=Alternatives[FormBox["\\[LeftPointer]LF\\[RightPointer]","InputForm"],\[LeftPointer]NEW\[RightPointer],\[LeftPointer]USED\[RightPointer],\[Bullet]range];

QuotedFreshNames[Hold[h_[e___]]]/;MatchQ[h,$TmaFreshNameKeywordPatterns]:=
(Hold[h[e]]/.MarkerTranslations\[RegisteredTrademark])//.$TmaOperatorTranslations;

QuotedFreshNames[Hold[FormBox["\\[LeftPointer]FRESHNAMES\\[RightPointer]","InputForm"][expr__]]]:=
Hold[expr]//.$TmaOperatorTranslations;

QuotedFreshNames[Hold[h_[e___]]]:=
ApplyHold[
QuotedFreshNames[Hold[h]],
QuotedFreshNames[Hold[e]]];

QuotedFreshNames[Hold[f_,t__]]:=
Join[
QuotedFreshNames[Hold[f]],
QuotedFreshNames[Hold[t]]];

QuotedFreshNames[Hold[]]:=Hold[]

QuotedFreshNames[Hold[e_]]:=Hold[e]

$TmaFreshNameProgKeywordPatterns=Alternatives[\[Bullet]newProofSits];

FreshNamesProg[Hold[h_[e___]]]/;MatchQ[h,$TmaFreshNameProgKeywordPatterns]:=
Hold[h[e]]//.TmaProgTranslations\[RegisteredTrademark];

FreshNamesProg[Hold[h_[e___]]]:=
ApplyHold[
FreshNamesProg[Hold[h]],
FreshNamesProg[Hold[e]]];

FreshNamesProg[Hold[f_,t__]]:=
Join[
FreshNamesProg[Hold[f]],
FreshNamesProg[Hold[t]]];

FreshNamesProg[Hold[]]:=Hold[]

FreshNamesProg[Hold[e_]]:=Hold[e]

MarkBoundVariables[Hold[FormBox["\\[LeftPointer]VARIABLES\\[RightPointer]","InputForm"][vlist_List,expr_]]]:=(Module[{s=Map[Rule[#,\[Bullet]var[#]]&,Select[vlist,IsIdentifier]]},
ReplaceAllExcept[MarkBoundVariables[Hold[expr]],s,{\[Bullet]seq,\[Bullet]var,\[Bullet]new,\[Bullet]fix}]])

MarkBoundVariables[Hold[FormBox["\\[LeftPointer]VARIABLES\\[RightPointer]","InputForm"][r:(_\[Bullet]range|_\[Bullet]\[Bullet]range),expr_]]]:=
MarkBoundVariables[
Hold[FormBox["\\[LeftPointer]VARIABLES\\[RightPointer]","InputForm"][#,expr]]&[(SpecifiedVariables[r])]]

MarkBoundVariables[Hold[FormBox["\\[LeftPointer]VARIABLES\\[RightPointer]","InputForm"][v_,expr_]]]:=MarkBoundVariables[Hold[FormBox["\\[LeftPointer]VARIABLES\\[RightPointer]","InputForm"][{v},expr]]]

MarkBoundVariables[Hold[h_[e___]]]:=ApplyHold[
MarkBoundVariables[Hold[h]],
MarkBoundVariables[Hold[e]]]

MarkBoundVariables[Hold[f_,t__]]:=Join[
MarkBoundVariables[Hold[f]],
MarkBoundVariables[Hold[t]]]

MarkBoundVariables[Hold[]]:=Hold[]

MarkBoundVariables[Hold[e_]]:=Hold[e]

MarkBoundVariables[e_]/;PrintMessage[Theorema::unexpected,e,MarkBoundVariables]:=Null

MarkVariables[expr_Hold]:=MarkBoundVariables[expr]

SetAttributes[\[Bullet]\[Bullet]range,HoldAll];

\[Bullet]range::usage="\[Bullet]range[range1,...] represents a range specification (mostly for variables). One single \[Bullet]range-object can contain more than one range specification.";

\[Bullet]\[Bullet]range::usage="\[Bullet]\[Bullet]range[range1,...] represents a range specification (mostly for variables). One single \[Bullet]\[Bullet]range-object can contain more than one range specification.";

ToRangeBox[x_]/;PrintMessage[ToRangeBox::usage]:=Null

ToHoldingRangeBox::usage="ToHoldingRangeBox[box] produces the range specification of a quantifier (with all the necessary attributes).";

ToTMRangeBox::usage="ToTMRangeBox[box] produces the range specification of a quantifier (without any attributes).";

ToPreliminaryRangeBox[s_]:=RowBox[{"\[Bullet]range","[",MakeRangeSequence[s],"]"}]

ToHoldingRangeBox[x_]:=ToPreliminaryRangeBox[x]/.rangeToHoldingRange

ToTMRangeBox[x_]:=ToPreliminaryRangeBox[x]/.holdingRangeToRange

MakeRangeSequence::usage="MakeRangeSequence[boxes]] reads the individual range specifications.";

MakeRangeSequence[GridBox[{{s_},r__}]]:=Sequence[MakeRangeSequence[s],",",MakeRangeSequence[GridBox[{r}]]]

MakeRangeSequence[GridBox[{{s_}}]]:=MakeRangeSequence[s]

MakeRangeSequence[RowBox[{"(",x_,")"}]]:=x/;$SessionIdentifier==="Prog"

MakeRangeSequence[RowBox[{"(",x_,")"}]]:=MakeRangeSequence[x]

SetAttributes[\[Bullet]\[Bullet]predRange,HoldFirst];

\[Bullet]predRange::usage="\[Bullet]predRange[x,pred] denotes that the variable `x` statisfies the unary predicate `pred`.";

\[Bullet]\[Bullet]predRange::usage="\[Bullet]\[Bullet]predRange[x,pred] denotes that the variable `x` statisfies the unary predicate `pred`.";

MakeRangeSequence[RowBox[{pred_,"[",x_,"]"}]]:=RowBox[{"\[Bullet]predRange","[",x,",",pred,"]"}]

MakeRangeSequence[RowBox[{pred_,"[",RowBox[{x_}],"]"}]]:=RowBox[{"\[Bullet]predRange","[",x,",",pred,"]"}]

MakeRangeSequence[RowBox[{pred_,"[",RowBox[{x_,",",y__}],"]"}]]:=Sequence[RowBox[{"\[Bullet]predRange","[",x,",",pred,"]"}],",",MakeRangeSequence[RowBox[{pred,"[",RowBox[{y}],"]"}]]]

SetAttributes[\[Bullet]\[Bullet]setRange,HoldFirst];

\[Bullet]setRange::usage="\[Bullet]setRange[x,s] denotes that the variable `x` ranges over the set `s`.";

\[Bullet]\[Bullet]setRange::usage="\[Bullet]\[Bullet]setRange[x,s] denotes that the variable `x` ranges over the set `s`.";

MakeRangeSequence[RowBox[{i_, ",", j__,",",RowBox[{k_, "\[Element]", s_}]}]]:=Sequence[RowBox[{"\[Bullet]setRange","[",i,",",s,"]"}],",",MakeRangeSequence[RowBox[{j,",",RowBox[{k, "\[Element]", s}]}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_, "\[Element]", s_}]}]]:=Sequence[RowBox[{"\[Bullet]setRange","[",j,",",s,"]"}],",",RowBox[{"\[Bullet]setRange","[",k,",",s,"]"}]]

MakeRangeSequence[RowBox[{k_,"\[Element]",s_}]]:=RowBox[{"\[Bullet]setRange","[",k,",",s,"]"}]

SetAttributes[\[Bullet]\[Bullet]integerRange,HoldFirst];

\[Bullet]integerRange::usage="\[Bullet]integerRange[i,lower,upper] denotes that the variable `i` ranges over all integers from `lower` to `upper`.";

\[Bullet]\[Bullet]integerRange::usage="\[Bullet]\[Bullet]integerRange[i,lower,upper] denotes that the variable `i` ranges over all integers from `lower` to `upper`.";

MakeRangeSequence[RowBox[{i_, ",", j__,",",n      RowBox[{k_, "=", lower_}], ",", "\[Ellipsis]", ",", upper_}]]:=Sequence[RowBox[{"\[Bullet]integerRange","[",i,",",lower,",",upper,"]"}],",",MakeRangeSequence[RowBox[{j,",",n      RowBox[{k, "=", lower}], ",", "\[Ellipsis]", ",", upper}]]]

MakeRangeSequence[RowBox[{j_, ",", n      RowBox[{k_, "=", lower_}], ",", "\[Ellipsis]", ",", upper_}]]:=Sequence[RowBox[{"\[Bullet]integerRange","[",j,",",lower,",",upper,"]"}],",",RowBox[{"\[Bullet]integerRange","[",k,",",lower,",",upper,"]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,"=",lower_}],",","\[Ellipsis]",",",upper_}]]:=n	RowBox[{"\[Bullet]integerRange","[",k,",",lower,",",upper,"]"}]

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,"=",lower_}],",","\[Ellipsis]"}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",i,",",lower,",","\[Infinity]","]"}],",",MakeRangeSequence[RowBox[{j,",",RowBox[{k,"=",lower}],",","\[Ellipsis]"}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,"=",lower_}],",","\[Ellipsis]"}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",j,",",lower,",","\[Infinity]","]"}],",",RowBox[{"\[Bullet]integerRange","[",k,",",lower,",","\[Infinity]","]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,"=",lower_}],",","\[Ellipsis]"}]]:=n	RowBox[{"\[Bullet]integerRange","[",k,",",lower,",","\[Infinity]","]"}]

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,"=","\[Ellipsis]"}],",",upper_}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",i,",",RowBox[{"-", "\[Infinity]"}],",",upper,"]"}],",",MakeRangeSequence[RowBox[{j,",",RowBox[{k,"=","\[Ellipsis]"}],",",upper}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,"=","\[Ellipsis]"}],",",upper_}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",j,",",RowBox[{"-", "\[Infinity]"}],",",upper,"]"}],",",RowBox[{"\[Bullet]integerRange","[",k,",",RowBox[{"-", "\[Infinity]"}],",",upper,"]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,"=","\[Ellipsis]"}],",",upper_}]]:=n	RowBox[{"\[Bullet]integerRange","[",k,",",RowBox[{"-", "\[Infinity]"}],",",upper,"]"}]

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,"=","\[Ellipsis]"}]}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",i,",",RowBox[{"-", "\[Infinity]"}],",","\[Infinity]","]"}],",",nMakeRangeSequence[RowBox[{j,",",RowBox[{k,"=","\[Ellipsis]"}]}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,"=","\[Ellipsis]"}]}]]:=n	Sequence[RowBox[{"\[Bullet]integerRange","[",j,",",RowBox[{"-", "\[Infinity]"}],",","\[Infinity]","]"}],",",n	RowBox[{"\[Bullet]integerRange","[",k,",",RowBox[{"-", "\[Infinity]"}],",","\[Infinity]","]"}]]

MakeRangeSequence[RowBox[{k_,"=","\[Ellipsis]"}]]:=n	RowBox[{"\[Bullet]integerRange","[",k,",",RowBox[{"-", "\[Infinity]"}],",","\[Infinity]","]"}]

SetAttributes[\[Bullet]\[Bullet]domainRange,HoldFirst];

\[Bullet]domainRange::usage="\[Bullet]domainRange[i,domain,lower,upper] denotes that the variable `i` ranges over all elements of the enumerable domain `domain` from `lower` to `upper`.";

\[Bullet]\[Bullet]domainRange::usage="\[Bullet]\[Bullet]domainRange[i,domain,lower,upper] denotes that the variable `i` ranges over all elements of the enumerable domain `domain` from `lower` to `upper`.";

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","\[Ellipsis]",",",upper_}]]:=Sequence[RowBox[{"\[Bullet]domainRange","[",i,",",domain,",",lower,",",upper,"]"}],",",MakeRangeSequence[RowBox[{j,",",RowBox[{k,UnderscriptBox["=",domain],lower}],",","\[Ellipsis]",",",upper}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","\[Ellipsis]",",",upper_}]]:=Sequence[RowBox[{"\[Bullet]domainRange","[",j,",",domain,",",lower,",",upper,"]"}],",",RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",lower,",",upper,"]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","\[Ellipsis]",",",upper_}]]:=(DeclareUnderscriptDomain[domain];RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",lower,",",upper,"]"}])

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","\[Ellipsis]"}]]:=Sequence[n		RowBox[{"\[Bullet]domainRange","[",i,",",domain,",",lower,",",RowBox[{domain,"[","Last","]"}],"]"}],",",n		MakeRangeSequence[RowBox[{j,",",RowBox[{k,UnderscriptBox["=",domain],lower}],",","\[Ellipsis]"}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","\[Ellipsis]"}]]:=Sequence[n		RowBox[{"\[Bullet]domainRange","[",j,",",domain,",",lower,",",RowBox[{domain,"[","Last","]"}],"]"}],",",n		RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",lower,",",RowBox[{domain,"[","Last","]"}],"]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,UnderscriptBox["=",domain_],lower_}],",","\[Ellipsis]"}]]:=(DeclareUnderscriptDomain[domain];RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",lower,",",RowBox[{domain,"[","Last","]"}],"]"}])

MakeRangeSequence[n		RowBox[{i_,",",j__,",",RowBox[{k_,UnderscriptBox["=",domain_],"\[Ellipsis]"}],",",upper_}]]:=Sequence[n		RowBox[{"\[Bullet]domainRange","[",i,",",domain,",",RowBox[{domain,"[","First","]"}],",",upper,"]"}],",",MakeRangeSequence[n		RowBox[{j,",",RowBox[{k,UnderscriptBox["=",domain],"\[Ellipsis]"}],",",upper}]]]

MakeRangeSequence[n		RowBox[{j_,",",RowBox[{k_,UnderscriptBox["=",domain_],"\[Ellipsis]"}],",",upper_}]]:=Sequence[n		RowBox[{"\[Bullet]domainRange","[",j,",",domain,",",RowBox[{domain,"[","First","]"}],",",upper,"]"}],",",n		RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",RowBox[{domain,"[","First","]"}],",",upper,"]"}]]

MakeRangeSequence[RowBox[{RowBox[{k_,UnderscriptBox["=",domain_],"\[Ellipsis]"}],",",upper_}]]:=(DeclareUnderscriptDomain[domain];RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",RowBox[{domain,"[","First","]"}],",",upper,"]"}])

MakeRangeSequence[RowBox[{i_,",",j__,",",RowBox[{k_,UnderscriptBox["=",domain_],"\[Ellipsis]"}]}]]:=Sequence[RowBox[{"\[Bullet]domainRange","[",i,",",domain,",",RowBox[{domain,"[","First","]"}],",",RowBox[{domain,"[","Last","]"}],"]"}],",",MakeRangeSequence[RowBox[{j,",",RowBox[{k,UnderscriptBox["=",domain],"\[Ellipsis]"}]}]]]

MakeRangeSequence[RowBox[{j_,",",RowBox[{k_,UnderscriptBox["=",domain_],"\[Ellipsis]"}]}]]:=Sequence[RowBox[{"\[Bullet]domainRange","[",j,",",domain,",",RowBox[{domain,"[","First","]"}],",",RowBox[{domain,"[","Last","]"}],"]"}],",",RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",RowBox[{domain,"[","First","]"}],",",RowBox[{domain,"[","Last","]"}],"]"}]]

MakeRangeSequence[RowBox[{k_,UnderscriptBox["=",domain_],"\[Ellipsis]"}]]:=n	(DeclareUnderscriptDomain[domain];RowBox[{"\[Bullet]domainRange","[",k,",",domain,",",RowBox[{domain,"[","First","]"}],",",RowBox[{domain,"[","Last","]"}],"]"}])

SetAttributes[\[Bullet]\[Bullet]limitRange,HoldFirst];

MakeRangeSequence[RowBox[{i_, ",", j__, ",",RowBox[{k_,UnderscriptBox["\[LongRightArrow]"|"\[RightArrow]"|"\[Rule]",dom_], s_}]}]]:=n	Sequence[RowBox[{"\[Bullet]limitRange","[",i,",",s,",",dom,"]"}],",",n		MakeRangeSequence[RowBox[{j,",",RowBox[{k, "\[LongRightArrow]", s}]}]]]

MakeRangeSequence[n    RowBox[{j_, ",", n      RowBox[{k_, UnderscriptBox["\[LongRightArrow]"|"\[RightArrow]"|"\[Rule]",dom_], s_}]}]]:=Sequence[RowBox[{"\[Bullet]limitRange","[",j,",",s,",",dom,"]"}],",",RowBox[{"\[Bullet]limitRange","[",k,",",s,",",dom,"]"}]]

MakeRangeSequence[RowBox[{k_,UnderscriptBox["\[LongRightArrow]"|"\[RightArrow]"|"\[Rule]",dom_],s_}]]:=RowBox[{"\[Bullet]limitRange","[",k,",",s,",",dom,"]"}]

MakeRangeSequence[RowBox[{i_, ",", j__, ",",RowBox[{k_,"\[LongRightArrow]"|"\[RightArrow]"|"\[Rule]", s_}]}]]:=n	Sequence[RowBox[{"\[Bullet]limitRange","[",i,",",s,",","None","]"}],",",n		MakeRangeSequence[RowBox[{j,",",RowBox[{k, "\[LongRightArrow]", s}]}]]]

MakeRangeSequence[n    RowBox[{j_, ",", n      RowBox[{k_, "\[LongRightArrow]"|"\[RightArrow]"|"\[Rule]", s_}]}]]:=Sequence[RowBox[{"\[Bullet]limitRange","[",j,",",s,",","None","]"}],",",RowBox[{"\[Bullet]limitRange","[",k,",",s,",","None","]"}]]

MakeRangeSequence[RowBox[{k_,"\[LongRightArrow]"|"\[RightArrow]"|"\[Rule]",s_}]]:=RowBox[{"\[Bullet]limitRange","[",k,",",s,",","None","]"}]

SetAttributes[\[Bullet]\[Bullet]simpleRange,HoldFirst];

\[Bullet]simpleRange::usage="\[Bullet]simpleRange[x] usually denotes that the variable `x` ranges over the \"universe\".";

\[Bullet]\[Bullet]simpleRange::usage="\[Bullet]\[Bullet]simpleRange[x] usually denotes that the variable `x` ranges over the \"universe\".";

MakeRangeSequence[RowBox[{s_,",",r__}]]:=Sequence[MakeRangeSequence[s],",",MakeRangeSequence[RowBox[{r}]]]

MakeRangeSequence[RowBox[{s_}]]:=MakeRangeSequence[s]

MakeRangeSequence[s_]:=RowBox[{"\[Bullet]simpleRange","[",s,"]"}]

\[Bullet]locval::usage="\[Bullet]locval[x,v] declares `v` as a local value for `x`.";

MakeRangeSequence[RowBox[{x_,"="|"\[LeftArrow]"|"\[LongLeftArrow]",v_}]]:=RowBox[{"\[Bullet]locval","[",RowBox[{x,",",v}],"]"}]

MakeRangeBoxes::usage="MakeRangeBoxes[x,f] produces the nice-looking output for the range 'x' in output form 'f'.";

SetAttributes[MakeRangeBoxes,HoldAll];

MakeRangeBoxes[(\[Bullet]range|\[Bullet]\[Bullet]range)[x_Pattern,y___],f_]:=RowBox[{"(",RowBox[MakePatternRangeBoxes[{x,y},f]],")"}]

MakeRangeBoxes[(\[Bullet]range|\[Bullet]\[Bullet]range)[x:(_[_Pattern,___]),y___],f_]:=RowBox[{"(",RowBox[MakePatternRangeBoxes[{x,y},f]],")"}]

MakeRangeBoxes[(\[Bullet]range|\[Bullet]\[Bullet]range)[x_],f_]:=MakeSingleRangeBoxes[x,f]

MakeRangeBoxes[(\[Bullet]range|\[Bullet]\[Bullet]range)[x:(__\[Bullet]simpleRange|__\[Bullet]\[Bullet]simpleRange)],f_]:=RowBox[MakeSimpleRangeBoxes[{x},f]]

MakeRangeBoxes[(\[Bullet]range|\[Bullet]\[Bullet]range)[x__],f_]:=GridBox[MakeMultipleRangeBoxes[{x},f]]

MakeRangeBoxes[x_,f_]:=(PrintMessage[Theorema::strangeRange,ToString[x]];
MakeBoxes[x,f])

ClearAll[MakeSingleRangeBoxes];
((SetAttributes[MakeSingleRangeBoxes,HoldAll];))

MakeSingleRangeBoxes[(\[Bullet]simpleRange|\[Bullet]\[Bullet]simpleRange)[x_],f_]:=MakeBoxes[x,f]

MakeSingleRangeBoxes[(\[Bullet]predRange|\[Bullet]\[Bullet]predRange)[x_,t_],f_]:=MakeSingleRangeBoxes[\[Bullet]simpleRange[x],f]/;(TypeVar/.SessionContext[x])===\[Bullet]\[Bullet]predRange[x,t]

MakeSingleRangeBoxes[(\[Bullet]predRange|\[Bullet]\[Bullet]predRange)[x_,t_],f_]:=MakeBoxes[t[x],f]

MakeSingleRangeBoxes[(\[Bullet]setRange|\[Bullet]\[Bullet]setRange)[x_,s_],f_]:=MakeSingleRangeBoxes[\[Bullet]simpleRange[x],f]/;(TypeVar/.SessionContext[x])===\[Bullet]\[Bullet]setRange[x,s]

MakeSingleRangeBoxes[(\[Bullet]setRange|\[Bullet]\[Bullet]setRange)[x_,s_],f_]:=RowBox[{MakeBoxes[x,f],"\[Element]",MakeBoxes[s,f]}]

MakeSingleRangeBoxes[(\[Bullet]integerRange|\[Bullet]\[Bullet]integerRange)[x_,lower_,upper_],f_]:=MakeSingleRangeBoxes[\[Bullet]simpleRange[x],f]/;(TypeVar/.SessionContext[x])===\[Bullet]\[Bullet]integerRange[x,lower,upper]

MakeSingleRangeBoxes[(\[Bullet]integerRange|\[Bullet]\[Bullet]integerRange)[x_,lower_,upper_],f_]:=RowBox[{RowBox[{MakeBoxes[x,f],"=",MakeBoxes[lower,f]}],",","\[Ellipsis]",",",MakeBoxes[upper,f]}]

MakeSingleRangeBoxes[(\[Bullet]domainRange|\[Bullet]\[Bullet]domainRange)[x_,domain_,lower_,upper_],f_]:=MakeSingleRangeBoxes[\[Bullet]simpleRange[x],f]/;(TypeVar/.SessionContext[x])===\[Bullet]\[Bullet]domainRange[x,domain,lower,upper]

MakeSingleRangeBoxes[(\[Bullet]domainRange|\[Bullet]\[Bullet]domainRange)[x_,domain_,lower_,upper_],f_]:=RowBox[{RowBox[{MakeBoxes[x,f],UnderscriptBox["=",MakeBoxes[domain,f]],MakeBoxes[lower,f]}],",","\[Ellipsis]",",",MakeBoxes[upper,f]}]

MakeSingleRangeBoxes[(\[Bullet]limitRange|\[Bullet]\[Bullet]limitRange)[x_,y_],f_]:=MakeSingleRangeBoxes[\[Bullet]simpleRange[x],f]/;(TypeVar/.SessionContext[x])===\[Bullet]\[Bullet]limitRange[x,y]

MakeSingleRangeBoxes[(\[Bullet]limitRange|\[Bullet]\[Bullet]limitRange)[x_,y_],f_]:=RowBox[{MakeBoxes[x,f],"\[Rule]",MakeBoxes[y,f]}]

MakeSingleRangeBoxes[(\[Bullet]locval)[x_,y_],f_]:=RowBox[{MakeBoxes[x,f],"\[LeftArrow]",MakeBoxes[y,f]}]

MakeSingleRangeBoxes[x_,f_]:=(PrintMessage[Theorema::strangeRange,ToString[x]];
RowBox[{"(",MakeBoxes[x,f],")"}])

SetAttributes[MakeSimpleRangeBoxes,HoldAll];

MakeSimpleRangeBoxes[{(\[Bullet]simpleRange|\[Bullet]\[Bullet]simpleRange)[x_]},f_]:={MakeBoxes[x,f]}

MakeSimpleRangeBoxes[{(\[Bullet]simpleRange|\[Bullet]\[Bullet]simpleRange)[x_],y__},f_]:=Prepend[Prepend[MakeSimpleRangeBoxes[{y},f],","],MakeBoxes[x,f]]

SetAttributes[MakeMultipleRangeBoxes,HoldAll];

MakeMultipleRangeBoxes[{x_},f_]:={{MakeSingleRangeBoxes[x,f]}}

MakeMultipleRangeBoxes[{x_,y__},f_]:=Prepend[MakeMultipleRangeBoxes[{y},f],{MakeSingleRangeBoxes[x,f]}]

SetAttributes[MakePatternRangeBoxes,HoldAll]

MakePatternRangeBoxes[{x_},f_]:={MakeBoxes[x,f]}

MakePatternRangeBoxes[{x_,y__},f_]:=Prepend[Prepend[MakePatternRangeBoxes[{y},f],","],MakeBoxes[x,f]]

SpecifiedVariables[(\[Bullet]range|\[Bullet]\[Bullet]range)[r___]]:=
Map[Part[#,1]&,
Cases[{r},rangePattern[__]]]

ToConditionBox[]:="True"

ToConditionBox[RowBox[{}]]:="True"

ToConditionBox[RowBox[{s_}]]:=ToConditionBox[s]

ToConditionBox[s_]:=s

ToConditionBox[s__]:=RowBox[{s}]

SetAttributes[MakeConditionBoxes,HoldAll];

MakeConditionBoxes[x_,f_]:=MakeBoxes[x,f];

TmaEnvironmentTranslationList\[RegisteredTrademark]=({{"Definition", "\[Bullet]def"}, {"Definitions", "\[Bullet]def"}, {"Theorem", "\[Bullet]thm"}, {"Theorems", "\[Bullet]thm"}, {"Lemma", "\[Bullet]lma"}, {"Lemmata", "\[Bullet]lma"}, {"Axiom", "\[Bullet]axm"}, {"Axioms", "\[Bullet]axm"}, {"Corollary", "\[Bullet]crlr"}, {"Corollaries", "\[Bullet]crlr"}, {"Proposition", "\[Bullet]prop"}, {"Propositions", "\[Bullet]prop"}, {"Theory", "\[Bullet]thr"}, {"Theories", "\[Bullet]thr"}, {"KnowledgeBase", "\[Bullet]kb"}, {"KnowledgeBases", "\[Bullet]kb"}, {"Algorithm", "\[Bullet]alg"}, {"Algorithms", "\[Bullet]alg"}, {"Assumption", "\[Bullet]asm"}, {"Assumptions", "\[Bullet]asm"}, {"Formula", "\[Bullet]fml"}, {"Formulae", "\[Bullet]fml"}, {"System", "\[Bullet]sys"}, {"Systems", "\[Bullet]sys"}});

TmaEnvironmentTags\[RegisteredTrademark]=Union[{"\[Bullet]bui"},(Transpose[TmaEnvironmentTranslationList\[RegisteredTrademark]])[[2]]];

TmaEnvironmentTagPatterns\[RegisteredTrademark]=Apply[Alternatives,ToExpression[TmaEnvironmentTags\[RegisteredTrademark]]];

TmaEnvironments\[RegisteredTrademark]=(Transpose[TmaEnvironmentTranslationList\[RegisteredTrademark]])[[1]];

TmaEnvironmentPatterns\[RegisteredTrademark]=Apply[Alternatives,TmaEnvironments\[RegisteredTrademark]];

TmaEnvironmentTranslations\[RegisteredTrademark]=Dispatch[Map[Apply[Rule,#]&,TmaEnvironmentTranslationList\[RegisteredTrademark]]];

TmaEnvironmentTagTranslations\[RegisteredTrademark]=Dispatch[Union[MapThread[Rule[#1,#2]&,{ToExpression[(Transpose[TmaEnvironmentTranslationList\[RegisteredTrademark]])[[2]]],TmaEnvironments\[RegisteredTrademark]}],SameTest->(#1[[1]]===#2[[1]]&)]];

MakeExpression[RowBox[{env:TmaEnvironmentPatterns\[RegisteredTrademark],"[",RowBox[{name_,",",rangeCond__,",",formulaList_?NotIsPreOrPattern}],"]"}],f_]:=
Module[{rg,cond,type,form},
{rg,cond,type}=ToRangeConditionTypeBox[Hold[rangeCond],"FreshNames"];
form=ToFormulaListBox[formulaList];
MakeExpression[RowBox[{env,"[",RowBox[{name,",",MakeTheoremaExpression[RowBox[{"Theorema`Language`Syntax`Parser`Private`\[LeftPointer]VARIABLES\[RightPointer]","[",RowBox[{rg,",",RowBox[{env/.TmaEnvironmentTranslations\[RegisteredTrademark],"[",RowBox[{name,",",rg,",",cond,",",RowBox[{"Theorema`Language`Syntax`Parser`Private`TypeQuantifiers","[",RowBox[{type,",",form}],"]"}]}],"]"}]}],"]"}],f]}],"]"}],f]]/;$SessionIdentifier==="User"

MakeExpression[RowBox[{env:TmaEnvironmentPatterns\[RegisteredTrademark],"[",RowBox[{name_,",",formulaList_?NotIsPreOrPattern}],"]"}],f_]:=
Module[{form,rg=RowBox[{"\[Bullet]range","[","]"}]},
form=ToFormulaListBox[formulaList];
MakeExpression[RowBox[{env,"[",RowBox[{name,",",MakeTheoremaExpression[RowBox[{"Theorema`Language`Syntax`Parser`Private`\[LeftPointer]VARIABLES\[RightPointer]","[",RowBox[{rg,",",RowBox[{env/.TmaEnvironmentTranslations\[RegisteredTrademark],"[",RowBox[{name,",",rg,",","True",",",form}],"]"}]}],"]"}],f]}],"]"}],f]]/;$SessionIdentifier==="User"

NotIsPreOrPattern[RowBox[{"Theorema`Language`Syntax`Parser`Private`\[LeftPointer]VARIABLES\[RightPointer]",___}]]:=False

NotIsPreOrPattern[_]:=True

ToFormulaListBox[s_]:=RowBox[{"\[Bullet]flist","[",MakeFormulaSequence[s],"]"}]

MakeFormulaSequence[env:RowBox[{TmaEnvironmentPatterns\[RegisteredTrademark],"[",___,"]"}]]:=MakeFormulaSequence[GridBox[{{env}}]]

MakeFormulaSequence[f_]:=RowBox[{"\[Bullet]lf","[",RowBox[{"\"\"",",",f}],"]"}]

MakeFormulaSequence[GridBox[{{f_,l_},r:{_,_}..}]]:=Sequence[MakeFormulaSequence[f,l],",",MakeFormulaSequence[GridBox[{r}]]]

MakeFormulaSequence[GridBox[{{f_,l_}}]]:=MakeFormulaSequence[f,l]

MakeFormulaSequence[f_,l_]:=RowBox[{"\[Bullet]lf","[",RowBox[{l,",",f}],"]"}]

MakeFormulaSequence[GridBox[{{env:RowBox[{TmaEnvironmentPatterns\[RegisteredTrademark],"[",___,"]"}]},r:{RowBox[{"Built\[Dash]in"|"Built\[Dash]ins"|"Properties"|"Property","[",___,"]"}]}...}]]:=Sequence[env,MakeFormulaSequence[GridBox[{r}]]]

MakeFormulaSequence[GridBox[{{env:RowBox[{TmaEnvironmentPatterns\[RegisteredTrademark],"[",___,"]"}]},r__}]]:=Sequence[env,",",MakeFormulaSequence[GridBox[{r}]]]

MakeFormulaSequence[GridBox[{{RowBox[{env:"Built\[Dash]in"|"Built\[Dash]ins"|"Properties"|"Property","[",___,"]"}]},r___}]]:=(PrintMessage[Theorema::invalidNesting,env];MakeFormulaSequence[GridBox[{r}]])

MakeFormulaSequence[GridBox[{}]]:=Sequence[]

MakeFormulaSequence[GridBox[c:{{_},{_}..}]]:=Module[{l=Length[c],labels},
labels=Table["\""<>ToString[i]<>"\"",{i,1,Length[c]}];
MakeFormulaSequence[GridBox[Transpose[Append[Transpose[c],labels]]]]]

MakeFormulaSequence[RowBox[{"(",eqn_,")"}]]:=MakeFormulaSequence[eqn]

ToRangeConditionTypeBox[Hold[],_]:={RowBox[{"\[Bullet]range","[","]"}],"True",RowBox[{"\[Bullet]\[Bullet]range","[","]"}]}

ToRangeConditionTypeBox[Hold[rg:RowBox[{"any",___}]],_]:={rg,"True",RowBox[{"\[Bullet]\[Bullet]range","[","]"}]}

ToRangeConditionTypeBox[Hold[ty:RowBox[{"bound",___}]],_]:={RowBox[{"\[Bullet]range","[","]"}],"True",ty}

ToRangeConditionTypeBox[Hold[rg:RowBox[{"any",___}],",",ty:RowBox[{"bound",___}]],_]:={rg,"True",ty}

ToRangeConditionTypeBox[Hold[rg:RowBox[{"any",___}],",",cond_],fn_]:={rg,FreshNameInCond[cond,fn],RowBox[{"\[Bullet]\[Bullet]range","[","]"}]}

ToRangeConditionTypeBox[Hold[rg:RowBox[{"any",___}],",",cond_,",",ty:RowBox[{"bound",___}]],fn_]:={rg,FreshNameInCond[cond,fn],ty}

ToRangeConditionTypeBox[Hold[GridBox[{{r1_},{r2_}}]],fn_]:=ToRangeConditionTypeBox[Hold[r1,",",r2],fn]

ToRangeConditionTypeBox[Hold[GridBox[{{r1_},{r2_},{r3_}}]],fn_]:=ToRangeConditionTypeBox[Hold[r1,",",r2,",",r3],fn]

ToRangeConditionTypeBox[Hold[RowBox[{"(",RowBox[{r__}],")"}]],fn_]:=ToRangeConditionTypeBox[Hold[r],fn]

ToRangeConditionTypeBox[Hold[more___],_]:=(PrintMessage[Theorema::varCondType];
{RowBox[{"\[Bullet]range","[","]"}],"True",RowBox[{"\[Bullet]\[Bullet]range","[","]"}]})

FreshNameInCond[cond_,"FreshNames"]:=RowBox[{"\[Bullet]","[",cond,"]"}]

FreshNameInCond[cond_,_]:=cond

IntroduceVar[r:_[_\[Bullet]var,___]]:=r

IntroduceVar[r_[n_,s___]]:=r[\[Bullet]var[n],s]

TypeQuantifiers[r_\[Bullet]\[Bullet]range,e_]:=With[{s=Apply[List,Map[RangeToHoldingSimpleRange[#]->IntroduceVar[#]&,r/.rangeToHoldingRange]]},
e/.s]

TypeQuantifiers[a___]/;PrintMessage[Theorema::wrongArguments,"TypeQuantifiers",a]:=Null

RangeToHoldingSimpleRange[_[n_\[Bullet]var,___]]:=\[Bullet]\[Bullet]simpleRange[n]

RangeToHoldingSimpleRange[_[n_,___]]:=\[Bullet]\[Bullet]simpleRange[\[Bullet]var[n]]

MakeTheoremaExpression[RowBox[{"any","[",v__,"]"}],f_]:=ToHoldingRangeBox[v]

MakeTheoremaExpression[RowBox[{"any","[","]"}],f_]:=RowBox[{"\[Bullet]range","[","]"}]

MakeTheoremaExpression[RowBox[{"with","[",v__,"]"}],f_]:=ToConditionBox[v]

MakeTheoremaExpression[RowBox[{"bound","[",v__,"]"}],f_]:=ToHoldingRangeBox[v]
*)


End[];
EndPackage[];

