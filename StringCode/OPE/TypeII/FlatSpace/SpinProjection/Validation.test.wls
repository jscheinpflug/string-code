auditScriptDirectory = DirectoryName[$InputFileName];
Needs["StringCode`"];
InitStringCode[<|"theory"->"TypeII","CFT"->"FlatSpace","conventions"->"TypeII-Ashoke","bracket"->"Flat"|>];
ops={R[c[0,z1],ct[0,z1bar],\[Psi][a,0,z1],\[Psi][b1,0,z1],\[Psi]t[a,0,z1bar],\[Psi]t[b1,0,z1bar]],
 R[c[0,-z0],ct[0,-z0bar],S[{s1,"chiral"},-1/2,{},0,-z0],St[{s1,"chiral"},-1/2,{},0,-z0bar]],
 R[c[0,z0],ct[0,z0bar],exp\[Phi]f[-1,z0],\[Psi][p,0,z0],exp\[Phi]tf[-1,z0bar],\[Psi]t[p,0,z0bar]],
 R[S[{s2,"chiral"},-1/2,{},0,w],St[{s2,"chiral"},-1/2,{},0,wbar]]};
Get[FileNameJoin[{auditScriptDirectory,"Solve.m"}]];
Get[FileNameJoin[{DirectoryName[auditScriptDirectory],"FlatSpace.m"}]];
auditResults={};
auditCheck::usage="auditCheck[label, condition] records one regression assertion.";
auditCheck[label_,condition_]:=(AppendTo[auditResults,{label,TrueQ[condition]}];Print[label,": ",TrueQ[condition]]);
capt={{{"Holo", {R[\[Psi][a, 0, z1], \[Psi][b1, 0, z1], \[Psi]t[a, 0, z1bar], 
     \[Psi]t[b1, 0, z1bar]], R[S[{s1, "chiral"}, -1/2, {}, 0, -z0], 
     St[{s1, "chiral"}, -1/2, {}, 0, -z0bar]], R[exp\[Phi]f[-1, z0], 
     exp\[Phi]tf[-1, z0bar], \[Psi][p, 0, z0], \[Psi]t[p, 0, z0bar]], 
    R[S[{s2, "chiral"}, -1/2, {}, 0, w], St[{s2, "chiral"}, -1/2, {}, 0, 
      wbar]]}, 0, 1234}}, 
 {{"Holo", {R[\[Psi][m1, 0, z1], \[Psi][Private`\[Mu]$123456, 0, z1], 
     \[Psi]t[m1, 0, z1bar], \[Psi]t[Private`\[Mu]$123456, 0, z1bar]], 
    R[S[{\[Alpha]1, "chiral"}, -1/2, {}, 0, -z0], St[{\[Alpha]1, "chiral"}, 
      -1/2, {}, 0, -z0bar]], R[exp\[Phi]f[-1, z0], exp\[Phi]tf[-1, z0bar], 
     \[Psi][p1, 0, z0], \[Psi]t[p1, 0, z0bar]], 
    R[S[{\[Alpha]3, "chiral"}, -1/2, {}, 0, w], St[{\[Alpha]3, "chiral"}, 
      -1/2, {}, 0, wbar]]}, 0, 1234}}};
bad=StringCode`OPE`TypeII`FlatSpace`SpinProjection`Compile`buildSectorArtifact@@capt[[1,1]];
raw=Private`spinProjectionFitSectorArtifact0[bad,1234];
auditCheck["bad case has full rank",raw["CompleteQ"]&&raw["PivotCount"]==4];
(* The old physical counterexample is repaired by local cocycles. Inject a
   wrong fitted vector to keep testing rejection without encoding that bug. *)
{badTime,badResult}=AbsoluteTiming[Block[{Private`spinProjectionFitSectorArtifact0},
 Private`spinProjectionFitSectorArtifact0[args___]:=Join[raw,<|"CoeffVector"->2 raw["CoeffVector"]|>];
 StringCode`OPE`TypeII`FlatSpace`SpinProjection`Solve`solveSectorArtifact[bad,1234]]];
Print["BAD=",InputForm[badResult["Validation"]]," seconds=",badTime];
auditCheck["injected coefficient inconsistency rejected",!badResult["CompleteQ"]&&badResult["FitCompleteQ"]];
auditCheck["rejected coefficients unavailable",badResult["CoeffVector"]===$Failed&&ListQ[badResult["CandidateCoeffVector"]]];
auditCheck["routine not run after fail-fast",badResult["Validation"]["RoutineRegression"]["Status"]==="NotRun"];
auditCheck["failure contains nonzero residual",Lookup[Lookup[badResult["Validation"]["FailFast"],"Failure",<||>],"Residual",0]=!=0];
publicBad=Block[{Private`spinProjectionFitSectorArtifact0},
 Private`spinProjectionFitSectorArtifact0[args___]:=Join[raw,<|"CoeffVector"->2 raw["CoeffVector"]|>];
 Quiet[OPEProjected[0,0][Sequence@@capt[[1,1,2]]]]];
Print["PUBLIC BAD=",InputForm[publicBad]];
auditCheck["public OPE rejects bad case",publicBad===$Failed];
base={R[S[{s1,"chiral"},-1/2,{},0,-z0]],R[exp\[Phi]f[-1,z0],\[Psi][p,0,z0]],R[S[{s2,"chiral"},-1/2,{},0,w]]};
good=StringCode`OPE`TypeII`FlatSpace`SpinProjection`Compile`buildSectorArtifact["Holo",base,0,1234];
{goodTime,goodResult}=AbsoluteTiming[StringCode`OPE`TypeII`FlatSpace`SpinProjection`Solve`solveSectorArtifact[good,1234]];
Print["GOOD=",InputForm[goodResult["Validation"]]," seconds=",goodTime];
auditCheck["valid lower block passes both gates",TrueQ[goodResult["CompleteQ"]]&&TrueQ[goodResult["Validation"]["FailFast"]["PassedQ"]]&&TrueQ[goodResult["Validation"]["RoutineRegression"]["PassedQ"]]];
auditCheck["relabel check passes",TrueQ[Lookup[Lookup[goodResult["Validation"]["RoutineRegression"],"Relabel",<||>],"PassedQ",False]]];
goodRaw=Private`spinProjectionFitSectorArtifact0[good,1234];
wrong=Join[goodRaw,<|"CoeffVector"->2 goodRaw["CoeffVector"]|>];
auditCheck["corrupted coefficient rejected",!TrueQ[Private`spinProjectionValidateSolution0[good,wrong,1234]["PassedQ"]]];
auditCheck["empty probe batch fails closed",!TrueQ[Private`spinProjectionValidationBatch0[good,goodRaw["CoeffVector"],{},1]["PassedQ"]]];
cand=First[goodRaw["WitnessAssignments"]];
timeoutResult=Block[{Private`spinProjectionSectorEvaluation},
 Private`spinProjectionSectorEvaluation[args___]:=(Pause[0.1];0);
 Private`spinProjectionValidationProbe0[good,goodRaw["CoeffVector"],cand,0.01]];
auditCheck["component timeout fails closed",timeoutResult["Status"]==="Timeout"&&!timeoutResult["PassedQ"]];
unevaluatedResult=Block[{Private`spinProjectionSectorEvaluation},
 Private`spinProjectionSectorEvaluation[args___]:=Bosonize[unknownOperator[]];
 Private`spinProjectionValidationProbe0[good,goodRaw["CoeffVector"],cand,1]];
auditCheck["unevaluated reference fails closed",!unevaluatedResult["PassedQ"]];
SeedRandom[777];expectedRandom=RandomInteger[1000000];SeedRandom[777];
Private`spinProjectionValidationUniform0[good,999,10];
auditCheck["uniform sampling preserves random stream",RandomInteger[1000000]===expectedRandom];
antiBase=base/.{S->St,exp\[Phi]f->exp\[Phi]tf,\[Psi]->\[Psi]t,z0->z0bar,w->wbar};
anti=StringCode`OPE`TypeII`FlatSpace`SpinProjection`Compile`buildSectorArtifact["Anti",antiBase,0,1234];
antiResult=StringCode`OPE`TypeII`FlatSpace`SpinProjection`Solve`solveSectorArtifact[anti,1234];
Print["ANTI=",InputForm[antiResult["Validation"]]];
auditCheck["valid antiholomorphic block passes both gates",TrueQ[antiResult["CompleteQ"]]];
vectorBase={R[S[{s1,"chiral"},-1/2,{},0,z0]],R[S[{s2,"chiral"},-1/2,{},0,w]]};
vectorArtifact=StringCode`OPE`TypeII`FlatSpace`SpinProjection`Compile`buildSectorArtifact["Holo",vectorBase,1,1234];
vectorResult=StringCode`OPE`TypeII`FlatSpace`SpinProjection`Solve`solveSectorArtifact[vectorArtifact,1234];
Print["VECTOR=",InputForm[vectorResult["Validation"]]];
auditCheck["vector-output family validates",TrueQ[vectorResult["CompleteQ"]]];
routineRejected=Block[{Private`spinProjectionValidationRelabel0},
 Private`spinProjectionValidationRelabel0[args___]:=<|"PassedQ"->False,"Status"->"InjectedRelabelFailure"|>;
 StringCode`OPE`TypeII`FlatSpace`SpinProjection`Solve`solveSectorArtifact[good,1234]];
auditCheck["routine failure blocks public solve",!routineRejected["CompleteQ"]&&routineRejected["Validation"]["FailFast"]["PassedQ"]&&routineRejected["CoeffVector"]===$Failed];
relabelRejected=Block[{Private`spinProjectionFitSectorArtifact0},
 Private`spinProjectionFitSectorArtifact0[args___]:=Join[goodRaw,<|"CoeffVector"->2 goodRaw["CoeffVector"]|>];
 Private`spinProjectionValidationRelabel0[good,goodRaw,{cand},1234]];
auditCheck["relabel component mismatch is rejected",!relabelRejected["PassedQ"]&&relabelRejected["Status"]==="RelabelMismatch"];
relabelTimeout=Block[{Private`spinProjectionValidationPolicy0,Private`spinProjectionValidationPrediction0},
 Private`spinProjectionValidationPolicy0[]:=<|"ProbeSeconds"->0.01|>;
 Private`spinProjectionValidationPrediction0[args___]:=(Pause[0.1];0);
 Private`spinProjectionValidationRelabel0[good,goodRaw,{cand},1234]];
auditCheck["relabel component timeout fails closed",!relabelTimeout["PassedQ"]&&relabelTimeout["Status"]==="Timeout"];
phaseTimeout=Block[{Private`spinProjectionValidationPolicy0,Private`spinProjectionValidationSupport0},
 Private`spinProjectionValidationPolicy0[]:=<|"ProbeSeconds"->1,"PhaseSeconds"->0.01,"FailFastSupport"->8,"RoutineSupport"->16,"RoutineUniform"->24,"RelabelProbes"->8|>;
 Private`spinProjectionValidationSupport0[args___]:=(Pause[0.1];{cand});
 Private`spinProjectionValidateSolution0[good,goodRaw,1234]];
auditCheck["phase timeout blocks solution",!phaseTimeout["PassedQ"]&&phaseTimeout["FailFast"]["Status"]==="Timeout"];
invalid=StringCode`OPE`TypeII`FlatSpace`SpinProjection`Solve`solveSectorArtifact[<|"Mode"->"SpinProjectionFailure","VarCount"->0|>,1234];
auditCheck["invalid artifact is not accepted",!TrueQ[invalid["CompleteQ"]]];
auditCheck["degenerate probes absent for one vector",Private`spinProjectionValidationRepeated0[{cand}]==={}];
{publicHolo,publicAnti}=Block[{Private`spinProjectionFitSectorArtifact0},
 Private`spinProjectionFitSectorArtifact0[args___]:=Join[raw,<|"CoeffVector"->2 raw["CoeffVector"]|>];
 {Quiet[OPEProjectedHolo[0][Sequence@@capt[[1,1,2]]]],Quiet[OPEProjectedAntiHolo[0][Sequence@@capt[[1,1,2]]]]}];
auditCheck["both chiral APIs propagate failure",publicHolo===$Failed&&publicAnti===$Failed];
Print["ALL=",And@@auditResults[[All,2]]];
Quit[If[And@@auditResults[[All,2]],0,1]];
