$Path = Prepend[$Path, Nest[DirectoryName, $InputFileName, 5]];
Needs["StringCode`"];
InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> "TypeII-Ashoke", "bracket" -> "Flat"|>];
recombLegacy::usage = "recombLegacy is the original globally expanding OPE postprocessor, retained as a small-expression oracle.";
recombLegacy[expr_] := FixedPoint[
  Expand[# /. ra_ /; Private`RTest[ra] :> Private`recombineProjectedFlatSpaceR0[ra]] &,
  Expand[expr]];
recombResults = {};
recombCheck::usage = "recombCheck records a projection recombination regression result.";
recombCheck[name_, condition_] := Module[{ok = TrueQ[condition]},
  AppendTo[recombResults, <|"Check" -> name, "Passed" -> ok|>];
  Print[name, ": ", ok]];
recombCases = {
  0, 1, (a+b)^5,
  (a+b)^4 R[ProfileXHolo[F, {}, 0], ProfileXAntiHolo[F, {}, 0], c[0,0],ct[0,0]],
  (a+b)^3 R[ProfileXAntiHolo[F, {}, 0], ProfileXHolo[F, {}, 0], c[0,0],ct[0,0]],
  R[ProfileXHolo[F,{i},0], ProfileXAntiHolo[F,{i},0],
    ProfileXHolo[G,{},0], ProfileXAntiHolo[G,{},0],
    c[0,0],ct[0,0],exp\[Phi]f[-1,0],\[Psi][aa,0,0],
    exp\[Phi]tf[-1,0],\[Psi]t[bb,0,0]],
  R[ProfileXHolo[F,{},0], ProfileXAntiHolo[G,{},0]],
  R[ProfileXHolo[F,{i},0], ProfileXAntiHolo[F,{j},0]],
  R[expXHolo[k,0],expXAntiHolo[k,0],c[0,0],ct[0,0]],
  R[expXAntiHolo[k,0],expXHolo[k,0],c[0,0],ct[0,0]],
  (a+b) (R[ProfileXHolo[F,{},0],ProfileXAntiHolo[F,{},0],c[0,0]] +
    (c0+d)^2 R[ProfileXHolo[G,{},0],ProfileXAntiHolo[G,{},0],ct[0,0]])
};
Do[
  recombCheck["Legacy algebraic equivalence " <> ToString[i],
    SameQ[Expand[Private`postProcessProjectedOPE0[recombCases[[i]]] - recombLegacy[recombCases[[i]]]],0]],
  {i,Length[recombCases]}];
recombCheck["Recombination is idempotent",
  And @@ (SameQ[Private`postProcessProjectedOPE0[Private`postProcessProjectedOPE0[#]],
    Private`postProcessProjectedOPE0[#]] & /@ recombCases)];
recombCheck["Matching profile pairs are recombined",
  SameQ[Private`postProcessProjectedOPE0[R[ProfileXHolo[F,{},0],ProfileXAntiHolo[F,{},0]]],
    R[ProfileX[F,{},0,0]]]];
recombCheck["Mismatched profiles are retained",
  !FreeQ[Private`postProcessProjectedOPE0[recombCases[[7]]],_ProfileXHolo | _ProfileXAntiHolo]];
recombLarge = (1+x1+x2+x3+x4+x5+x6)^1000000 *
  R[ProfileXHolo[F,{},0],ProfileXAntiHolo[F,{},0],c[0,0],ct[0,0]];
recombLargeTime = AbsoluteTiming[recombLargeResult = TimeConstrained[
  Private`postProcessProjectedOPE0[recombLarge],3,$TimedOut];][[1]];
recombCheck["Huge scalar coefficient stays factored while profiles recombine",
  SameQ[recombLargeResult,(1+x1+x2+x3+x4+x5+x6)^1000000 R[ProfileX[F,{},0,0],c[0,0],ct[0,0]]]];
recombCheck["Index guard remains enabled",TrueQ[Private`$StringCodeProjectionGuard]];
recombLegacyJoin::usage = "recombLegacyJoin reproduces the original R-of-whole-chiral-expressions recombination for small regression examples.";
recombLegacyJoin[h_,a_] := Which[h===0||a===0,0,h===1,a,a===1,h,True,recombLegacy[R[h,a]]];
recombJoinCases = {
  {0,R[ct[0,0]]},{1,R[ct[0,0]]},{R[c[0,0]],1},
  {(x+y)^3 R[c[0,0]],(a+b)^2 R[ct[0,0]]},
  {(x+y) (R[c[0,0],\[Psi][aa,0,0]]+R[c[1,0],\[Psi][bb,0,0]]),
   (a+b) (R[ct[0,0],\[Psi]t[cc,0,0]]+R[ct[1,0],\[Psi]t[dd,0,0]])},
  {(x+y) R[ProfileXHolo[F,{},0],c[0,0],exp\[Phi]f[-1,0],\[Psi][aa,0,0]],
   (a+b) R[ProfileXAntiHolo[F,{},0],ct[0,0],exp\[Phi]tf[-1,0],\[Psi]t[bb,0,0]]},
  {R[ProfileXHolo[F,{i},0],ProfileXHolo[G,{},0],c[0,0]],
   R[ProfileXAntiHolo[F,{i},0],ProfileXAntiHolo[G,{},0],ct[0,0]]},
  {x+y,R[ct[0,0],\[Psi]t[bb,0,0]]},
  {R[c[0,0],\[Psi][aa,0,0]],R[c[0,0],ct[0,0]]}
};
Do[recombCheck["Chiral join algebra and ordering signs "<>ToString[i],
  SameQ[Expand[(Private`combineProjectedBracketChiral@@recombJoinCases[[i]])-
    (recombLegacyJoin@@recombJoinCases[[i]])],0]],{i,Length[recombJoinCases]}];
Export[FileNameJoin[{$TemporaryDirectory,"StringCodeProjectionRecombinationChecks.json"}],
  <|"AllPassed"->And@@Lookup[recombResults,"Passed"], "LargeFactoredSeconds"->recombLargeTime,
    "Checks"->recombResults|>,"RawJSON"];
Print["ALL ",And@@Lookup[recombResults,"Passed"]];
Quit[If[And@@Lookup[recombResults,"Passed"],0,1]];
