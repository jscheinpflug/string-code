(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`ModuliIntegration`"];

(* Brackets owns the Differential symbol that bracket output is built from; we
   load it so the exterior-calculus rules below attach to that same symbol and
   therefore fire on bracket results. *)
Needs["StringCode`Brackets`"];


(* ::Section:: *)
(*Declare public variables and methods*)


ExteriorD::usage =
  "ExteriorD[form] is the exterior derivative on the wedge algebra. Each Times term is split into its wedge factor, its coordinate-varying scalar (in z[n,i]/zbar[n,i]/q[n,i]/qbar[n,i]) and its coordinate-free operator part; only the scalar is differentiated. When all summands of a Plus share a common wedge factor the per-variable wedge basis is precomputed once and the term map is run in parallel if subkernels are available.";

UnWedge::usage =
  "UnWedge[form, dz] extracts the coefficient of the one-form dz from form, tracking the graded sign by position inside each Wedge.";

NumberConjugate::usage =
  "NumberConjugate[expr] conjugates only the explicit Complex numbers in expr, leaving symbols untouched.";

bar::usage =
  "bar[expr] is formal complex conjugation: it distributes over Plus/Times/Power, conjugates explicit numbers via NumberConjugate, and fixes the plumbing radius (bar[r0] = r0).";

MaxInsertNum::usage =
  "MaxInsertNum is the maximum number of string insertions handled by the coordinate/variable tables (default 4).";

zvars::usage = "zvars[n] is the list of position coordinates z[k,i], zbar[k,i] for k in 2..n.";
qvars::usage = "qvars[n] is the list of local-frame coordinates q[k,i], qbar[k,i] for k in 2..n.";
allvars::usage = "allvars[n] is the joint list of z, zbar, q, qbar coordinates for k in 2..n.";
dzvars::usage = "dzvars[n] is Differential applied to each entry of zvars[n].";
dqvars::usage = "dqvars[n] is Differential applied to each entry of qvars[n].";
dallvars::usage = "dallvars[n] is Differential applied to each entry of allvars[n].";

varsub::usage =
  "varsub[form, sublist] applies the coordinate substitutions in sublist to form without touching the Differential[...] factors.";

f::usage =
  "f[n,i][w, moduli] = q[n,i][moduli] w + z[n,i][moduli] is the local affine coordinate map around insertion i in the n-string vertex.";

BiPartition::usage =
  "BiPartition[set] returns all ordered splits of set into two nonempty complementary subsets.";

ModuliDomain::usage =
  "ModuliDomain[n] represents the moduli domain of the n-string vertex. ModuliDomain[2] = {} (the propagator strip has no internal moduli).";

VertexDomain::usage =
  "VertexDomain[n] is the vertex chain Chain[{f[n,1],...,f[n,n]}, ModuliDomain[n]] in the fiber bundle.";

BoundaryDomain::usage =
  "BoundaryDomain[n] is the boundary of VertexDomain[n], a sum of ChainPermutation[...] of plumbing trees over all BiPartition[Range[n]].";

PlumbingTree::usage =
  "PlumbingTree[domainL, domainR, qPlumb] glues two vertex chains through a plumbing fixture with parameter qPlumb, producing a chain fibered over Cartesian[moduliL, UnitCircle[qPlumb], moduliR].";

MatchingCondition::usage =
  "MatchingCondition[n] lists the coordinate-map matching data on the boundary of VertexDomain[n] (illustration only).";

MapPermute::usage =
  "MapPermute[Function[f], a] permutes the arguments of the coordinate-map function f by the permutation a.";

ChainIntegrate::usage =
  "ChainIntegrate[integrand, chain] integrates a form-valued integrand over a chain, recursing through Plus, Chain, MapDomain and ChainPermutation down to DomainIntegrate.";

DomainIntegrate::usage =
  "DomainIntegrate[form, domain] integrates form over a moduli domain; an exact form over ModuliDomain[n] is reduced (Stokes) to its primitive over BoundaryDomain[n].";

IntegrateExactForm::usage =
  "IntegrateExactForm[form] returns a scalar primitive whose ExteriorD equals form, by integrating one coordinate at a time and subtracting the exterior derivative of each partial result. Assumes form is exact.";

LineIntegral::usage =
  "LineIntegral[form, variable] is the indefinite integral of form in variable.";

PullBack::usage =
  "PullBack[form, n][coordmaps] substitutes the n-th insertion's coordinates z[n,i], zbar[n,i], q[n,i], qbar[n,i] using coordmaps and its derivative, sending Conjugate to bar.";

FormIntegrate::usage =
  "FormIntegrate[form] is the primitive of a closed form on a moduli stratum used by the Stokes recursion in DomainIntegrate. Placeholder: not yet given an explicit definition.";

Chain::usage = "Chain[coordmaps, domain] is an inert container for a chain in the moduli fiber bundle.";
MapDomain::usage = "MapDomain[map, base] is an inert container for the pushforward of base under map.";
Cartesian::usage = "Cartesian[domains...] is an inert product of moduli domains.";
UnitCircle::usage = "UnitCircle[q] is the unit circle in the plumbing parameter q.";
ChainPermutation::usage = "ChainPermutation[sigma, chain] is a chain with its insertions permuted by sigma.";
Matching::usage = "Matching[...] is inert boundary coordinate-map matching data produced by MatchingCondition.";

z::usage = "z[n,i] is the position coordinate of insertion i in the n-string vertex; z[n,i][moduli] is its moduli-dependent value.";
zbar::usage = "zbar[n,i] is the conjugate position coordinate of insertion i in the n-string vertex.";
q::usage = "q[n,i] is the local-frame scale of insertion i in the n-string vertex; q[n,i][moduli] is its moduli-dependent value.";
qbar::usage = "qbar[n,i] is the conjugate local-frame scale of insertion i in the n-string vertex.";
z0::usage = "z0 is the fixed position modulus of the 2-string (propagator) vertex.";
r0::usage = "r0 is the fixed plumbing radius of the 2-string (propagator) vertex.";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Wedge product of forms (rules attach to System`Wedge)*)


(* System`Wedge ships with the Flat/OneIdentity attributes, which break the
   positional antisymmetry rules below (they cause non-termination). Strip them. *)
Unprotect[Wedge];
ClearAll[Wedge];

Wedge[a___,b_+c_,d___]:=Wedge[a,b,d]+Wedge[a,c,d];
Wedge[e___,a_ b_,c___]:=a Wedge[e,b,c]/;FreeQ[a,Differential];
Wedge[e___,a_,b_,c___]:=-Wedge[e,b,a,c]/;(!OrderedQ[{a,b}]);
Wedge[e___,a_,a_,c___]:=0;
Wedge[e___,a_,b___,a_,c___]:=0;
Wedge[a_,Wedge[b___]]:=Wedge[a,b];
Wedge[a___,Wedge[b___],c___]:=Wedge[a,b,c];
Wedge[a_]:=a;
Wedge[0]=0;
Wedge[a___,0,b___]:=0;
Wedge[]=1;


(* ::Subsection:: *)
(*Differential (rules attach to StringCode`Brackets`Differential)*)


Unprotect[Differential];

Differential[f_]:= (Differential[#] &/@ f)/;Head[f]==Plus;
Differential[f_+g_]:=Differential[f]+Differential[g];
Differential[f_ g_]:=f Differential[g]+g Differential[f];
Differential[f_^2]:=2 f Differential[f];
Differential[f_^n_]:=n f^(n-1) Differential[f];
Differential[a_ f_]:=a Differential[f]/;NumberQ[a];
Differential[z0]:=0;
Differential[r0]:=0;
Differential[0]=0;

(* Total differential of a moduli-dependent function: expand along the moduli list.
   For f[{t,tbar}] this gives D[f[{t,tbar}], t] Differential[t] + D[f[{t,tbar}], tbar] Differential[tbar].
   This collapses all dz[n,i] onto the 2-dimensional basis {Differential[t], Differential[tbar]}
   so wedge antisymmetry kills 3-forms and higher automatically. *)
Differential[f_[moduli_List]] := 0 /; VectorQ[moduli, NumericQ];
Differential[f_[moduli_List]] := Sum[D[f[moduli], v] Differential[v], {v, moduli}] /; VectorQ[moduli, MatchQ[#, _Symbol] &];
Differential[f_[mods__]] := 0 /; AllTrue[{mods}, NumericQ];
Differential[f_[mods__]] := Sum[D[f[mods], v] Differential[v], {v, {mods}}] /; VectorQ[{mods}, MatchQ[#, _Symbol] &];

(* Tell D and Derivative that Differential[...] and Wedge[...] are constants w.r.t.
   any variable. Mathematica's chain rule for D on an unknown head emits Derivative[
   indices][f][args] directly without re-calling D, so we need both forms covered.
   Without these, ExteriorD's internal D[varying, v] produces spurious
   Derivative[1][Differential][...] / Wedge^(...)[...] artefacts. *)
Differential /: D[_Differential, _] := 0;
Differential /: Derivative[1][Differential] := (0 &);

Wedge /: D[_Wedge, _] := 0;
Wedge /: Derivative[n__Integer][Wedge] := (0 &) /; Total[{n}] > 0;


(* ::Subsection:: *)
(*Contraction of forms*)


UnWedge[f_,dz_]:=(UnWedge[#,dz] &/@ f)/;Head[f]==Plus;
UnWedge[a_+b_,dz_]:=UnWedge[a,dz]+UnWedge[b,dz];
UnWedge[f_,dz_]:=Coefficient[f,dz]/;FreeQ[f,Wedge];
UnWedge[f_,dz_]:=Module[{wedges=Cases[f,_Wedge],nonwedges=DeleteCases[f,_Wedge]},nonwedges UnWedge[Times @@ wedges,dz] ]/;Head[f]==Times;
UnWedge[a_ b_,dz_]:=a UnWedge[b,dz]/;(FreeQ[a,Differential] && Head[b]==Wedge);
UnWedge[f_,dz_]:=0/;FreeQ[f,Differential];
UnWedge[Wedge[a___],dz_]:=Module[{tmp=Position[List @@ (Wedge[a]),dz]},If[Length[tmp]==0,0,If[Length[tmp]==1,(-1)^(tmp[[1,1]]-1) DeleteCases[Wedge[a],dz],Print["error"]]]];


(* ::Subsection:: *)
(*Exterior derivative*)


ExteriorD[0]=0;
ExteriorD[g_]:=0/;Head[g]==Wedge;

(* Per-term action: strip the (known) common wedge by substitution -- robust to
   nested positions inside Plus/Times -- then apply the vars-skip Sum. *)
exteriorDStrip[expr_,wedgeBasis_Association,commonWedge_]:=Module[
  {stripped,vars=Keys[wedgeBasis],factors,varying,fixed,relevant},
  stripped=expr/.commonWedge->1;
  factors=If[Head[stripped]===Times,List @@ stripped,{stripped}];
  varying=Times @@ Select[factors,!FreeQ[#,Alternatives @@ vars] &];
  fixed  =Times @@ Select[factors, FreeQ[#,Alternatives @@ vars] &];
  relevant=Select[vars,!FreeQ[varying,#] &];
  fixed Sum[D[varying,v] wedgeBasis[v],{v,relevant}]
];

(* First-wedge subexpression (deep search). Missing[] if absent. *)
firstWedgeIn[expr_]:=FirstCase[expr,_Wedge,Missing[],{0,Infinity}];

(* Plus dispatcher: detect a wedge factor shared by all summands. If shared,
   precompute Wedge[d v, commonWedge] once per v and (when subkernels exist)
   ParallelMap; otherwise fall back to term-by-term ExteriorD. *)
ExteriorD[s_Plus]:=Module[
  {terms=List @@ s,vars=allvars[MaxInsertNum],firstWedge,commonWedge,wedgeBasis,mapped},
  firstWedge=firstWedgeIn[First[terms]];
  If[MissingQ[firstWedge]||!AllTrue[Rest[terms],firstWedgeIn[#]===firstWedge &],
    Return[Total[ExteriorD /@ terms]]
  ];
  commonWedge=firstWedge;
  wedgeBasis=AssociationMap[Wedge[Differential[#],commonWedge] &,vars];
  mapped=If[$KernelCount>0,
    DistributeDefinitions[exteriorDStrip];
    ParallelMap[exteriorDStrip[#,wedgeBasis,commonWedge] &,terms,Method->"FinestGrained"],
    exteriorDStrip[#,wedgeBasis,commonWedge] & /@ terms
  ];
  Total[mapped]
];

ExteriorD[expr_Times]/;!FreeQ[expr,_Wedge]:=Module[
  {vars=allvars[MaxInsertNum],wedge,wedgeBasis},
  wedge=firstWedgeIn[expr];
  wedgeBasis=AssociationMap[Wedge[Differential[#],wedge] &,vars];
  exteriorDStrip[expr,wedgeBasis,wedge]
];
ExteriorD[expr_Times]/;!FreeQ[expr,_Differential]&&FreeQ[expr,_Wedge]:=Module[
  {vars=allvars[MaxInsertNum],oneForm,wedgeBasis},
  oneForm=FirstCase[expr,_Differential,Missing[],{0,Infinity}];
  wedgeBasis=AssociationMap[Wedge[Differential[#],oneForm] &,vars];
  exteriorDStrip[expr,wedgeBasis,oneForm]
];


(* ::Subsection:: *)
(*Complex conjugation*)


NumberConjugate[f_]:=f/.Complex[a_,b_]:>Complex[a,-b];
bar[f_]:= (bar[#] &/@ f)/;(Head[f]==Plus || Head[f]==Times);
bar[f_^2]:=bar[f]^2;
bar[f_^n_]:=bar[f]^n;
bar[a_ f_]:=NumberConjugate[a] bar[f]/;NumberQ[a];
bar[r0]:=r0;
bar[a_]:=NumberConjugate[a]/;NumberQ[a];


(* ::Subsection:: *)
(*Coordinates and variable tables*)


MaxInsertNum=4;

zvars[insertnum_]:=zvars[insertnum]=Flatten[Table[{z[n,i],zbar[n,i]},{n,2,insertnum},{i,1,n}]];
qvars[insertnum_]:=qvars[insertnum]=Flatten[Table[{q[n,i],qbar[n,i]},{n,2,insertnum},{i,1,n}]];
allvars[insertnum_]:=allvars[insertnum]=Flatten[Table[{z[n,i],zbar[n,i],q[n,i],qbar[n,i]},{n,2,insertnum},{i,1,n}]];
dzvars[insertnum_]:=dzvars[insertnum]=Differential[#] & /@ zvars[insertnum];
dqvars[insertnum_]:=dqvars[insertnum]=Differential[#] & /@ qvars[insertnum];
dallvars[insertnum_]:=dallvars[insertnum]=Differential[#] & /@ allvars[insertnum];

varsub[form_,sublist_]:=Module[{tmp,i,lista,sublista,nvars=Length[allvars[MaxInsertNum]]},lista=Table[tmp[i],{i,1,nvars}];sublista=Table[Differential[allvars[MaxInsertNum][[i]]]->Differential[tmp[i]],{i,1,nvars}];form/.sublista/.sublist/.{tmp[j_]:>allvars[MaxInsertNum][[j]]}];


(* ::Subsection:: *)
(*Vertex / boundary / plumbing domains*)


f[n_,i_][w_,moduli_]:=q[n,i][moduli] w + z[n,i][moduli];

BiPartition[set_]:=Module[{asets=Subsets[set,{2,Length[set]-1}]},{#,Complement[set,#]} & /@ asets];

q[2,i_][_]:=r0;
z[2,1][_]:=-z0;
z[2,2][_]:=z0;
ModuliDomain[2]:={};

VertexDomain[n_]:=Module[{i},Chain[Table[Evaluate[f[n,i][#1,#2]] &,{i,1,n}],ModuliDomain[n]]];

BoundaryDomain[n_]:=Module[{qPlumb},Plus @@ (ChainPermutation[Join @@ #,PlumbingTree[VertexDomain[Length[#[[1]]]],VertexDomain[Length[#[[2]]]+1],qPlumb]] & /@ BiPartition[Range[n]])];

PlumbingTree[domainL_,domainR_,qPlumb_]:=Module[{i,j,k,l1=Length[domainL[[1]]],l2=Length[domainR[[1]]],coordmaps,moduliL,moduliR},coordmaps=Evaluate[Join[Table[domainR[[1,1]][qPlumb domainL[[1,j]][#,moduliL],moduliR],{j,1,l1}],
Table[domainR[[1,k]][#,moduliR],{k,2,l2}]]] &;Chain[coordmaps,MapDomain[Evaluate[coordmaps[0,#]] &,Cartesian[domainL[[2]][moduliL],UnitCircle[qPlumb],domainR[[2]][moduliR]]]]];

MatchingCondition[n_]:=Module[{bulk=VertexDomain[n],boundary=List @@ BoundaryDomain[n]},Matching[Permute[bulk[[1]],#[[1]]],#[[2,1]],#[[2,2]]] & /@ boundary];

MapPermute[Function[f_],a_]:=Function[Permute[f,a]//Evaluate];


(* ::Subsection:: *)
(*Chain integration*)


ChainIntegrate[stringintegrand_,chainvar_]:=(ChainIntegrate[stringintegrand,#] & /@ chainvar)/;Head[chainvar]==Plus;
ChainIntegrate[stringintegrand_,chainvar_]:=DomainIntegrate[stringintegrand[chainvar[[1]]],chainvar[[2,2]]]/;Head[chainvar]==Chain && Head[chainvar[[2]]]==MapDomain;
ChainIntegrate[stringintegrand_,chainvar_]:=DomainIntegrate[stringintegrand[chainvar[[1]]],chainvar[[2]]]/;Head[chainvar]==Chain && Head[chainvar[[2]]]==ModuliDomain;
ChainIntegrate[stringintegrand_,chainvar_]:=DomainIntegrate[stringintegrand[MapPermute[chainvar[[2,1]],chainvar[[1]]]],chainvar[[2,2,2]]]/;Head[chainvar]==ChainPermutation && Head[chainvar[[2]]]==Chain;

DomainIntegrate[form[anything_],ModuliDomain[n_]]:=DomainIntegrate[FormIntegrate[form],BoundaryDomain[n]];
DomainIntegrate[0,moduli_]:=0;

IntegrateExactForm[f_]:=(IntegrateExactForm[#] &/@ f)/;Head[f]==Plus;
IntegrateExactForm[form_]:=Module[{nvars=Length[allvars[MaxInsertNum]],i,tmpform=form//Expand,tmpint,accu},accu=0;Do[tmpint=LineIntegral[UnWedge[tmpform,dallvars[MaxInsertNum][[i]]],allvars[MaxInsertNum][[i]]];accu=accu+tmpint;tmpform=tmpform-ExteriorD[tmpint]//Expand,{i,1,nvars}];accu];

LineIntegral[form_,variable_]:=Module[{indefint},indefint=Integrate[form,variable];indefint];

PullBack[form_,n_][coormaps_]:=Module[{zz=coormaps[0],qq=coormaps'[0]},form/.{z[n,i_]:>zz[[i]],zbar[n,i_]:>Conjugate[zz[[i]]],q[n,i_]:>qq[[i]],qbar[n,i_]:>Conjugate[qq[[i]]]}/.Conjugate->bar];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
