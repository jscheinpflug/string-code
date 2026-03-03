(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`FlatSpace`TensorStructuresVisualize`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructures`"];


(* ::Section:: *)
(*Declare public variables and methods*)


tensorStructureGraph::usage =
  "tensorStructureGraph[expr, opts] draws a box-and-legs diagram for one tensor structure.";

visualizeTensorStructures::usage =
  "visualizeTensorStructures[groups, opts] draws one representative per tensor-structure group. \
visualizeTensorStructures[incoming, outgoing, opts] generates structures first and then draws representatives.";

exportTensorStructureVisualizations::usage =
  "exportTensorStructureVisualizations[pathPrefix, groups, opts] exports one representative visualization per group. \
exportTensorStructureVisualizations[pathPrefix, incoming, outgoing, opts] generates first, then exports.";

exportTensorStructureVisualizations::nofrontend =
  "No front end detected; falling back from `1` to `2` export format.";

visualizeTensorStructures::badgroups =
  "Expected a list of non-empty structure groups.";

tensorStructureGraph::badexpr =
  "Expected an expression built from GammaProduct/Eps10 factors or scalar 1.";

Options[tensorStructureGraph] = {
  "ImageSize" -> 500,
  "BoxWidth" -> 1.35,
  "BoxHeight" -> 0.82,
  "LegLength" -> 0.48,
  "ShowSpinorLabels" -> False
};

Options[visualizeTensorStructures] = Join[
  Options[generateTensorStructures],
  Options[tensorStructureGraph],
  {"ShowRepresentative" -> True, "MaxGroups" -> All}
];

Options[exportTensorStructureVisualizations] = Join[
  Options[visualizeTensorStructures],
  {"ImageFormat" -> "PNG"}
];


(* ::Section:: *)
(*Logic*)


Begin["Private`"];

isTensorHeadQ::usage = "isTensorHeadQ[head] is True if head is a supported tensor head in any context.";
isTensorHeadQ[head_] := MemberQ[
  {"GammaProduct", "GammaUD", "GammaDU", "Gamma11UU", "Gamma11DD", "CUD", "CDU", "Eps10"},
  SymbolName[Unevaluated[head]]
];

gammaProductCTagNameVisual::usage =
  "gammaProductCTagNameVisual[factor] returns None or \"CUD\"/\"CDU\" for supported GammaProduct factors, and $Failed otherwise.";
gammaProductPartsVisual::usage =
  "gammaProductPartsVisual[factor] returns <|\"cTag\", \"links\", \"spinors\"|> for supported GammaProduct forms, or $Failed.";
gammaProductPartsVisual[factor_] := Module[{args, linksRaw, cTagName, restLinks},
  If[SymbolName[Head[factor]] =!= "GammaProduct", Return[$Failed]];
  args = List @@ factor;
  If[Length[args] =!= 3 || !ListQ[args[[1]]], Return[$Failed]];
  linksRaw = args[[1]];
  If[linksRaw === {},
    Return[<|"cTag" -> None, "links" -> {}, "spinors" -> {args[[2]], args[[3]]}|>]
  ];
  If[SymbolQ[First[linksRaw]],
    cTagName = SymbolName[Unevaluated[First[linksRaw]]];
    If[MemberQ[{"CUD", "CDU"}, cTagName],
      restLinks = Rest[linksRaw];
      If[
        AnyTrue[
          restLinks,
          Function[entry, SymbolQ[entry] && MemberQ[{"CUD", "CDU"}, SymbolName[Unevaluated[entry]]]]
        ],
        Return[$Failed]
      ];
      Return[<|"cTag" -> cTagName, "links" -> restLinks, "spinors" -> {args[[2]], args[[3]]}|>]
    ];
  ];
  <|"cTag" -> None, "links" -> linksRaw, "spinors" -> {args[[2]], args[[3]]}|>
];

gammaProductCTagNameVisual[factor_] := Module[{parts},
  parts = gammaProductPartsVisual[factor];
  If[AssociationQ[parts], parts["cTag"], $Failed]
];

gammaProductLinksVisual::usage = "gammaProductLinksVisual[factor] extracts the links list from a supported GammaProduct factor.";
gammaProductLinksVisual[factor_] := Module[{parts},
  parts = gammaProductPartsVisual[factor];
  If[AssociationQ[parts], parts["links"], {}]
];

gammaProductSpinorsVisual::usage = "gammaProductSpinorsVisual[factor] extracts endpoint spinors from a supported GammaProduct factor.";
gammaProductSpinorsVisual[factor_] := Module[{parts},
  parts = gammaProductPartsVisual[factor];
  If[AssociationQ[parts], parts["spinors"], {}]
];

isGammaFactorVisualQ::usage =
  "isGammaFactorVisualQ[factor] is True for supported GammaProduct[{links},a,b] forms with optional leading CUD/CDU in the links list.";
isGammaFactorVisualQ[factor_] := AssociationQ[gammaProductPartsVisual[factor]];

extractTensorFactors::usage = "extractTensorFactors[expr] extracts gamma factors from expr in multiplicative order.";
extractTensorFactors[1] := {};
extractTensorFactors[expr_] := Module[{factors},
  factors = If[Head[expr] === Times, List @@ expr, {expr}];
  Select[
    factors,
    isGammaFactorVisualQ[#] || (
      Length[#] == 2 && ListQ[#[[1]]] && ListQ[#[[2]]] && SymbolName[Head[#]] === "Eps10"
    ) &
  ]
];

isEpsilonFactorQ::usage = "isEpsilonFactorQ[factor] is True for Eps10[up_List, down_List].";
isEpsilonFactorQ[factor_] := MatchQ[factor, _[_, _]] && SymbolName[Head[factor]] === "Eps10" &&
  ListQ[factor[[1]]] && ListQ[factor[[2]]];

gammaLinkVectorIndexVisual::usage = "gammaLinkVectorIndexVisual[link] extracts a vector index list from one gamma-chain link.";
gammaLinkVectorIndexVisual[link_] /; SymbolName[Head[link]] === "GammaUD" && Length[link] == 1 := Flatten[{link[[1]]}];
gammaLinkVectorIndexVisual[link_] /; SymbolName[Head[link]] === "GammaDU" && Length[link] == 1 := Flatten[{link[[1]]}];
gammaLinkVectorIndexVisual[link_] /; SymbolName[Head[link]] === "Gamma11UU" && Length[link] == 0 := {};
gammaLinkVectorIndexVisual[link_] /; SymbolName[Head[link]] === "Gamma11DD" && Length[link] == 0 := {};
gammaLinkVectorIndexVisual[_] := {};

gammaProductVectorIndicesVisual::usage = "gammaProductVectorIndicesVisual[factor] extracts ordered vector indices from a GammaProduct factor.";
gammaProductVectorIndicesVisual[factor_] /; isGammaFactorVisualQ[factor] :=
  Flatten[gammaLinkVectorIndexVisual /@ gammaProductLinksVisual[factor]];
gammaProductVectorIndicesVisual[_] := {};

vectorListKey::usage = "vectorListKey[vecs] gives a stable string key for a vector-index list.";
vectorListKey[vecs_List] := ToString[HoldForm[vecs], InputForm];

reorderFactorsForVisualization::usage =
  "reorderFactorsForVisualization[factors] places Eps10 factors next to the corresponding converted gamma factors.";
reorderFactorsForVisualization[factors_List] := Module[
  {epsByDown = <||>, gammas, g, key, out = {}, leftovers},
  gammas = Select[factors, isGammaFactorVisualQ];
  Do[
    key = vectorListKey[f[[2]]];
    epsByDown[key] = Append[Lookup[epsByDown, key, {}], f],
    {f, Select[factors, isEpsilonFactorQ]}
  ];
  Do[
    g = gammas[[i]];
    key = vectorListKey[gammaProductVectorIndicesVisual[g]];
    If[KeyExistsQ[epsByDown, key] && epsByDown[key] =!= {},
      AppendTo[out, First[epsByDown[key]]];
      epsByDown[key] = Rest[epsByDown[key]];
    ];
    AppendTo[out, g],
    {i, Length[gammas]}
  ];
  leftovers = Flatten[Values[epsByDown], 1];
  Join[out, leftovers]
];

slotSpinorChiralitiesVisual::usage = "slotSpinorChiralitiesVisual[form] returns spinor chiralities for one gamma head.";
slotSpinorChiralitiesVisual[form_] /; SymbolName[Unevaluated[form]] === "GammaUD" := {"chiral", "antichiral"};
slotSpinorChiralitiesVisual[form_] /; SymbolName[Unevaluated[form]] === "GammaDU" := {"antichiral", "chiral"};
slotSpinorChiralitiesVisual[form_] /; SymbolName[Unevaluated[form]] === "Gamma11UU" := {"chiral", "chiral"};
slotSpinorChiralitiesVisual[form_] /; SymbolName[Unevaluated[form]] === "Gamma11DD" := {"antichiral", "antichiral"};

gammaProductChiralityPairVisual::usage =
  "gammaProductChiralityPairVisual[factor] infers endpoint chirality labels for one supported GammaProduct factor.";
gammaProductChiralityPairVisual[factor_] /; isGammaFactorVisualQ[factor] := Module[
  {cTag, links, state, toggleCount, firstHead},
  cTag = gammaProductCTagNameVisual[factor];
  If[cTag === "CUD", Return[{"chiral", "chiral"}]];
  If[cTag === "CDU", Return[{"antichiral", "antichiral"}]];
  links = gammaProductLinksVisual[factor];
  firstHead = If[links === {}, "", SymbolName[Head[First[links]]]];
  state = Which[
    links === {}, "chiral",
    firstHead === "GammaUD", "chiral",
    firstHead === "GammaDU", "antichiral",
    firstHead === "Gamma11UU", "chiral",
    firstHead === "Gamma11DD", "antichiral",
    True, "chiral"
  ];
  toggleCount = Count[links, l_ /; MemberQ[{"GammaUD", "GammaDU"}, SymbolName[Head[l]]]];
  {
    state,
    If[OddQ[toggleCount], If[state === "chiral", "antichiral", "chiral"], state]
  }
];
gammaProductChiralityPairVisual[_] := {};

factorData::usage = "factorData[factor] returns normalized factor metadata association.";
factorData[factor_] := If[
  SymbolName[Head[factor]] === "Eps10",
  <|
    "form" -> Head[factor],
    "formName" -> SymbolName[Head[factor]],
    "kind" -> "epsilon",
    "cTag" -> None,
    "vectors" -> Join[factor[[1]], factor[[2]]],
    "spinors" -> {},
    "chiralityPair" -> {}
  |>,
  <|
    "form" -> Head[factor],
    "formName" -> SymbolName[Head[factor]],
    "kind" -> "gamma",
    "cTag" -> gammaProductCTagNameVisual[factor],
    "vectors" -> gammaProductVectorIndicesVisual[factor],
    "spinors" -> gammaProductSpinorsVisual[factor],
    "chiralityPair" -> gammaProductChiralityPairVisual[factor]
  |>
];

indexLabel::usage = "indexLabel[idx] gives compact display text for an index symbol/expression.";
indexLabel[idx_Symbol] := ToString[Unevaluated[idx], TraditionalForm];
indexLabel[idx_] := ToString[idx, InputForm];

factorSpacing::usage = "factorSpacing[boxWidth] returns horizontal spacing between neighboring gamma boxes.";
factorSpacing[boxWidth_?NumericQ] := 2.1 boxWidth;

centerXAt::usage = "centerXAt[i, n, spacing] gives x-coordinate for i-th box among n boxes.";
centerXAt[i_Integer, n_Integer, spacing_?NumericQ] := (i - (n + 1)/2) spacing;

vectorLegXOffsets::usage = "vectorLegXOffsets[count, boxWidth] returns x-offsets for vector legs along top edge.";
vectorLegXOffsets[count_Integer, boxWidth_?NumericQ] := Module[{},
  If[count <= 0, {}, Table[-boxWidth/2 + j (boxWidth/(count + 1)), {j, 1, count}]]
];

spinorLegXOffsets::usage = "spinorLegXOffsets[boxWidth] returns two x-offsets for spinor legs along bottom edge.";
spinorLegXOffsets[boxWidth_?NumericQ] := {-boxWidth/4, boxWidth/4};

buildFactorGeometry::usage = "buildFactorGeometry[data, idx, n, boxWidth, boxHeight, legLength] builds box and leg attachment geometry.";
buildFactorGeometry[data_Association, idx_Integer, n_Integer, boxWidth_?NumericQ, boxHeight_?NumericQ, legLength_?NumericQ] := Module[
  {cx, cy = 0, vecOffsets, spinOffsets, topY, botY, label},
  cx = centerXAt[idx, n, factorSpacing[boxWidth]];
  topY = cy + boxHeight/2;
  botY = cy - boxHeight/2;
  vecOffsets = vectorLegXOffsets[Length[data["vectors"]], boxWidth];
  spinOffsets = If[data["kind"] === "gamma", spinorLegXOffsets[boxWidth], {}];
  label = If[
    data["kind"] === "epsilon",
    data["formName"] <> "[" <> ToString[Length[data["vectors"]]] <> "]",
    data["formName"] <> "[" <> ToString[Length[data["vectors"]]] <> "]"
  ];
  <|
    "center" -> {cx, cy},
    "kind" -> data["kind"],
    "box" -> {{cx - boxWidth/2, cy - boxHeight/2}, {cx + boxWidth/2, cy + boxHeight/2}},
    "label" -> label,
    "vectorLegs" -> Table[
      <|
        "index" -> data["vectors"][[j]],
        "root" -> {cx + vecOffsets[[j]], topY},
        "tip" -> {cx + vecOffsets[[j]], topY + legLength}
      |>,
      {j, Length[data["vectors"]]}
    ],
    "spinorLegs" -> If[
      data["kind"] === "gamma",
      Table[
        <|
          "index" -> data["spinors"][[j]],
          "chirality" -> data["chiralityPair"][[j]],
          "root" -> {cx + spinOffsets[[j]], botY},
          "tip" -> {cx + spinOffsets[[j]], botY - legLength}
        |>,
        {j, 2}
      ],
      {}
    ]
  |>
];

buildAllGeometry::usage = "buildAllGeometry[factors, boxWidth, boxHeight, legLength] builds geometry for all factors.";
buildAllGeometry[factors_List, boxWidth_?NumericQ, boxHeight_?NumericQ, legLength_?NumericQ] := Module[{data, n},
  data = factorData /@ factors;
  n = Length[data];
  Table[buildFactorGeometry[data[[i]], i, n, boxWidth, boxHeight, legLength], {i, 1, n}]
];

boxPrimitives::usage = "boxPrimitives[geometry] returns gamma box primitives and labels.";
boxPrimitives[geometry_List] := Flatten[
  Table[
    {
      If[geometry[[i, "kind"]] === "epsilon", RGBColor[0.65, 0.86, 0.58], RGBColor[0.98, 0.78, 0.46]],
      EdgeForm[Directive[GrayLevel[0.25], AbsoluteThickness[1.2]]],
      Rectangle @@ geometry[[i, "box"]],
      Black,
      Text[Style[geometry[[i, "label"]], 11, Bold], geometry[[i, "center"]]]
    },
    {i, Length[geometry]}
  ],
  1
];

spinorLegPrimitives::usage = "spinorLegPrimitives[geometry, showLabels] returns spinor-leg stubs and optional labels.";
spinorLegPrimitives[geometry_List, showLabels_] := Module[{legs, labelText},
  legs = Flatten[geometry[[All, "spinorLegs"]], 1];
  labelText[leg_] := indexLabel[leg["index"]] <> If[leg["chirality"] === "chiral", " (c)", " (a)"];
  Join[
    {Directive[GrayLevel[0.25], AbsoluteThickness[1.2]]},
    (Line[{#["root"], #["tip"]}] &) /@ legs,
    If[TrueQ[showLabels],
      (Text[Style[labelText[#], 9], #["tip"] + {0, -0.18}] &) /@ legs,
      {}
    ]
  ]
];

vectorLegStubs::usage = "vectorLegStubs[geometry] returns vector-leg stub lines from box top to tips.";
vectorLegStubs[geometry_List] := Module[{legs},
  legs = Flatten[geometry[[All, "vectorLegs"]], 1];
  Join[
    {Directive[GrayLevel[0.3], AbsoluteThickness[1.3]]},
    (Line[{#["root"], #["tip"]}] &) /@ legs
  ]
];

vectorContractionPrimitives::usage = "vectorContractionPrimitives[geometry] draws vector-index contractions and labels.";
vectorContractionPrimitives[geometry_List] := Module[
  {legs, grouped, pieces = {}, idx, legList, p1, p2, dx, ctrl, hub},
  legs = Flatten[geometry[[All, "vectorLegs"]], 1];
  grouped = GroupBy[legs, #["index"] &];
  Do[
    idx = key;
    legList = grouped[key];
    Switch[Length[legList],
      1,
        Null,
      2,
        p1 = legList[[1, "tip"]];
        p2 = legList[[2, "tip"]];
        dx = Abs[p2[[1]] - p1[[1]]];
        ctrl = {(p1[[1]] + p2[[1]])/2, Max[p1[[2]], p2[[2]]] + 0.55 + 0.12 dx};
        AppendTo[pieces, {
          Directive[RGBColor[0.2, 0.2, 0.2], AbsoluteThickness[1.6]],
          BezierCurve[{p1, ctrl, p2}]
        }],
      _,
        hub = {Mean[legList[[All, "tip", 1]]], Max[legList[[All, "tip", 2]]] + 0.9};
        AppendTo[pieces, {
          Directive[RGBColor[0.75, 0.2, 0.2], AbsoluteThickness[1.2]],
          Sequence @@ (Line[{#["tip"], hub}] & /@ legList)
        }]
    ],
    {key, Keys[grouped]}
  ];
  Flatten[pieces, 1]
];

plotRangeFromGeometry::usage = "plotRangeFromGeometry[geometry] returns a padded plot range covering boxes and legs.";
plotRangeFromGeometry[geometry_List] := Module[
  {allPts, xs, ys, padX = 0.9, padY = 0.9},
  allPts = Join[
    Flatten[geometry[[All, "box"]], 1],
    Flatten[geometry[[All, "vectorLegs", All, "tip"]], 1],
    Flatten[geometry[[All, "spinorLegs", All, "tip"]], 1]
  ];
  xs = allPts[[All, 1]];
  ys = allPts[[All, 2]];
  {{Min[xs] - padX, Max[xs] + padX}, {Min[ys] - padY, Max[ys] + padY}}
];

buildTensorGraphic::usage = "buildTensorGraphic[factors, optsAssoc] builds the final Graphics diagram for one tensor structure.";
buildTensorGraphic[factors_List, optsAssoc_Association] := Module[
  {boxWidth, boxHeight, legLength, showSpinorLabels, geometry, prims, prange},
  boxWidth = optsAssoc["BoxWidth"];
  boxHeight = optsAssoc["BoxHeight"];
  legLength = optsAssoc["LegLength"];
  showSpinorLabels = optsAssoc["ShowSpinorLabels"];
  geometry = buildAllGeometry[factors, boxWidth, boxHeight, legLength];
  prims = Join[
    boxPrimitives[geometry],
    spinorLegPrimitives[geometry, showSpinorLabels],
    vectorLegStubs[geometry],
    vectorContractionPrimitives[geometry]
  ];
  prange = plotRangeFromGeometry[geometry];
  Graphics[
    prims,
    PlotRange -> prange,
    ImageSize -> optsAssoc["ImageSize"],
    Background -> GrayLevel[0.99]
  ]
];

tensorStructureGraph::usage = "tensorStructureGraph[expr, opts] draws a box-and-legs diagram for one tensor structure.";
tensorStructureGraph[expr_, opts : OptionsPattern[]] := Module[
  {factors, settings},
  factors = reorderFactorsForVisualization[extractTensorFactors[expr]];
  settings = Association[Join[Options[tensorStructureGraph], {opts}]];
  If[expr === 1,
    Return[
      Graphics[
        {
          GrayLevel[0.25], EdgeForm[GrayLevel[0.25]], Rectangle[{-0.7, -0.35}, {0.7, 0.35}],
          Text[Style["Scalar 1", 11, Bold], {0, 0}]
        },
        PlotRange -> {{-1.2, 1.2}, {-0.8, 0.8}},
        ImageSize -> settings["ImageSize"],
        Background -> GrayLevel[0.99]
      ]
    ]
  ];
  If[factors === {},
    Message[tensorStructureGraph::badexpr];
    Return[$Failed];
  ];
  buildTensorGraphic[factors, settings]
];

normalizeGroups::usage = "normalizeGroups[groups] keeps only non-empty list groups.";
normalizeGroups[groups_List] := Select[groups, ListQ[#] && # =!= {} &];

takeLimitedGroups::usage = "takeLimitedGroups[groups, maxGroups] truncates groups if maxGroups is a positive integer.";
takeLimitedGroups[groups_List, maxGroups_] := Module[{},
  If[IntegerQ[maxGroups] && maxGroups > 0, Take[groups, UpTo[maxGroups]], groups]
];

groupPanel::usage = "groupPanel[group, index, showRepresentative, settings] renders one representative diagram panel.";
groupPanel[group_List, index_Integer, showRepresentative_, settings_Association] := Module[
  {rep, g, title},
  rep = First[group];
  g = tensorStructureGraph[
    rep,
    "ImageSize" -> settings["ImageSize"],
    "BoxWidth" -> settings["BoxWidth"],
    "BoxHeight" -> settings["BoxHeight"],
    "LegLength" -> settings["LegLength"],
    "ShowSpinorLabels" -> settings["ShowSpinorLabels"]
  ];
  title = Style[
    "Structure " <> ToString[index] <> " (index permutations: " <> ToString[Length[group]] <> ")",
    Bold, 12
  ];
  Panel[
    Column[
      If[TrueQ[showRepresentative],
        {title, g, Style[TraditionalForm[rep], 10]},
        {title, g}
      ],
      Spacings -> 0.7
    ],
    Background -> GrayLevel[0.98],
    FrameMargins -> Medium
  ]
];

visualizeTensorStructures::usage = "visualizeTensorStructures[groups, opts] draws one representative per structure group.";
visualizeTensorStructures[groups_List, opts : OptionsPattern[]] := Module[
  {normalized, limited, maxGroups, showRepresentative, settings},
  normalized = normalizeGroups[groups];
  If[normalized === {},
    Message[visualizeTensorStructures::badgroups];
    Return[$Failed];
  ];
  maxGroups = OptionValue["MaxGroups"];
  limited = takeLimitedGroups[normalized, maxGroups];
  showRepresentative = OptionValue["ShowRepresentative"];
  settings = Association[Join[Options[tensorStructureGraph], {opts}]];
  Column[
    MapIndexed[groupPanel[#1, #2[[1]], showRepresentative, settings] &, limited],
    Spacings -> 1
  ]
];

visualizeTensorStructures::usage =
  "visualizeTensorStructures[incoming, outgoing, opts] generates structures, then draws one representative per group.";
visualizeTensorStructures[incoming_Association, outgoing_Association, opts : OptionsPattern[]] := Module[
  {genOpts, groups},
  genOpts = FilterRules[{opts}, Options[generateTensorStructures]];
  genOpts = Join[genOpts, {"RepresentativesOnly" -> True}];
  groups = generateTensorStructures[incoming, outgoing, Sequence @@ genOpts];
  visualizeTensorStructures[groups, Sequence @@ FilterRules[{opts}, Options[visualizeTensorStructures]]]
];

buildExportPath::usage = "buildExportPath[pathPrefix, idx, fmt] builds an indexed output path.";
buildExportPath[pathPrefix_String, idx_Integer, fmt_String] := pathPrefix <> "-" <> IntegerString[idx, 10, 3] <> "." <> ToLowerCase[fmt];

resolveExportFormat::usage = "resolveExportFormat[fmt] chooses a safe export format for the current runtime.";
resolveExportFormat[fmt_String] := Module[{imageFormats, safeFmt},
  imageFormats = {"PNG", "JPG", "JPEG", "SVG", "PDF", "EPS"};
  safeFmt = ToUpperCase[fmt];
  If[MemberQ[imageFormats, safeFmt] && $FrontEnd === Null,
    Message[exportTensorStructureVisualizations::nofrontend, safeFmt, "WL"];
    "WL",
    safeFmt
  ]
];

exportTensorStructureVisualizations::usage =
  "exportTensorStructureVisualizations[pathPrefix, groups, opts] exports one representative visualization per group.";
exportTensorStructureVisualizations[pathPrefix_String, groups_List, opts : OptionsPattern[]] := Module[
  {normalized, limited, maxGroups, fmt, safeFmt, settings, i, rep, g, out = {}},
  normalized = normalizeGroups[groups];
  If[normalized === {},
    Message[visualizeTensorStructures::badgroups];
    Return[$Failed];
  ];
  maxGroups = OptionValue["MaxGroups"];
  limited = takeLimitedGroups[normalized, maxGroups];
  fmt = OptionValue["ImageFormat"];
  safeFmt = resolveExportFormat[fmt];
  settings = Association[Join[Options[tensorStructureGraph], {opts}]];
  For[i = 1, i <= Length[limited], i++,
    rep = First[limited[[i]]];
    g = tensorStructureGraph[
      rep,
      "ImageSize" -> settings["ImageSize"],
      "BoxWidth" -> settings["BoxWidth"],
      "BoxHeight" -> settings["BoxHeight"],
      "LegLength" -> settings["LegLength"],
      "ShowSpinorLabels" -> settings["ShowSpinorLabels"]
    ];
    AppendTo[out, Export[buildExportPath[pathPrefix, i, safeFmt], g, safeFmt]];
  ];
  out
];

exportTensorStructureVisualizations::usage =
  "exportTensorStructureVisualizations[pathPrefix, incoming, outgoing, opts] generates structures then exports representative diagrams.";
exportTensorStructureVisualizations[pathPrefix_String, incoming_Association, outgoing_Association, opts : OptionsPattern[]] := Module[
  {genOpts, groups},
  genOpts = FilterRules[{opts}, Options[generateTensorStructures]];
  genOpts = Join[genOpts, {"RepresentativesOnly" -> True}];
  groups = generateTensorStructures[incoming, outgoing, Sequence @@ genOpts];
  exportTensorStructureVisualizations[pathPrefix, groups, Sequence @@ FilterRules[{opts}, Options[exportTensorStructureVisualizations]]]
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
