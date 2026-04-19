(* ::Package:: *)

Begin["StringCode`Common`"];

UseContexts::usage = "UseContexts[{ctx1,...}, expr] loads contexts and evaluates expr with those contexts prepended to $ContextPath.";
UseContexts[ctxs_List, expr_] := Module[{},
  Scan[Needs, ctxs];
  Block[{$ContextPath = Join[ctxs, $ContextPath]}, expr]
];

End[];
