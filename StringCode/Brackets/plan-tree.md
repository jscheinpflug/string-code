# DrawTree: Visualize EffectiveBracket tree diagrams

## Task
- Create a public function `DrawTree` in `Brackets.m` that takes the output of `EffectiveBracket` (or a single term from it) and draws tree diagrams using native Mathematica functions.
- Each `PropagatorHold[q][ProjectorBarHold[...]]` = internal leg
- Each field argument = external leg, labeled by number
- Optionally print a legend mapping numbers to input fields

## File to modify
`/home/scheinpflug/Github/string-code/StringCode/Brackets/Brackets.m`

### Change 1: Public declaration (after line 23)
```mathematica
DrawTree::usage = "DrawTree[expr] draws tree diagrams for EffectiveBracket output";
```

### Change 2: New subsection before `End[]` (before line 841)

## Design

### Visual style
- **No vertex labels** — vertices are just junction points where lines meet
- **External legs** labeled with circled numbers (1, 2, 3, ...)
- **Outgoing leg** (from `ProjectorHold`) drawn as a line going up from root, labeled "P"
- Clean, minimal aesthetic: thin dark edges, small filled circles at vertices, colored numbered circles at leaves
- Use `Graph` with `"LayeredDigraphEmbedding"` layout, top-down orientation

### Vertex styling
- **Junction vertices** (bracket nodes): small filled dark gray circles, no labels
- **External legs** (field leaves): colored circles with white number inside (like pins on a map)
- **Root "P" node**: small circle at top, edge going up to indicate outgoing leg

### Optional legend
`DrawTree` accepts an option `"Legend" -> True` (default `True`). When enabled, a legend box is shown below the graph mapping each number to the corresponding input field expression.

### Input handling
```mathematica
DrawTree[expr_Plus]              (* sum of terms → Grid of trees *)
DrawTree[ProjectorHold[inner_]]  (* single term → single tree *)
DrawTree[c_ expr_ProjectorHold]  (* coefficient × term → single tree *)
DrawTree[0]                      (* zero → "No diagrams" message *)
```

## Algorithm

### Parse nested structure into graph data

Each term has structure:
```
ProjectorHold[BracketHold[field1, ..., PropagatorHold[q][ProjectorBarHold[BracketHold[...]]]]]
```

Recursive parser (`parseTree`):
1. Strip `ProjectorHold`, create root vertex
2. At each `BracketHold[args...]`, create a junction vertex, connect to parent
3. For each arg:
   - Field → create numbered leaf vertex, connect to junction
   - `PropagatorHold[q][ProjectorBarHold[inner]]` → recurse into `inner`
     (detect via `MatchQ[Head[arg], _PropagatorHold]` since head is `PropagatorHold[q]`)
4. Number assignment: scan all fields in the term left-to-right (as they appear in BracketHold args, outermost first), assign incrementing numbers

Returns: `{vertices, edges, vertexTypes, leafNumbers, root}`

### Build and render graph

```mathematica
buildTreeGraph[{vertices_, edges_, vertexTypes_, leafNumbers_, root_}]
```
- `DirectedEdge` from parent to child
- `GraphLayout -> {"LayeredDigraphEmbedding", "RootVertex" -> root}`
- Junction vertices: `VertexSize -> 0.015`, `VertexStyle -> Directive[GrayLevel[0.3]]`, no label
- Leaf vertices: `VertexSize -> 0.06`, styled as colored disks with white number text via `VertexShapeFunction`
- Root vertex: small node, with an upward stub edge or marker indicating outgoing leg
- `EdgeStyle -> Directive[GrayLevel[0.3], AbsoluteThickness[1.5]]`
- `Arrowheads[0]` (no arrows)

### Grid display for sums
`DrawTree[expr_Plus]` splits into terms, draws each, arranges in `Grid` with 4 columns. Each cell gets a `Labeled[graph, "Term i"]` or similar subtle label.

## Functions

| Function | Scope | Purpose |
|----------|-------|---------|
| `DrawTree` | Public | Main entry point (handles Plus, single term, zero) |
| `splitTerms` | Private | Split Plus expr into list of terms |
| `parseTree` | Private | Parse single term → graph data structure |
| `buildTreeGraph` | Private | Graph data → styled `Graph` object |
| `drawSingleTree` | Private | Compose parse + build |
| `numberFields` | Private | Assign numbers to external legs in a term |
| `makeLegend` | Private | Build legend mapping numbers → field expressions |

## Edge cases
- `DrawTree[0]` → return text "No diagrams"
- n=2: simplest tree (root → vertex → two leaves)
- Deep chains (n=4, {2,1,1}): three nested levels, handled by recursion
- Coefficient prefactors: strip and ignore for drawing

## Verification
1. `DrawTree[EffectiveBracket[SF1, SF2]]` → 1 tree
2. `DrawTree[EffectiveBracket[SF1, SF2, SF3]]` → 4 trees in grid
3. Pick a single term from `EffectiveBracket[SF1, SF2, SF3]` and pass to `DrawTree` → 1 tree
4. `DrawTree[EffectiveBracket[SF1, SF2, SF3, SF4]]` → 23 trees in grid
5. Check that external legs show circled numbers and legend maps them correctly
6. `DrawTree[0]` → graceful "No diagrams" output
