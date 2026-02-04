# Claude Code Notes

- All `.m` files share a common `Private`` context. Use unqualified symbol names in patterns (e.g., `R`, `c`) rather than explicit context paths (e.g., `NormalOrdering`R`), which create new symbols instead of matching the loaded ones.
- Pattern match the header R on expr via expr/;RTest[expr], similarly with Op, SF, Interacting (OpTest, SFTest, InteractingTest)
- When Pattern-matching in Mathematica, make sure that the least specific case of a function is defined last. When not done, it can happen that fallback gets evaluated instead of specific case. One must take care when multiple files define the same function.