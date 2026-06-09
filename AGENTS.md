# Rules for code writing
1. Write simple explicit procedural code.
2. The symbolic expressions we handle grow combinatorially: performance and memory efficiency is key. Never allocate large intermediate expressions into memory.
3. Employ principles of data-oriented design. Design your data structures first, then think how procedures transform them at maximal efficiency - only then write the logic. Keep your data structures lean. Each step in the program logic only has access to the data it requires without compromise. 
4. Code is a liability, aim for the minimal amount of code while being explicit not to hide crucial details and descriptors.
5. The data flow must allow for paralellization when needed.
6. Each module exports the bare minimum interface required by other modules or the user.
7. The user-facing API is kept minimal and concise. Do not make declarations public by default, only when needed by another module or user-facing API.
8. Write a literal program (in the sense of Knuth) in .org files in /org (code blocks tangled to zig /src), creating an org-roam node for each file and linking (via org-roam id) to other nodes in the literal text. 
9. The prose is kept concise, to the point and explains the essential idea behind each logically independent block of code. Code blocks are kept short - one per idea. Every public declaration has a brief `///` comment describing it.
10. Only write tests when absolutely necessary. Never create tests just to have something pass. The tests must have a clear purpose and must test a precise idea/invariant of the code, not language specifics and syntax.
