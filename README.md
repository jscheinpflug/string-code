# StringCodeLean

A small Lean 4 proof-of-principle for the holomorphic `b-c` ghost OPE from `string-code`.

Current scope:
- typed fields indexed by chirality, ghost number, and conformal weight
- symbolic singular kernels built from products of pole factors, enough to represent multiple contractions
- sign-aware normal ordering for fermionic `b/c` fields
- a typed `ope` for arbitrary holomorphic `b/c` normal-ordered products on both sides
- correctness lemmas showing the typed API erases to the raw executable semantics

## Codex MCP

This project keeps the Lean MCP server configuration local to the repository so
it does not load in unrelated Codex sessions.

Put the following in `.codex/config.toml` at the project root:

```toml
[mcp_servers.lean-lsp]
command = "uvx"
args = ["lean-lsp-mcp"]
```

Do not keep the same `lean-lsp` entry in `~/.codex/config.toml` unless you want
it enabled for every Codex project.
