# Toy Module-Alias Tree

This folder mirrors the layout discussed in ``rewrite-plan.md``:

- ``StringCode/StringCode.m``
- ``StringCode/Common/Common.m``
- ``StringCode/OPE/OPE.m``
- ``StringCode/Brackets/Brackets.m``

Run the test with:

```bash
/Applications/Wolfram.app/Contents/MacOS/MathKernel -noprompt -script toy-usecontexts-tree/run-toy-test.wl
```

The script prints symbol contexts, downvalue counts, alias mapping, and call results for:
- exported OPE symbol definition visibility
- context-alias resolution in Brackets via ``Needs["StringCode`OPE`" -> "ope`"]``
