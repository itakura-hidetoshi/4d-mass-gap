# Expanded Source Snapshot Inventory

Source zip: `MGAP4D_v1_6_expanded_source_snapshot.zip`

- Total entries: `16,734`
- Lean files: `12,308`
- Main snapshot Lean files: `12,094`
- Direct main `MGAP4D/` Lean files: `9`

## Batch 001 target files

- `MGAP4D/R1/Basic.lean` — 5,386 bytes
- `MGAP4D/R2/Basic.lean` — 5,718 bytes
- `MGAP4D/R3/Basic.lean` — 5,987 bytes
- `MGAP4D/R4/Basic.lean` — 13,419 bytes
- `MGAP4D/R5/Basic.lean` — 7,766 bytes
- `MGAP4D/R6/Basic.lean` — 4,960 bytes
- `MGAP4D/R7/Basic.lean` — 13,683 bytes
- `MGAP4D/Global/FinalAssembly.lean` — 2,513 bytes
- `MGAP4D/Map.lean` — 2,022 bytes

## Batch 001 rationale

These files are the direct Lean root layer from the main snapshot:

```text
MGAP4D_v1_6_R1_R7_plus_all_prior_Lean/MGAP4D.lean
```

That root imports:

```lean
import MGAP4D.R1.Basic
import MGAP4D.R2.Basic
import MGAP4D.R3.Basic
import MGAP4D.R4.Basic
import MGAP4D.R5.Basic
import MGAP4D.R6.Basic
import MGAP4D.R7.Basic
import MGAP4D.Global.FinalAssembly
import MGAP4D.Map
```

The repository keeps its current migration root `MGAP4D.lean` and adds these snapshot modules additively.
