# Prior Kernels Inventory

This inventory tracks historical MGAP4D kernel material during GitHub-native migration.

## Initial archive classes

| Class | Meaning | Active import allowed? |
|---|---|---:|
| pending | preserved, not yet reviewed | no |
| reviewed | CI-checked and mapped | yes, in small batches |
| superseded | lineage only | no |

## Initial pending groups

- `v1_0_final` prior Lean project archive
- `v0_9_*` manifest family
- earlier R1--R7 scaffold variants
- earlier Global final assembly variants
- map and declaration index material

## Current active equivalent

The active source tree already contains status-interface versions of:

```text
R1.Concrete
R2.Concrete
R3.Concrete
R4.Concrete
R5.Concrete
R6.Concrete
R7.Concrete
OperatorAPI
Global.Concrete status files
```

Historical kernels should be compared against these active paths before migration.
