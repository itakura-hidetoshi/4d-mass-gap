# Lean/mathlib compiler-feedback reinforcement loop

## Purpose

This repository treats the pinned Lean compiler and mathlib version as the
verification environment and reward oracle for proof repair. It does **not**
train model weights. It records reproducible compiler episodes so an agent or
human can reuse successful proof shapes and avoid repeated syntax, elaboration,
typeclass, tactic, and import failures.

The repository currently pins both Lean and mathlib in `lean-toolchain` and
`lakefile.lean`, and builds with `-DautoImplicit=false`. Episodes must therefore
be generated inside this repository rather than against an unpinned global Lean
installation.

## One observation

```bash
python3 scripts/lean_feedback_episode.py \
  MGAP4D.MathlibAnalytic.FiniteLatticeWilsonPlaquetteLocality
```

The command runs the smallest named Lake target, stores the raw log under
`.lean-feedback/logs/`, and appends a JSON record to
`.lean-feedback/episodes.jsonl`. The directory is local and ignored by Git.

## One repair transition

After applying exactly one narrow repair, name the action:

```bash
python3 scripts/lean_feedback_episode.py \
  MGAP4D.MathlibAnalytic.FiniteLatticeWilsonPlaquetteLocality \
  --action ascii_identifier
```

The latest episode for the same target becomes the parent. The record stores

```text
transition_reward = current_reward - parent_reward
```

An explicit parent can be selected with `--parent EPISODE_ID`.

Recommended action names are stable, small labels:

- `ascii_identifier`
- `declare_explicit_binder`
- `add_narrow_import`
- `fully_qualify_name`
- `add_type_annotation`
- `supply_local_instance`
- `replace_broad_simp_with_simp_only`
- `split_have_calc`
- `correct_argument_order`

Do not combine unrelated fixes in one transition; otherwise the reward cannot
identify which repair helped.

## Feedback categories and rewards

| Category | Reward | First response |
|---|---:|---|
| `build_success` | `+8` | Preserve as a positive example; run regression target |
| `build_success_with_warning` | `+6` | Remove warnings before promotion |
| `import_build` | `-2` | Check module path, manifest, cache, smallest target |
| `tactic` | `-3` | Inspect first goal; use explicit `have/calc/rw/exact` |
| `elaboration` | `-4` | Check types, coercions, named arguments, argument order |
| `typeclass` | `-5` | Add explicit assumptions or a local instance |
| `name_resolution` | `-6` | Verify import, namespace, theorem name with `#check` |
| `auto_implicit` | `-6` | Declare all variables under `autoImplicit=false` |
| `parser` | `-8` | Repair syntax before changing mathematics |
| `placeholder` | `-100` | Remove `sorry`/`admit`; never promote as positive data |

When multiple errors occur, the earliest processing layer is primary, while all
matched layers remain in the episode record.

## Report learned repair value

```bash
python3 scripts/lean_feedback_report.py --pretty
```

The report shows success rate, category frequencies, mean reward, and repair
actions ranked by average reward improvement within their parent error category.
This is a small contextual-bandit memory, not an autonomous theorem prover.

## Promotion rule

A proof shape is promoted to reusable positive data only after:

1. the smallest target succeeds;
2. the relevant downstream or smoke target succeeds;
3. no `sorry`, `admit`, placeholder, or unresolved warning remains;
4. the standard PR Lean Fast Check succeeds with the pinned toolchain.

Raw logs and local ledgers are evidence, not proof. The Lean kernel and project
CI remain the final acceptance boundary.
