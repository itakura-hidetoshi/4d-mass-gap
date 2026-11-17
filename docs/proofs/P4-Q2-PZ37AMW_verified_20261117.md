# P4-Q2-PZ37AMW — finite two-Wilson-mode cylinder in the genuine physical top orthogonal space

Date: 2026-11-17 JST. Authoritative branch `formal/real-hilbert-uniform-coercive-strong-limit`; `main` is a separately maintained documentation mirror. Lean `v4.30.0-rc2`; mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Same-root / append-only / tighten-only / overwrite-forbidden.

## Mathematical proof scope

Existing independently certified AMT–AMV give a true SU(2) normalized-Wilson physical Gauss-law Hilbert space with explicit orthonormal Wilson-energy Gram–Schmidt modes, a one-dimensional complete top eigenspace `ℝ ∙ Ω`, an abstract Hilbert-basis unit top-orthogonal excitation, and a genuine normalized physical one-slab operator which is nonidentity.

AMU's abstract Hilbert-basis witness does **not** provide a finite Wilson-cylinder representative. AMW instead constructs a nonzero vector **entirely in the span of the first two actual native time-zero spatial plaquette Wilson-energy Gram–Schmidt modes** `v₀`, `v₁`.

For arbitrary finite half-extent `H` and physical `beta ≥ 0`, let `a = inner Ω v₀`, `b = inner Ω v₁`. If `a=0` choose `v₀`; otherwise choose `b v₀ - a v₁`. The original two-mode orthonormality gives nonvanishing, and a direct inner-product calculation gives `inner Ω w=0`. Existing proved one-dimensional top simplicity then identifies that with membership in the full original normalized Wilson top orthogonal complement. No extra one-dimensionality, excitation existence, surjectivity or positive-time OS assumption.

The same two-mode linear combination, as an element of the **original physical SU(2) Gauss-law Hilbert carrier**, has an explicitly identified Haar-a.e. representative on the native time-zero original spatial configuration: the corresponding scalar combination of the **continuous** SU(2) Wilson-energy Gram–Schmidt class functions evaluated on the actual four-Haar cyclic primary spatial plaquette holonomy. This uses AMT's proof of exact `Lp`-representative equality and `Lp.coeFn_add` / `Lp.coeFn_smul`. The cyclic vs intrinsic oriented holonomy are already proven conjugate in AMT.

Proof source: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2TwoModeFiniteCylinderTopOrthogonalV5_PZ37AMW.lean`, final exact-source length 180 lines, canonical source blob pending independent read-back. Three Lean declarations and explicit `#print axioms` audits:

1. `p4Q2PZ37AMW_twoMode_linearCombination`: generic real Hilbert two-mode nonzero orthogonal combination, without dimension assumptions.
2. `p4Q2PZ37AMW_exists_twoMode_nonzero_originalPhysicalTopOrthogonal`: original physical Gauss-law two-Wilson-mode nonzero vector in complete physical Wilson top orthogonal complement, for every `H,beta≥0`.
3. `p4Q2PZ37AMW_twoMode_ae_originalSpatialWilsonObservable`: same physical two-mode vector has the actual Haar-a.e. specified Wilson-class-function observable on the original spatial-slice.

## Source failure and repair provenance, append-only

- Original candidate HEAD `b4e2648c058fc6a551f80caec4b5e9c6e7e9f800`, [PR #6830 exact-source CI #44017759717](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44017759717) **FAILURE**. Two source-direct errors: (1) unknown `inner_zero` identifier at line 63 of this fixed mathlib context, (2) attempted rewriting of `Lp` scalar-summand pointwise representatives before expanding function addition with `Pi.add_apply` at line 166. Downstream `sorryAx` outputs from failed elaboration are not certification and remain historical.
- Minimal source-local repair, theorem statement and original physical model unchanged: replace the named inner-zero rewrite by a `simp`-verified equation; expand `Pi.add_apply` before rewriting `Lp.coeFn_smul` and the original Wilson-mode a.e. equalities.
- Final corrected source HEAD `284a32712741ee73b480e5665bb405136a301e45` in the SAME PR #6830.

## Exact-source independent Lean certification

- [Corrected exact-source CI #44018435756](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44018435756), event `pull_request`, exact source HEAD `284a32712741ee73b480e5665bb405136a301e45`, workflow completed/SUCCESS.
- Mandatory Lean job `133821863351`, required `Run changed Lean fast check` step completed/SUCCESS. Actual decoded log: `Build completed successfully (8832 jobs).`, AMW direct warning/error `0/0`. Three `#print axioms` declarations depend only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Independent receipt job `133823073967` completed/SUCCESS, emitted: `[mcp-receipt] event=pull_request exact_sha=284a32712741ee73b480e5665bb405136a301e45 source_result=success run=44018435756 attempt=1`.
- Exact source, test-merge and canonical Formal merged Git tree all `f6d79ca9aacd84d58c438bdac58fbe471bc40ae1`.
- [Theorem PR #6830](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6830) MERGED, Formal HEAD `0c79f9c31ed6f1580bd7f53cb2df371c94cf14a4`.

## Independent canonical push separately pending at initial record

- [Formal independent push CI #44018904237](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44018904237), event `push`, exact `head_sha=0c79f9c31ed6f1580bd7f53cb2df371c94cf14a4`; initially `in_progress`. **Do not call this completed until workflow, Lean job/required step, logs, axiom audit and exact-head independent receipt have been observed**. Append final result as a separate dated section; never rewrite this checkpoint.

## Explicit obstruction that remains open

This is a physically original finite-cylinder representation in **time-zero spatial Haar L²**, not yet an element of an arbitrary `D.positiveTimeSubalgebra` with a proven compatible `Q.positiveHalfPullback` and boundary synthesis. Existing OS readout packages impose explicit observable and synthesis realization requirements that AMW's true spatial-cylinder representative does not automatically discharge. No same-mode completed-OS boundary moment, physical one-slab vs `C.translate` identification, or 4D continuum Yang–Mills mass gap is claimed.

Docs-only record: no Strict Lean required.

## 2026-11-17 JST append-only independent canonical push completion

The earlier `in_progress` checkpoint remains a distinct true observation at its observation time. Later GitHub MCP inspection of the exact merged source establishes the following independent completion:

- [Canonical Formal push CI #44018904237](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44018904237): event `push`, exact `head_sha=0c79f9c31ed6f1580bd7f53cb2df371c94cf14a4`, attempt 1, workflow **completed/SUCCESS**.
- Required `Changed Lean fast check` job `133823412701` and mandatory `Run changed Lean fast check` step **completed/SUCCESS**. Exact decoded Lake output: `Build completed successfully (8832 jobs).`
- All three AMW `#print axioms` declarations contain exactly standard `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`. Changed AMW Lean source warning/error `0/0`.
- Independent receipt job `133824910615` completed/SUCCESS, actual emitted receipt: `[mcp-receipt] event=push exact_sha=0c79f9c31ed6f1580bd7f53cb2df371c94cf14a4 source_result=success run=44018904237 attempt=1`.
- Full source, PR test-merge, canonical theorem-merged Formal Git tree `f6d79ca9aacd84d58c438bdac58fbe471bc40ae1`.

**Certification:** FORMAL_INTEGRATED_INDEPENDENT_PUSH_CERTIFIED for AMW's exact three theorem statements. The original physical two-mode excitation and Haar-a.e. time-zero cylinder representative are verified, but actual positive-time OS carrier lifting, Wilson/OS one-slab intertwining, volume-uniform/continuum gap remain unproved.

This is a documentation-only append and must not trigger Strict Lean.
