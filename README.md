# MGAP4D — formalizing the four-dimensional Yang–Mills problem

**Original Wilson SU(2) lattice theory · Lean 4 + mathlib · Hidetoshi Itakura**

> **Research status (2026-10-18 JST): substantial finite-volume Wilson and physical-Hilbert results are formally proved; the continuum four-dimensional Yang–Mills existence and mass-gap problem is NOT solved.** This page is a map of proved statements and remaining obligations, not a claim of a Clay Millennium Prize solution.

**日本語要約：** 真正Wilson相互作用posterior、Gauss則を満たす物理Hilbert空間、有限体積の作用素・GI検出器をLean 4/mathlibで形式化している。時間方向のSU(2) Wilson posteriorに対する厳密な非零検出は証明済み。一方、空間Wilson作用に対する真正GI二文脈minorの非零性、正のfine結合における全高次Krylov物理源の分離、体積・格子間隔に一様な評価、連続体Yang–Mills構成と質量ギャップは未解決である。

## Authoritative theorem source and verified checkpoint

| Item | Grounded status |
| --- | --- |
| Repository | [itakura-hidetoshi/4d-mass-gap](https://github.com/itakura-hidetoshi/4d-mass-gap) |
| **Sole theorem-authoritative branch** | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Canonical HEAD observed on **2026-10-18 JST** | [`d5316fe0a0cf96a8ab8a198bda280ac035585ab4`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/d5316fe0a0cf96a8ab8a198bda280ac035585ab4) |
| Latest merged theorem PR at this checkpoint | [#5665 — P4-Q2-JS](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5665), preceded by [#5664 — JR](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5664) |
| #5665 exact-source Lean CI | [#39098811665 — SUCCESS](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39098811665); **10754/10754** Lean jobs |
| #5665 source audit | Five printed axioms reports; no `sorryAx`; changed JS file warning/error **0/0**; MCP completion receipt SUCCESS |
| Pinned Lean toolchain | `leanprover/lean4:v4.30.0-rc2` |
| Pinned mathlib commit | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` (in `lake-manifest.json`) |

The GitHub default `main` is **not** the theorem-bearing authority. The SHA above is a dated checkpoint, not a promise that the branch will never advance. For any new mathematical claim, re-observe the branch HEAD, read the exact Lean statement and its dependencies, then inspect the CI for that exact source SHA. Source, test, and squash-merge SHAs serve different roles. Documentation alone is not theorem evidence.

## What is being formalized

The project keeps several genuinely different structures **distinct**:

1. **Original interacting Wilson probability and transfer:** the real physical joint Wilson ground-state law, normalized one-slab transfer, Perron vacuum, and gauge-invariant physical Haar-`L²` sources. A *frozen* Wilson coupling `b = beta(n)` and a *fine-source* coupling `t = beta(n+1)` are different parameters.
2. **Two genuine interacting conditional posteriors:** `p₀,b` and `pπ,b` for the original identity/π-rotated left physical contexts. The normalized SU(2) Haar measure `ν` is their **common density reference**, not either conditional posterior. The distinct outer pair-Haar measure integrates actual full physical contexts.
3. **Physical signed GI source response:** the difference of expectations under those two original posterior laws, tested with the *actual source-dependent Wilson receiver*, retaining joint half-density, transfer normalization, and the physical link insertion.
4. **Different finite-volume quadratic operators:** `A_W` is the Riesz operator of the **unnormalized original Wilson Haar-reference 12-color sum**; `D₁₂` is the normalized **physical conditional-projection** Dirichlet operator. Pair-Haar coordinate conditional expectations form a third, independent reference construction. None may be silently identified with another.
5. **Source detection and continuum mass gap:** positive finite-volume spectral certificates, finite-dimensional source Gram estimates, an H1-C3 strong-limit construction, and the eventual continuum Wightman/OS mass-gap statement are logically separate proof obligations.

## Proved mathematics — scope explicitly limited

### I. Actual finite-volume Wilson operators and physical source geometry

- [#5440 (CO)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5440) proves the qualitative original full-`L²` Wilson kernel description. [#5470–#5472 (DS–DU)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5472) establish finite-volume coercivity, Loewner order and positive restricted spectrum for the **physical** `D₁₂`. [#5473–#5485 (DV–EC)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5485) supply distinct quantitative original Wilson `A_W` Riesz and comparison theorems. The constants retain their exact finite-model scope; they do **not** establish a continuum gap.
- [#5513–#5514 (ES–ET)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5514) prove the original SU(2) six-color spatial cardinality `L_c(H)=4(H+1)^3` and a **relative** `A_W/D₁₂` coefficient obstruction `κ ≤ 3/(H+1)^3` in the stated model. This is **not** a no-go theorem for an absolute continuum mass gap.
- [#5571–#5574 (GI–GL)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5574) bound the original spatial GL/source Gram by an actual two-interacting-posterior expectation-gap square. With `F_a = ∑_i a_i f_i` a physical signed source and `Q_{b,e}(z)=∫(p₀,b-pπ,b)^2\,dν`, the proved finite-volume certificate has the form

  $$
  a^\mathsf{T}G_{b,H}a \;\ge\;
  \frac{e^{-16b}}{2\,\|T_{b,H}\|^2}
  \sum_{e\in E_H}\int
  \frac{\Delta_{b,e,F_a}(z)^2}{Q_{b,e}(z)}\,d\mu_{\mathrm{pair}}(z).
  $$

  Here `Δ` is the **actual difference of the two original interacting Wilson posterior expectations** of the physically normalized signed receiver; the denominator is the genuine posterior density-contrast Haar norm. Positive `Q` by itself does not imply nonzero `Δ` for every source.

### II. Exact physical-source null spaces and restricted positivity

- [#5601–#5606 (HI–HM)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5606) supply continuity and real-linearity for the actual GI detector, a finite authentic-context kernel certificate, and physical-source/receiver Gram and rank identities.
- [#5619–#5621 (HZ–IB)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5621) establish `ker S=ker Φ` for **all finite Krylov depths when the fine coupling is zero**, and for **depth zero at arbitrary nonnegative fine coupling**, given positive frozen coupling. These theorems do **not** imply source separation for all positive-fine higher-depth inputs.
- [#5629–#5630 (IJ–IK)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5630) give the exact kernel/rank criterion for a positive original physical GL/source-norm lower bound and an **unconditional fixed-model upper bound**.
- [#5632–#5639 (IL–IR)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5639) identify the **actual physical invisible subspace** `I_phys=S(ker Φ)`, its orthogonal visible complement, the induced GI quotient and restricted positive finite-model GL/source comparisons. A whole physical source-span lower bound holds **if and only if** `I_phys=0`; that zero-invisibility condition is *not* proved for every positive-fine, positive-depth family.
- Historical [#5365 (P4-Q2-Z2)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5365) constructs a **genuine one-sided small positive-fine interval** preserving a specified original frozen-posterior innovation through a physical top projection. This is a particular physical witness, **not** a full higher-depth GI frame or a scale-uniform bound.

### III. Literal spatial Wilson source and original GI obstruction (JI–JK)

- [#5654–#5656 (JG–JI)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5656) derive the real original Wilson Haar-row sup-norm/`L²` first derivative and the actual GI two-context minor derivative. For fixed frozen `b` and fine `t`, the raw minor has `M_0=0` and `M'_0=-\Delta_W/2`, where

  $$
  \Delta_W(x,y)=G_x(1)G_y(W_H)-G_x(W_H)G_y(1).
  $$

  If an *actual* nonzero `Δ_W` witness exists, the positive-small-fine normalized physical minor is nonzero. Existence of that witness is still **OPEN**.
- [#5657 (JK)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5657) proves the anchor-centered spatial Wilson action `W_H-c_x1` is **nonzero in the original spatial Haar-`L²`**, converts vanishing of all actual spatial GI minors into common-kernel membership and gives an **exact original Wilson posterior double-Haar moment** for the outstanding second-context test. A nonzero source is **not** automatically detected by the GI functional.

### IV. Genuine temporal posterior detection and physical receiver bridge (JL–JS)

Let `D(g)=E_W(g)-E_W(R_\pi^{-1}g)` be the literal SU(2) temporal Wilson action contrast, and `V_{\mathrm{SU(2)}}=\int D(g)^2\,d\nu(g)>0`.

- [#5658–#5661 (JL–JO)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5661) prove the frozen-`b=0` original GI no-go, the true posterior-contrast norm bounds, exact centered logarithmic tangent, and `∫D\,dν=0`. For positive frozen `b` the *actual posterior density contrast* satisfies

  $$
  e^{-32b}\,b^2 V_{\mathrm{SU(2)}}\ \le\
  \int(p_{0,b}-p_{\pi,b})^2\,d\nu
  \ \le\ (e^{16b}-e^{-16b})^2.
  $$

- [#5662 (JP)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5662) proves the **genuine interacting posterior detects the temporal Wilson test**, with `C=272e^8`, `\rho=\min(1/4,V_{\mathrm{SU(2)}}/(4C))>0` and every `0<b<\rho`:

  $$
  \Gamma_b(D)
  :=\int D(g)\big(p_{0,b}(g)-p_{\pi,b}(g)\big)\,d\nu(g)
  \ \le\ -\frac{b}{2}V_{\mathrm{SU(2)}}<0 .
  $$

  The explicitly proved radius is independent of **finite H, chosen physical link, and right Wilson boundary**. This is **temporal** detection, not the outstanding spatial `Δ_W` witness.
- [#5663 (JQ)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5663) inserts the **original Gauss-law physical source receiver** `F_{b,f,e,z}` into that same genuine posterior difference. [#5664 (JR)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5664) subtracts its Haar mean `F_c=F-\int F\,d\nu`, preserving both the true GI gap and temporal covariance. With original positive physical weight `q_b(z)>0`, `0\le b\le1/4`:

  $$
  \left|q_b(z)\,G_b(f,e,z)
  - b\int F_c(g)D(g)\,d\nu(g)\right|
  \ \le\ 272e^8 b^2\,\|F_c\|_\infty.
  $$

  Thus a *verified receiver–`D` correlation* exceeding this error would yield a nonzero **actual** GI response; such a spatial-Wilson correlation has **not** been established.
- [#5665 (JS)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5665) defines the real algebraic span `\mathcal R_{b,e,B}` of **actual physical Wilson source receivers over all physical sources and left contexts at fixed right context/link, together with constants**. For `0<b<\rho` it proves

  $$
  \big[\ \forall f,A,\ G_b(f,e,(A,B))=0\ \big]
  \quad\Longrightarrow\quad
  D\notin\mathcal R_{b,e,B}.
  $$

  Conversely, **if** `D\in\mathcal R_{b,e,B}`, at least one original physical GI response is nonzero. **Membership of `D` is not proved**. The theorem is a real obstruction/conditional witness statement, not an unconditional spatial GI result.

## Explicitly OPEN

**Mathematical frontier:** nonzero **original spatial** `Δ_W(x,y)` at two genuine Wilson physical contexts; the associated actual receiver–temporal contrast covariance or representation mechanism; complete physical-source separation for positive fine coupling and arbitrary depth; uniform-in-volume/spacing/depth original signed-source coercivity and physically justified summable spatial correlations.

**Continuum frontier:** physical coarse/fine compatibility, strong limits with **one common natural-time operator** (H1-C1/C2/C3), a strongly continuous physical time semigroup, OS/Wightman reconstruction, a nontrivial self-adjoint continuum Hamiltonian, and a strictly positive **continuum four-dimensional Yang–Mills mass gap**. Finite-lattice spectral gaps and positive posterior contrasts do not establish these.

No independent-Haar law replaces either original interacting Wilson conditional posterior, no Dobrushin reconstruction is assumed, no generic detector-rank axiom is inserted, and a `sorry`-free local Lean file is not by itself a continuum existence proof.

## Reproduce the exact formal source

Check out the **theorem-authoritative** branch, never silently substitute default `main`:

```bash
git fetch origin formal/real-hilbert-uniform-coercive-strong-limit
git switch --detach d5316fe0a0cf96a8ab8a198bda280ac035585ab4
cat lean-toolchain
# Optional: use an available pinned mathlib cache rather than rebuilding it.
lake exe cache get
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIPhysicalReceiverSpanObstructionV5_JS
```

The JS module imports the JQ/JP evidence; JR is a separately compiled compatible improvement of the same original physical receiver. For a broad repository build run `lake build`; CI's changed-Lean checks use pinned dependencies and restored caches. Inspect the original `#print axioms` output: the newest JS source has no `sorryAx`, but some physical finite-grid theorem dependencies carry *previously identified* `native_decide` axioms. **Do not conflate legacy finite-grid axioms with newly postulated axioms or pretend that all dependencies are axiom-free.**

**[Full proof plan and acceptance gates → ROADMAP.md](ROADMAP.md).** Older long-form README/ROADMAP snapshots remain recoverable from Git history; this living summary deliberately avoids repeating stale “latest” claims and hundreds of historical PR details.
