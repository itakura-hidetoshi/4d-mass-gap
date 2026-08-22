import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanVariation
import Mathlib.Tactic

/-!
# Finite random-scan variation resolvent profile

For the exact compact-Haar random-scan variation operator `U`, this file keeps
all arguments finite.  Starting from a nonnegative physical-link variation
profile `v`, define recursively

`u₀ = v`, `uₘ₊₁ = U uₘ`

and the finite accumulated profile

`S_M = ∑_{m<M} uₘ`, `w_M = |E|⁻¹ S_M`.

The pointwise random-scan update satisfies the exact algebraic identity

`|E| Uv(s) = (|E|-1) v(s) + ∑_t D(t,s) v(t)`.

A finite telescope therefore gives

`S_M(s) = |E| v(s) + ∑_t D(t,s) S_M(t) - |E| u_M(s)`.

Since the terminal profile `u_M` is nonnegative, no infinite Neumann series or
limit is required to conclude

`w_M(s) ≤ v(s) + ∑_t D(t,s) w_M(t)`.

This is exactly the transpose-subinvariance hypothesis consumed by the
geometric finite resolvent carrier.  The uniform total-mass estimate is kept
for a separate bridge.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Exact finite random-scan iterate of a physical-link variation profile. -/
noncomputable def continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ) : ℕ → C.base.geometry.Edge → ℝ
  | 0 => variation
  | m + 1 =>
      continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
        D (continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
          D variation m)

/-- Exact finite partial sum of random-scan variation iterates. -/
noncomputable def continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationPartialSum
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ) : ℕ → C.base.geometry.Edge → ℝ
  | 0 => fun _ => 0
  | m + 1 => fun source =>
      continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationPartialSum
          D variation m source +
        continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
          D variation m source

/-- The finite partial sum is the literal finite sum of random-scan iterates. -/
theorem continuous_compact_oriented_dobrushinRandomScanVariationPartialSum_eq_sum
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (M : ℕ)
    (source : C.base.geometry.Edge) :
    continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationPartialSum
        D variation M source =
      (Finset.range M).sum
        (fun m =>
          continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
            D variation m source) := by
  induction M with
  | zero =>
      simp [continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationPartialSum]
  | succ M ih =>
      rw [Finset.sum_range_succ]
      simpa [continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationPartialSum]
        using congrArg
          (fun x => x +
            continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
              D variation M source) ih

/-- Nonnegative initial variation remains nonnegative under every finite
random-scan iterate. -/
theorem continuous_compact_oriented_dobrushinRandomScanVariationIterate_nonneg
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (hVariation : ∀ e : C.base.geometry.Edge, 0 ≤ variation e) :
    ∀ m : ℕ, ∀ source : C.base.geometry.Edge,
      0 ≤ continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
        D variation m source := by
  intro m
  induction m with
  | zero =>
      intro source
      exact hVariation source
  | succ m ih =>
      intro source
      exact
        continuous_compact_oriented_dobrushinRandomScanUpdatedVariation_nonneg
          D
          (continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
            D variation m)
          ih source

/-- Exact sum over target links for one random-scan pointwise variation update.
The deleted diagonal target contributes exactly one copy of the source
variation, while the Dobrushin diagonal itself is zero. -/
theorem continuous_compact_oriented_dobrushinRandomScanUpdatedVariation_targetSum_eq
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (source : C.base.geometry.Edge) :
    (∑ target : C.base.geometry.Edge,
      continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
        D variation target source) =
      ((Fintype.card C.base.geometry.Edge : ℝ) - 1) * variation source +
        ∑ target : C.base.geometry.Edge,
          D.influence target source * variation target := by
  classical
  have hPointwise (target : C.base.geometry.Edge) :
      continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
          D variation target source =
        variation source + D.influence target source * variation target -
          (if target = source then variation source else 0) := by
    by_cases h : target = source
    · subst target
      simp [continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation,
        D.influence_diagonal_zero]
    · have h' : source ≠ target := by exact Ne.symm h
      simp [continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation, h, h']
  calc
    (∑ target : C.base.geometry.Edge,
      continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
        D variation target source) =
      ∑ target : C.base.geometry.Edge,
        (variation source + D.influence target source * variation target -
          (if target = source then variation source else 0)) := by
        apply Finset.sum_congr rfl
        intro target _
        exact hPointwise target
    _ =
      (∑ _target : C.base.geometry.Edge, variation source) +
        (∑ target : C.base.geometry.Edge,
          D.influence target source * variation target) - variation source := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        simp
    _ =
      ((Fintype.card C.base.geometry.Edge : ℝ) - 1) * variation source +
        ∑ target : C.base.geometry.Edge,
          D.influence target source * variation target := by
        simp [nsmul_eq_mul]
        ring

/-- Exact pointwise algebra of the uniform random-scan variation operator. -/
theorem continuous_compact_oriented_dobrushinRandomScanUpdatedVariation_card_mul_eq
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (source : C.base.geometry.Edge) :
    (Fintype.card C.base.geometry.Edge : ℝ) *
        continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
          D variation source =
      ((Fintype.card C.base.geometry.Edge : ℝ) - 1) * variation source +
        ∑ target : C.base.geometry.Edge,
          D.influence target source * variation target := by
  let n : ℝ := Fintype.card C.base.geometry.Edge
  have hn : n ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hEdge)
  unfold continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
  change
    n * (n⁻¹ *
      ∑ target : C.base.geometry.Edge,
        continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
          D variation target source) =
      (n - 1) * variation source +
        ∑ target : C.base.geometry.Edge,
          D.influence target source * variation target
  rw [mul_assoc, mul_inv_cancel₀ hn, one_mul]
  exact
    continuous_compact_oriented_dobrushinRandomScanUpdatedVariation_targetSum_eq
      D variation source

/-- Finite random-scan telescope before normalization.  The terminal iterate
appears with a negative coefficient and will later be discarded using
nonnegativity. -/
theorem continuous_compact_oriented_dobrushinRandomScanVariationPartialSum_resolvent_identity
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge) :
    ∀ M : ℕ, ∀ source : C.base.geometry.Edge,
      continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationPartialSum
          D variation M source =
        (Fintype.card C.base.geometry.Edge : ℝ) * variation source +
          (∑ target : C.base.geometry.Edge,
            D.influence target source *
              continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationPartialSum
                D variation M target) -
          (Fintype.card C.base.geometry.Edge : ℝ) *
            continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
              D variation M source := by
  intro M
  induction M with
  | zero =>
      intro source
      simp [continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationPartialSum,
        continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate]
  | succ M ih =>
      intro source
      let n : ℝ := Fintype.card C.base.geometry.Edge
      let S :=
        continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationPartialSum
          D variation M
      let u :=
        continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
          D variation M
      have hRec :=
        continuous_compact_oriented_dobrushinRandomScanUpdatedVariation_card_mul_eq
          D u hEdge source
      change
        S source + u source =
          n * variation source +
            (∑ target : C.base.geometry.Edge,
              D.influence target source * (S target + u target)) -
            n * continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
              D u source
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      symm
      calc
        n * variation source +
              ((∑ target : C.base.geometry.Edge,
                  D.influence target source * S target) +
                ∑ target : C.base.geometry.Edge,
                  D.influence target source * u target) -
            n * continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
              D u source =
          (n * variation source +
              ∑ target : C.base.geometry.Edge,
                D.influence target source * S target - n * u source) +
            u source := by
              change
                n * variation source +
                      ((∑ target : C.base.geometry.Edge,
                          D.influence target source * S target) +
                        ∑ target : C.base.geometry.Edge,
                          D.influence target source * u target) -
                    n * continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
                      D u source =
                  (n * variation source +
                      ∑ target : C.base.geometry.Edge,
                        D.influence target source * S target - n * u source) +
                    u source
              rw [hRec]
              ring
        _ = S source + u source := by
          rw [ih source]

/-- Normalized finite random-scan accumulated variation profile. -/
noncomputable def continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (M : ℕ)
    (source : C.base.geometry.Edge) : ℝ :=
  (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
    continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationPartialSum
      D variation M source

/-- The normalized finite accumulated random-scan profile is nonnegative. -/
theorem continuous_compact_oriented_dobrushinRandomScanFiniteResolventProfile_nonneg
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (hVariation : ∀ e : C.base.geometry.Edge, 0 ≤ variation e)
    (M : ℕ)
    (source : C.base.geometry.Edge) :
    0 ≤ continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
      D variation M source := by
  unfold continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  induction M with
  | zero =>
      simp [continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationPartialSum]
  | succ M ih =>
      change
        0 ≤
          continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationPartialSum
              D variation M source +
            continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
              D variation M source
      exact add_nonneg ih
        (continuous_compact_oriented_dobrushinRandomScanVariationIterate_nonneg
          D variation hVariation M source)

/-- The finite normalized random-scan accumulated profile is already
transpose-subinvariant.  This is the finite Poisson--Neumann input needed by the
geometric resolvent theorem; no limiting profile is constructed. -/
theorem continuous_compact_oriented_dobrushinRandomScanFiniteResolventProfile_subinvariant
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (hVariation : ∀ e : C.base.geometry.Edge, 0 ≤ variation e)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (M : ℕ)
    (source : C.base.geometry.Edge) :
    continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
        D variation M source ≤
      variation source +
        ∑ target : C.base.geometry.Edge,
          D.influence target source *
            continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
              D variation M target := by
  let n : ℝ := Fintype.card C.base.geometry.Edge
  let S :=
    continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationPartialSum
      D variation M
  let uM :=
    continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
      D variation M
  have hnPos : 0 < n := Nat.cast_pos.mpr hEdge
  have hn : n ≠ 0 := ne_of_gt hnPos
  have hTerminal : 0 ≤ uM source :=
    continuous_compact_oriented_dobrushinRandomScanVariationIterate_nonneg
      D variation hVariation M source
  have hIdentity :=
    continuous_compact_oriented_dobrushinRandomScanVariationPartialSum_resolvent_identity
      D variation hEdge M source
  have hSle :
      S source ≤ n * variation source +
        ∑ target : C.base.geometry.Edge, D.influence target source * S target := by
    rw [hIdentity]
    exact sub_le_self _ (mul_nonneg hnPos.le hTerminal)
  unfold continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
  change
    n⁻¹ * S source ≤
      variation source +
        ∑ target : C.base.geometry.Edge,
          D.influence target source * (n⁻¹ * S target)
  calc
    n⁻¹ * S source ≤
        n⁻¹ *
          (n * variation source +
            ∑ target : C.base.geometry.Edge,
              D.influence target source * S target) := by
      exact mul_le_mul_of_nonneg_left hSle (inv_nonneg.mpr hnPos.le)
    _ = variation source +
        ∑ target : C.base.geometry.Edge,
          D.influence target source * (n⁻¹ * S target) := by
      rw [mul_add, Finset.mul_sum]
      have hInvMul : n⁻¹ * n = 1 := inv_mul_cancel₀ hn
      rw [mul_assoc, hInvMul, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro target _
      ring

end

end MathlibAnalytic
end MGAP4D
