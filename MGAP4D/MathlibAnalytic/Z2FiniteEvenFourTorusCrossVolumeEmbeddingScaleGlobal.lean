import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeOneStepProjectiveFirstVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The apparent orbit-dependent pointwise scale of the canonical invariant
coarse embedding is in fact the single global finite-volume cardinality ratio.
The orbit masses cancel exactly against the pushforward-probability weights. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingGlobalScale
    (H : ℕ) : ℝ :=
  Real.sqrt
      ((Fintype.card
        (FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H)) : ℝ)⁻¹) /
    Real.sqrt
      ((Fintype.card
        (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹)

/-- Exact cancellation of fine/coarse orbit masses in the normalized
cross-volume embedding scale. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_global
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A =
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingGlobalScale H := by
  let qf := finiteEvenFourTorusZ2FineGaugeOrbitOfConfiguration H A
  let qc := finiteEvenFourTorusZ2CoarseGaugeOrbitOfFineConfiguration H A
  let Gf := FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
    (finiteEvenFourTorusDoubleRefinement H)
  let αf := FiniteEvenFourTorusZ2SliceConfiguration
    (finiteEvenFourTorusDoubleRefinement H)
  let Gc := FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H
  let αc := FiniteEvenFourTorusZ2SliceConfiguration H
  have hmf : 0 < finiteGroupOrbitMass Gf αf qf :=
    finiteGroupOrbitMass_pos Gf αf qf
  have hmc : 0 < finiteGroupOrbitMass Gc αc qc :=
    finiteGroupOrbitMass_pos Gc αc qc
  have hnf : 0 < (Fintype.card αf : ℝ)⁻¹ := by
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hnc : 0 < (Fintype.card αc : ℝ)⁻¹ := by
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hsmf : Real.sqrt (finiteGroupOrbitMass Gf αf qf) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hmf)
  have hsmc : Real.sqrt (finiteGroupOrbitMass Gc αc qc) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hmc)
  have hsnf : Real.sqrt ((Fintype.card αf : ℝ)⁻¹) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hnf)
  have hsnc : Real.sqrt ((Fintype.card αc : ℝ)⁻¹) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hnc)
  unfold finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale
  unfold finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingGlobalScale
  change
    (Real.sqrt
        (finiteGroupOrbitMass Gf αf qf * (Fintype.card αf : ℝ)⁻¹) *
      (Real.sqrt (finiteGroupOrbitMass Gc αc qc) /
        Real.sqrt
          (finiteGroupOrbitMass Gc αc qc * (Fintype.card αc : ℝ)⁻¹))) /
        Real.sqrt (finiteGroupOrbitMass Gf αf qf) =
      Real.sqrt ((Fintype.card αf : ℝ)⁻¹) /
        Real.sqrt ((Fintype.card αc : ℝ)⁻¹)
  rw [Real.sqrt_mul (le_of_lt hmf), Real.sqrt_mul (le_of_lt hmc)]
  field_simp [hsmf, hsmc, hsnf, hsnc]

/-- Hence the exact pointwise scale is independent of the fine
configuration. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq
    (H : ℕ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A =
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B := by
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_global,
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_global]

/-- The global scale is strictly positive. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingGlobalScale_pos
    (H : ℕ) :
    0 < finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingGlobalScale H := by
  rw [← finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_global
    H (1 : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))]
  exact finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_pos H 1

end

end MathlibAnalytic
end MGAP4D