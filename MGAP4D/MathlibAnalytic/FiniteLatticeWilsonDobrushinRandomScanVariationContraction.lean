import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinTotalVariationContraction
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinRandomScanScale

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The linkwise variation profile obtained by uniformly averaging the sharp
single-target Dobrushin update profiles.  This is the variation-level analogue
of the concrete random-scan heat-bath sweep; no Gibbs `L²` conclusion is
asserted here. -/
noncomputable def finiteLatticeWilsonDobrushinRandomScanUpdatedVariation
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (source : L.Edge) : ℝ :=
  (Fintype.card L.Edge : ℝ)⁻¹ *
    ∑ target : L.Edge,
      finiteLatticeWilsonDobrushinUpdatedVariation
        D variation target source

/-- A nonnegative variation profile remains nonnegative after uniform
random-scan averaging. -/
theorem finite_lattice_dobrushinRandomScanUpdatedVariation_nonneg
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (hVariation : ∀ e : L.Edge, 0 ≤ variation e)
    (source : L.Edge) :
    0 ≤ finiteLatticeWilsonDobrushinRandomScanUpdatedVariation
      D variation source := by
  unfold finiteLatticeWilsonDobrushinRandomScanUpdatedVariation
  exact mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun target _ =>
      finite_lattice_dobrushinUpdatedVariation_nonneg
        D variation hVariation target source))

/-- Summing the averaged profile over source links is the normalized average
of the single-target total variations. -/
theorem finite_lattice_dobrushinRandomScanUpdatedVariation_total_eq
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ) :
    finiteLatticeWilsonTotalVariation
        (finiteLatticeWilsonDobrushinRandomScanUpdatedVariation
          D variation) =
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ target : L.Edge,
          finiteLatticeWilsonTotalVariation
            (finiteLatticeWilsonDobrushinUpdatedVariation
              D variation target) := by
  classical
  unfold finiteLatticeWilsonTotalVariation
  unfold finiteLatticeWilsonDobrushinRandomScanUpdatedVariation
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]

/-- Uniform random-scan averaging contracts total link variation by the
standard Dobrushin rate `1 - (1 - α) / |E|`.  This theorem lives entirely in
the finite oscillation-seminorm layer and is not an `L²(μ)` Rayleigh theorem. -/
theorem finite_lattice_dobrushinRandomScanUpdatedVariation_total_le_rate_mul
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (hVariation : ∀ e : L.Edge, 0 ≤ variation e)
    (hEdge : 0 < Fintype.card L.Edge) :
    finiteLatticeWilsonTotalVariation
        (finiteLatticeWilsonDobrushinRandomScanUpdatedVariation
          D variation) ≤
      finiteLatticeWilsonDobrushinRandomScanRate L D *
        finiteLatticeWilsonTotalVariation variation := by
  let n : ℝ := Fintype.card L.Edge
  let total : ℝ := finiteLatticeWilsonTotalVariation variation
  let gap : ℝ := finiteLatticeWilsonDobrushinHeatBathGap D
  have hCardPos : 0 < n := by
    exact Nat.cast_pos.mpr hEdge
  have hCardNe : n ≠ 0 := ne_of_gt hCardPos
  have hInvNonneg : 0 ≤ n⁻¹ :=
    inv_nonneg.mpr (le_of_lt hCardPos)
  have hTargetSum :
      (∑ target : L.Edge,
          finiteLatticeWilsonTotalVariation
            (finiteLatticeWilsonDobrushinUpdatedVariation
              D variation target)) ≤
        ∑ target : L.Edge,
          (total - gap * variation target) := by
    apply Finset.sum_le_sum
    intro target _htarget
    exact finite_lattice_dobrushinUpdatedVariation_total_le
      D variation hVariation target
  have hConstSum :
      (∑ _target : L.Edge, total) = n * total := by
    simp [n, nsmul_eq_mul]
  have hDropSum :
      (∑ target : L.Edge, gap * variation target) =
        gap * total := by
    unfold total finiteLatticeWilsonTotalVariation
    rw [← Finset.mul_sum]
  rw [finite_lattice_dobrushinRandomScanUpdatedVariation_total_eq]
  change n⁻¹ *
      (∑ target : L.Edge,
        finiteLatticeWilsonTotalVariation
          (finiteLatticeWilsonDobrushinUpdatedVariation
            D variation target)) ≤
    finiteLatticeWilsonDobrushinRandomScanRate L D * total
  calc
    n⁻¹ *
        (∑ target : L.Edge,
          finiteLatticeWilsonTotalVariation
            (finiteLatticeWilsonDobrushinUpdatedVariation
              D variation target)) ≤
      n⁻¹ * ∑ target : L.Edge,
        (total - gap * variation target) :=
      mul_le_mul_of_nonneg_left hTargetSum hInvNonneg
    _ = n⁻¹ * (n * total - gap * total) := by
      rw [Finset.sum_sub_distrib, hConstSum, hDropSum]
    _ = finiteLatticeWilsonDobrushinRandomScanRate L D * total := by
      dsimp [n, gap]
      unfold finiteLatticeWilsonDobrushinRandomScanRate
      field_simp [hCardNe]

end

end MathlibAnalytic
end MGAP4D
