import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinVariationProfile

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The sum of the linkwise variation bounds.  This is a finite oscillation
seminorm; it is not yet the Gibbs `L²` norm or a Rayleigh quotient. -/
def finiteLatticeWilsonTotalVariation
    {L : FiniteLatticeWilsonSystem}
    (variation : L.Edge → ℝ) : ℝ :=
  ∑ e : L.Edge, variation e

/-- The sharp updated variation profile has an exact finite-sum expression:
the target variation is removed and the target row of the influence matrix is
transported with weight `variation target`. -/
theorem finite_lattice_dobrushinUpdatedVariation_sum_eq
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (target : L.Edge) :
    (∑ source : L.Edge,
        finiteLatticeWilsonDobrushinUpdatedVariation
          D variation target source) =
      (∑ source : L.Edge, variation source) +
        (∑ source : L.Edge, D.influence target source) *
          variation target - variation target := by
  classical
  have hPointwise (source : L.Edge) :
      finiteLatticeWilsonDobrushinUpdatedVariation
          D variation target source =
        variation source +
          D.influence target source * variation target -
          (if source = target then variation target else 0) := by
    by_cases h : source = target
    · subst source
      simp [finiteLatticeWilsonDobrushinUpdatedVariation,
        D.influence_diagonal_zero]
    · simp [finiteLatticeWilsonDobrushinUpdatedVariation, h]
  calc
    (∑ source : L.Edge,
        finiteLatticeWilsonDobrushinUpdatedVariation
          D variation target source) =
      ∑ source : L.Edge,
        (variation source +
          D.influence target source * variation target -
          (if source = target then variation target else 0)) := by
      apply Finset.sum_congr rfl
      intro source _hsource
      exact hPointwise source
    _ = (∑ source : L.Edge, variation source) +
        (∑ source : L.Edge, D.influence target source) *
          variation target - variation target := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_mul]
      simp

/-- One exact target-link heat-bath update decreases total variation by at
least `(1 - α) * variation target`, where `α` is the certified Dobrushin
coefficient. -/
theorem finite_lattice_dobrushinUpdatedVariation_total_le
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (hVariation : ∀ e : L.Edge, 0 ≤ variation e)
    (target : L.Edge) :
    finiteLatticeWilsonTotalVariation
        (finiteLatticeWilsonDobrushinUpdatedVariation
          D variation target) ≤
      finiteLatticeWilsonTotalVariation variation -
        (1 - D.dobrushinCoefficient) * variation target := by
  have hRowMul :
      (∑ source : L.Edge, D.influence target source) *
          variation target ≤
        D.dobrushinCoefficient * variation target :=
    mul_le_mul_of_nonneg_right
      (D.rowSum_le_coefficient target)
      (hVariation target)
  unfold finiteLatticeWilsonTotalVariation
  rw [finite_lattice_dobrushinUpdatedVariation_sum_eq]
  calc
    (∑ source : L.Edge, variation source) +
          (∑ source : L.Edge, D.influence target source) *
            variation target - variation target ≤
      (∑ source : L.Edge, variation source) +
          D.dobrushinCoefficient * variation target -
            variation target :=
      sub_le_sub_right (add_le_add_left hRowMul _) _
    _ = (∑ source : L.Edge, variation source) -
        (1 - D.dobrushinCoefficient) * variation target := by
      ring

/-- Since the certified Dobrushin coefficient is below one, a single update
never increases total variation. -/
theorem finite_lattice_dobrushinUpdatedVariation_total_le_original
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (hVariation : ∀ e : L.Edge, 0 ≤ variation e)
    (target : L.Edge) :
    finiteLatticeWilsonTotalVariation
        (finiteLatticeWilsonDobrushinUpdatedVariation
          D variation target) ≤
      finiteLatticeWilsonTotalVariation variation := by
  have hOneSub : 0 ≤ 1 - D.dobrushinCoefficient :=
    sub_nonneg.mpr (le_of_lt D.dobrushinCoefficient_lt_one)
  have hDrop :
      0 ≤ (1 - D.dobrushinCoefficient) * variation target :=
    mul_nonneg hOneSub (hVariation target)
  exact le_trans
    (finite_lattice_dobrushinUpdatedVariation_total_le
      D variation hVariation target)
    (sub_le_self _ hDrop)

end

end MathlibAnalytic
end MGAP4D
