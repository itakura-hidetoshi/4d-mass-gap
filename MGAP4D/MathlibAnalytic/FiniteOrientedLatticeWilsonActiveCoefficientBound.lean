import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalDobrushinCoefficient

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Exact active support, a local influence bound, and active-neighbor
cardinality control every oriented canonical row sum. -/
theorem finite_oriented_canonicalDobrushinRowSum_le_activeCard_mul_eta
    (L : FiniteOrientedLatticeWilsonSystem)
    (eta : ℝ)
    (hEta : 0 ≤ eta)
    (hLocal : ∀ target source : L.Edge,
      source ∈ L.activePlaquetteNeighbors target →
        L.canonicalDobrushinInfluence target source ≤ eta)
    (degreeBound : ℕ)
    (hDegree : ∀ target : L.Edge,
      (L.activePlaquetteNeighbors target).card ≤ degreeBound)
    (target : L.Edge) :
    L.canonicalDobrushinRowSum target ≤
      (degreeBound : ℝ) * eta := by
  classical
  have hSupport :
      (∑ e ∈ L.activePlaquetteNeighbors target,
          L.canonicalDobrushinInfluence target e) =
        ∑ e : L.Edge,
          L.canonicalDobrushinInfluence target e := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _he hNotMem
    exact
      finite_oriented_canonicalDobrushinInfluence_eq_zero_of_not_mem_active
        L target e hNotMem
  have hCard :
      ((L.activePlaquetteNeighbors target).card : ℝ) ≤
        (degreeBound : ℝ) := by
    exact_mod_cast hDegree target
  unfold FiniteOrientedLatticeWilsonSystem.canonicalDobrushinRowSum
  rw [← hSupport]
  calc
    (∑ e ∈ L.activePlaquetteNeighbors target,
        L.canonicalDobrushinInfluence target e) ≤
      ∑ _e ∈ L.activePlaquetteNeighbors target, eta := by
        apply Finset.sum_le_sum
        intro e hEdge
        exact hLocal target e hEdge
    _ = ((L.activePlaquetteNeighbors target).card : ℝ) * eta := by
      simp [nsmul_eq_mul]
    _ ≤ (degreeBound : ℝ) * eta :=
      mul_le_mul_of_nonneg_right hCard hEta

/-- The exact oriented canonical coefficient obeys the same active-cardinality
multiplied by local-influence estimate. -/
theorem finite_oriented_canonicalDobrushinCoefficient_le_activeCard_mul_eta
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (eta : ℝ)
    (hEta : 0 ≤ eta)
    (hLocal : ∀ target source : L.Edge,
      source ∈ L.activePlaquetteNeighbors target →
        L.canonicalDobrushinInfluence target source ≤ eta)
    (degreeBound : ℕ)
    (hDegree : ∀ target : L.Edge,
      (L.activePlaquetteNeighbors target).card ≤ degreeBound) :
    L.canonicalDobrushinCoefficient hEdge ≤
      (degreeBound : ℝ) * eta := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.canonicalDobrushinCoefficient
  apply Finset.max'_le
  intro r hr
  unfold FiniteOrientedLatticeWilsonSystem.canonicalDobrushinRowSums at hr
  rcases Finset.mem_image.mp hr with ⟨target, _hTarget, rfl⟩
  exact finite_oriented_canonicalDobrushinRowSum_le_activeCard_mul_eta
    L eta hEta hLocal degreeBound hDegree target

end

end MathlibAnalytic
end MGAP4D
