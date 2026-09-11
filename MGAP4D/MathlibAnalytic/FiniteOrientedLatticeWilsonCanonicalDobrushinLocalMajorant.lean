import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonDobrushinMatrix

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Local geometric data sufficient to prove strictness of the exact oriented
canonical Dobrushin coefficient. -/
structure FiniteOrientedLatticeWilsonCanonicalDobrushinLocalMajorantData
    (L : FiniteOrientedLatticeWilsonSystem) where
  neighbors : L.Edge → Finset L.Edge
  eta : ℝ
  eta_nonneg : 0 ≤ eta
  influence_eq_zero_of_not_mem :
    ∀ target source : L.Edge,
      source ∉ neighbors target →
        L.canonicalDobrushinInfluence target source = 0
  influence_le_eta_of_mem :
    ∀ target source : L.Edge,
      source ∈ neighbors target →
        L.canonicalDobrushinInfluence target source ≤ eta
  degreeBound : ℕ
  neighbor_card_le :
    ∀ target : L.Edge, (neighbors target).card ≤ degreeBound
  degree_mul_eta_lt_one : (degreeBound : ℝ) * eta < 1

/-- Local influence and degree bounds control every exact oriented row sum. -/
theorem finite_oriented_canonicalDobrushinRowSum_le_degree_mul_eta
    (L : FiniteOrientedLatticeWilsonSystem)
    (M : FiniteOrientedLatticeWilsonCanonicalDobrushinLocalMajorantData L)
    (target : L.Edge) :
    L.canonicalDobrushinRowSum target ≤
      (M.degreeBound : ℝ) * M.eta := by
  classical
  have hSupport :
      (∑ e ∈ M.neighbors target,
          L.canonicalDobrushinInfluence target e) =
        ∑ e : L.Edge,
          L.canonicalDobrushinInfluence target e := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _he hNotMem
    exact M.influence_eq_zero_of_not_mem target e hNotMem
  have hCard :
      ((M.neighbors target).card : ℝ) ≤
        (M.degreeBound : ℝ) := by
    exact_mod_cast M.neighbor_card_le target
  unfold FiniteOrientedLatticeWilsonSystem.canonicalDobrushinRowSum
  rw [← hSupport]
  calc
    (∑ e ∈ M.neighbors target,
        L.canonicalDobrushinInfluence target e) ≤
      ∑ _e ∈ M.neighbors target, M.eta := by
        apply Finset.sum_le_sum
        intro e hEdge
        exact M.influence_le_eta_of_mem target e hEdge
    _ = ((M.neighbors target).card : ℝ) * M.eta := by
      simp [nsmul_eq_mul]
    _ ≤ (M.degreeBound : ℝ) * M.eta :=
      mul_le_mul_of_nonneg_right hCard M.eta_nonneg

/-- The exact oriented canonical coefficient is bounded by degree times eta. -/
theorem finite_oriented_canonicalDobrushinCoefficient_le_degree_mul_eta
    (L : FiniteOrientedLatticeWilsonSystem)
    (M : FiniteOrientedLatticeWilsonCanonicalDobrushinLocalMajorantData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalDobrushinCoefficient hEdge ≤
      (M.degreeBound : ℝ) * M.eta := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.canonicalDobrushinCoefficient
  apply Finset.max'_le
  intro r hr
  unfold FiniteOrientedLatticeWilsonSystem.canonicalDobrushinRowSums at hr
  rcases Finset.mem_image.mp hr with ⟨target, _hTarget, rfl⟩
  exact finite_oriented_canonicalDobrushinRowSum_le_degree_mul_eta
    L M target

/-- Local majorant strictness proves strict exact oriented contraction. -/
theorem finite_oriented_canonicalDobrushinCoefficient_lt_one_of_localMajorant
    (L : FiniteOrientedLatticeWilsonSystem)
    (M : FiniteOrientedLatticeWilsonCanonicalDobrushinLocalMajorantData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalDobrushinCoefficient hEdge < 1 :=
  lt_of_le_of_lt
    (finite_oriented_canonicalDobrushinCoefficient_le_degree_mul_eta
      L M hEdge)
    M.degree_mul_eta_lt_one

end

end MathlibAnalytic
end MGAP4D
