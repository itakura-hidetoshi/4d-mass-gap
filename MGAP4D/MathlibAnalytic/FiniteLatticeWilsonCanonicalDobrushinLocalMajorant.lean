import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalDobrushinMatrix

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Local geometric data sufficient to prove strictness of the exact canonical
Dobrushin coefficient.

For each target link, `neighbors target` records the only source links allowed
to influence its conditional law.  Every local influence is bounded by `eta`,
every neighborhood has at most `degreeBound` links, and `degreeBound * eta < 1`.
This isolates the remaining Wilson-action estimate from the already completed
finite spectral-gap argument. -/
structure FiniteLatticeWilsonCanonicalDobrushinLocalMajorantData
    (L : FiniteLatticeWilsonSystem) where
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
  neighbor_card_le : ∀ target : L.Edge,
    (neighbors target).card ≤ degreeBound
  degree_mul_eta_lt_one : (degreeBound : ℝ) * eta < 1

/-- A local influence bound and a degree bound control every exact canonical
Dobrushin row sum. -/
theorem finite_lattice_canonicalDobrushinRowSum_le_degree_mul_eta
    (L : FiniteLatticeWilsonSystem)
    (M : FiniteLatticeWilsonCanonicalDobrushinLocalMajorantData L)
    (target : L.Edge) :
    L.canonicalDobrushinRowSum target ≤ (M.degreeBound : ℝ) * M.eta := by
  classical
  have hSupport :
      (∑ e in M.neighbors target,
          L.canonicalDobrushinInfluence target e) =
        ∑ e : L.Edge,
          L.canonicalDobrushinInfluence target e := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _he hNotMem
    exact M.influence_eq_zero_of_not_mem target e hNotMem
  have hCard :
      ((M.neighbors target).card : ℝ) ≤ (M.degreeBound : ℝ) := by
    exact_mod_cast M.neighbor_card_le target
  unfold FiniteLatticeWilsonSystem.canonicalDobrushinRowSum
  rw [← hSupport]
  calc
    (∑ e in M.neighbors target,
        L.canonicalDobrushinInfluence target e) ≤
      ∑ _e in M.neighbors target, M.eta := by
        apply Finset.sum_le_sum
        intro e hEdge
        exact M.influence_le_eta_of_mem target e hEdge
    _ = ((M.neighbors target).card : ℝ) * M.eta := by
      simp [nsmul_eq_mul]
    _ ≤ (M.degreeBound : ℝ) * M.eta :=
      mul_le_mul_of_nonneg_right hCard M.eta_nonneg

/-- The exact canonical Dobrushin coefficient is bounded by the local degree
bound times the uniform local influence bound. -/
theorem finite_lattice_canonicalDobrushinCoefficient_le_degree_mul_eta
    (L : FiniteLatticeWilsonSystem)
    (M : FiniteLatticeWilsonCanonicalDobrushinLocalMajorantData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalDobrushinCoefficient hEdge ≤
      (M.degreeBound : ℝ) * M.eta := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalDobrushinCoefficient
  apply Finset.max'_le
  intro r hr
  unfold FiniteLatticeWilsonSystem.canonicalDobrushinRowSums at hr
  rcases Finset.mem_image.mp hr with ⟨target, _hTarget, rfl⟩
  exact finite_lattice_canonicalDobrushinRowSum_le_degree_mul_eta
    L M target

/-- Locality, a uniform local influence bound, and `degreeBound * eta < 1`
prove strictness of the exact canonical Dobrushin coefficient. -/
theorem finite_lattice_canonicalDobrushinCoefficient_lt_one_of_localMajorant
    (L : FiniteLatticeWilsonSystem)
    (M : FiniteLatticeWilsonCanonicalDobrushinLocalMajorantData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalDobrushinCoefficient hEdge < 1 :=
  lt_of_le_of_lt
    (finite_lattice_canonicalDobrushinCoefficient_le_degree_mul_eta
      L M hEdge)
    M.degree_mul_eta_lt_one

/-- Local Wilson-action majorants generate the entire proof-relevant exact
canonical Dobrushin matrix. -/
noncomputable def finiteLatticeWilsonCanonicalDobrushinMatrixDataOfLocalMajorant
    (L : FiniteLatticeWilsonSystem)
    (M : FiniteLatticeWilsonCanonicalDobrushinLocalMajorantData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    FiniteLatticeWilsonDobrushinMatrixData L :=
  finiteLatticeWilsonCanonicalDobrushinMatrixData L hEdge
    (finite_lattice_canonicalDobrushinCoefficient_lt_one_of_localMajorant
      L M hEdge)

end

end MathlibAnalytic
end MGAP4D
