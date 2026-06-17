import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalDobrushinMatrix

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The exact canonical influence is pointwise no larger than every admissible
Dobrushin influence matrix. -/
theorem finite_lattice_canonicalDobrushinInfluence_le
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (target source : L.Edge) :
    L.canonicalDobrushinInfluence target source ≤
      D.influence target source := by
  classical
  by_cases h : target = source
  · subst target
    rw [finite_lattice_canonicalDobrushinInfluence_diagonal]
    exact D.influence_nonneg source source
  · rw [FiniteLatticeWilsonSystem.canonicalDobrushinInfluence, if_neg h]
    apply Finset.max'_le
    intro r hr
    unfold FiniteLatticeWilsonSystem.canonicalDobrushinInfluenceValues at hr
    rcases Finset.mem_image.mp hr with ⟨p, _hp, rfl⟩
    exact D.conditionalTotalVariation_le target source p.1
      (L.replaceLink p.1 source p.2) (by
        intro e he
        simp [FiniteLatticeWilsonSystem.replaceLink, he])

/-- Consequently, every canonical influence row sum is no larger than the
corresponding row sum of any admissible Dobrushin matrix. -/
theorem finite_lattice_canonicalDobrushinRowSum_le
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (target : L.Edge) :
    L.canonicalDobrushinRowSum target ≤
      ∑ source : L.Edge, D.influence target source := by
  unfold FiniteLatticeWilsonSystem.canonicalDobrushinRowSum
  apply Finset.sum_le_sum
  intro source _hsource
  exact finite_lattice_canonicalDobrushinInfluence_le L D target source

/-- The canonical exact Dobrushin coefficient is the least coefficient among all
proof-relevant Dobrushin matrix certificates for the same finite Wilson law. -/
theorem finite_lattice_canonicalDobrushinCoefficient_le
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalDobrushinCoefficient hEdge ≤ D.dobrushinCoefficient := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalDobrushinCoefficient
  apply Finset.max'_le
  intro r hr
  unfold FiniteLatticeWilsonSystem.canonicalDobrushinRowSums at hr
  rcases Finset.mem_image.mp hr with ⟨target, _htarget, rfl⟩
  exact le_trans
    (finite_lattice_canonicalDobrushinRowSum_le L D target)
    (D.rowSum_le_coefficient target)

/-- Any strict Dobrushin certificate therefore implies strictness of the exact
canonical coefficient. -/
theorem finite_lattice_canonicalDobrushinCoefficient_lt_one_of_matrixData
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalDobrushinCoefficient hEdge < 1 :=
  lt_of_le_of_lt
    (finite_lattice_canonicalDobrushinCoefficient_le L D hEdge)
    D.dobrushinCoefficient_lt_one

/-- Every externally supplied strict Dobrushin matrix can be replaced by the
canonical least exact matrix without weakening the coefficient. -/
noncomputable def finiteLatticeWilsonCanonicalDobrushinMatrixDataOfMatrixData
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    FiniteLatticeWilsonDobrushinMatrixData L :=
  finiteLatticeWilsonCanonicalDobrushinMatrixData L hEdge
    (finite_lattice_canonicalDobrushinCoefficient_lt_one_of_matrixData
      L D hEdge)

end

end MathlibAnalytic
end MGAP4D
