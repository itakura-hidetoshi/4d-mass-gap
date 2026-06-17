import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalCenteredVariationProfile
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinMatrix

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- All exact conditional-TV changes obtained by changing only `source`, as
seen by the conditional law at `target`. -/
noncomputable def
    FiniteLatticeWilsonSystem.canonicalDobrushinInfluenceValues
    (L : FiniteLatticeWilsonSystem)
    (target source : L.Edge) : Finset ℝ := by
  classical
  letI : Fintype L.Configuration := Fintype.ofFinite L.Configuration
  exact Finset.univ.image fun p : L.Configuration × L.Gauge =>
    L.singleLinkConditionalTotalVariation p.1
      (L.replaceLink p.1 source p.2) target

/-- The exact finite influence-value set is nonempty. -/
theorem finite_lattice_canonicalDobrushinInfluenceValues_nonempty
    (L : FiniteLatticeWilsonSystem)
    (target source : L.Edge) :
    (L.canonicalDobrushinInfluenceValues target source).Nonempty := by
  classical
  refine ⟨L.singleLinkConditionalTotalVariation default
    (L.replaceLink default source default) target, ?_⟩
  simp [FiniteLatticeWilsonSystem.canonicalDobrushinInfluenceValues]

/-- The canonical Wilson influence coefficient.  The diagonal is exactly zero;
off the diagonal it is the largest realizable conditional-TV change caused by
one source-link perturbation. -/
noncomputable def FiniteLatticeWilsonSystem.canonicalDobrushinInfluence
    (L : FiniteLatticeWilsonSystem)
    (target source : L.Edge) : ℝ :=
  if target = source then 0
  else
    (L.canonicalDobrushinInfluenceValues target source).max'
      (finite_lattice_canonicalDobrushinInfluenceValues_nonempty
        L target source)

/-- Canonical Wilson influences are nonnegative. -/
theorem finite_lattice_canonicalDobrushinInfluence_nonneg
    (L : FiniteLatticeWilsonSystem)
    (target source : L.Edge) :
    0 ≤ L.canonicalDobrushinInfluence target source := by
  classical
  by_cases h : target = source
  · simp [FiniteLatticeWilsonSystem.canonicalDobrushinInfluence, h]
  · rw [FiniteLatticeWilsonSystem.canonicalDobrushinInfluence, if_neg h]
    exact le_trans
      (finite_lattice_singleLinkConditionalTotalVariation_nonneg
        L default (L.replaceLink default source default) target)
      (Finset.le_max'
        (L.canonicalDobrushinInfluenceValues target source)
        (L.singleLinkConditionalTotalVariation default
          (L.replaceLink default source default) target)
        (by
          simp [FiniteLatticeWilsonSystem.canonicalDobrushinInfluenceValues]))

/-- The canonical influence has exact zero diagonal. -/
@[simp] theorem finite_lattice_canonicalDobrushinInfluence_diagonal
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) :
    L.canonicalDobrushinInfluence e e = 0 := by
  simp [FiniteLatticeWilsonSystem.canonicalDobrushinInfluence]

/-- Every admissible one-link change is dominated by the canonical exact
influence coefficient. -/
theorem finite_lattice_singleLinkConditionalTotalVariation_le_canonicalDobrushinInfluence
    (L : FiniteLatticeWilsonSystem)
    (target source : L.Edge)
    (A B : L.Configuration)
    (hAgree : L.AgreeOffLink A B source) :
    L.singleLinkConditionalTotalVariation A B target ≤
      L.canonicalDobrushinInfluence target source := by
  classical
  by_cases h : target = source
  · subst target
    rw [finite_lattice_canonicalDobrushinInfluence_diagonal]
    exact le_of_eq
      (finite_lattice_singleLinkConditionalTotalVariation_eq_zero_of_agreeOffLink
        L A B source hAgree)
  · rw [FiniteLatticeWilsonSystem.canonicalDobrushinInfluence, if_neg h]
    apply Finset.le_max'
    change
      L.singleLinkConditionalTotalVariation A B target ∈
        L.canonicalDobrushinInfluenceValues target source
    have hReplace : L.replaceLink A source (B source) = B :=
      finite_lattice_replaceLink_right_of_agreeOffLink
        L A B source hAgree
    simp [FiniteLatticeWilsonSystem.canonicalDobrushinInfluenceValues,
      hReplace]

/-- Canonical row sum of exact single-link influences. -/
def FiniteLatticeWilsonSystem.canonicalDobrushinRowSum
    (L : FiniteLatticeWilsonSystem)
    (target : L.Edge) : ℝ :=
  ∑ source : L.Edge, L.canonicalDobrushinInfluence target source

/-- Every canonical Dobrushin row sum is nonnegative. -/
theorem finite_lattice_canonicalDobrushinRowSum_nonneg
    (L : FiniteLatticeWilsonSystem)
    (target : L.Edge) :
    0 ≤ L.canonicalDobrushinRowSum target := by
  unfold FiniteLatticeWilsonSystem.canonicalDobrushinRowSum
  exact Finset.sum_nonneg fun source _ =>
    finite_lattice_canonicalDobrushinInfluence_nonneg L target source

/-- The finite set of all canonical Dobrushin row sums. -/
noncomputable def FiniteLatticeWilsonSystem.canonicalDobrushinRowSums
    (L : FiniteLatticeWilsonSystem) : Finset ℝ := by
  classical
  exact Finset.univ.image L.canonicalDobrushinRowSum

/-- A nonempty edge set gives a nonempty finite set of row sums. -/
theorem finite_lattice_canonicalDobrushinRowSums_nonempty
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalDobrushinRowSums.Nonempty := by
  classical
  let e : L.Edge := Classical.choice (Fintype.card_pos_iff.mp hEdge)
  refine ⟨L.canonicalDobrushinRowSum e, ?_⟩
  simp [FiniteLatticeWilsonSystem.canonicalDobrushinRowSums]

/-- The canonical Dobrushin coefficient is the largest exact influence row sum. -/
noncomputable def FiniteLatticeWilsonSystem.canonicalDobrushinCoefficient
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) : ℝ :=
  L.canonicalDobrushinRowSums.max'
    (finite_lattice_canonicalDobrushinRowSums_nonempty L hEdge)

/-- Every exact canonical row sum is bounded by the canonical coefficient. -/
theorem finite_lattice_canonicalDobrushinRowSum_le_coefficient
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (target : L.Edge) :
    L.canonicalDobrushinRowSum target ≤
      L.canonicalDobrushinCoefficient hEdge := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalDobrushinCoefficient
  apply Finset.le_max'
  simp [FiniteLatticeWilsonSystem.canonicalDobrushinRowSums]

/-- The canonical Dobrushin coefficient is nonnegative. -/
theorem finite_lattice_canonicalDobrushinCoefficient_nonneg
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    0 ≤ L.canonicalDobrushinCoefficient hEdge := by
  let e : L.Edge := Classical.choice (Fintype.card_pos_iff.mp hEdge)
  exact le_trans
    (finite_lattice_canonicalDobrushinRowSum_nonneg L e)
    (finite_lattice_canonicalDobrushinRowSum_le_coefficient L hEdge e)

/-- Once the single scalar strictness inequality is proved, the entire
proof-relevant Dobrushin matrix certificate is generated canonically. -/
noncomputable def finiteLatticeWilsonCanonicalDobrushinMatrixData
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (hStrict : L.canonicalDobrushinCoefficient hEdge < 1) :
    FiniteLatticeWilsonDobrushinMatrixData L :=
  { influence := L.canonicalDobrushinInfluence
    influence_nonneg := finite_lattice_canonicalDobrushinInfluence_nonneg L
    influence_diagonal_zero :=
      finite_lattice_canonicalDobrushinInfluence_diagonal L
    conditionalTotalVariation_le := by
      intro target source A B hAgree
      exact
        finite_lattice_singleLinkConditionalTotalVariation_le_canonicalDobrushinInfluence
          L target source A B hAgree
    dobrushinCoefficient := L.canonicalDobrushinCoefficient hEdge
    dobrushinCoefficient_nonneg :=
      finite_lattice_canonicalDobrushinCoefficient_nonneg L hEdge
    rowSum_le_coefficient := by
      intro target
      exact finite_lattice_canonicalDobrushinRowSum_le_coefficient
        L hEdge target
    dobrushinCoefficient_lt_one := hStrict }

end

end MathlibAnalytic
end MGAP4D
