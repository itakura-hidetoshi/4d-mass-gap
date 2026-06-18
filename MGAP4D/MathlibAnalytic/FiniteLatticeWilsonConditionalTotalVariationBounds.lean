import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonExactPlaquetteDobrushinProfile
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathProjection

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The finite total-variation distance between two finite probability mass
functions is at most one. -/
theorem finite_pmf_totalVariation_le_one
    {α : Type*} [Fintype α]
    (p q : PMF α) :
    (2 : ℝ)⁻¹ *
        ∑ a : α, |(p a).toReal - (q a).toReal| ≤ 1 := by
  classical
  have hTerm : ∀ a : α,
      |(p a).toReal - (q a).toReal| ≤
        (p a).toReal + (q a).toReal := by
    intro a
    have hp : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
    have hq : 0 ≤ (q a).toReal := ENNReal.toReal_nonneg
    simpa [sub_eq_add_neg, abs_of_nonneg hp, abs_of_nonneg hq] using
      (abs_add (p a).toReal (-(q a).toReal))
  calc
    (2 : ℝ)⁻¹ *
          ∑ a : α, |(p a).toReal - (q a).toReal| ≤
        (2 : ℝ)⁻¹ *
          ∑ a : α, ((p a).toReal + (q a).toReal) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro a _ha
        exact hTerm a
      · positivity
    _ = (2 : ℝ)⁻¹ *
        ((∑ a : α, (p a).toReal) +
          ∑ a : α, (q a).toReal) := by
      rw [Finset.sum_add_distrib]
    _ = 1 := by
      rw [finite_pmf_sum_toReal_eq_one,
        finite_pmf_sum_toReal_eq_one]
      norm_num

/-- Every exact Wilson single-link conditional total-variation response lies in
the unit interval. -/
theorem finite_lattice_singleLinkConditionalTotalVariation_le_one
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (target : L.Edge) :
    L.singleLinkConditionalTotalVariation A B target ≤ 1 := by
  classical
  unfold FiniteLatticeWilsonSystem.singleLinkConditionalTotalVariation
  exact finite_pmf_totalVariation_le_one
    (L.singleLinkConditionalPMF A target)
    (L.singleLinkConditionalPMF B target)

/-- Every exact canonical Dobrushin influence coefficient is at most one. -/
theorem finite_lattice_canonicalDobrushinInfluence_le_one
    (L : FiniteLatticeWilsonSystem)
    (target source : L.Edge) :
    L.canonicalDobrushinInfluence target source ≤ 1 := by
  classical
  by_cases hDiagonal : target = source
  · subst source
    rw [finite_lattice_canonicalDobrushinInfluence_diagonal]
    norm_num
  · rw [FiniteLatticeWilsonSystem.canonicalDobrushinInfluence,
      if_neg hDiagonal]
    apply Finset.max'_le
    intro r hr
    unfold FiniteLatticeWilsonSystem.canonicalDobrushinInfluenceValues at hr
    rcases Finset.mem_image.mp hr with ⟨p, _hp, rfl⟩
    exact finite_lattice_singleLinkConditionalTotalVariation_le_one
      L p.1 (L.replaceLink p.1 source p.2) target

/-- The exact largest plaquette-local canonical influence also lies in the unit
interval. -/
theorem finite_lattice_canonicalPlaquetteLocalInfluenceBound_le_one
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalPlaquetteLocalInfluenceBound hEdge ≤ 1 := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalPlaquetteLocalInfluenceBound
  apply Finset.max'_le
  intro r hr
  unfold FiniteLatticeWilsonSystem.canonicalPlaquetteLocalInfluenceValues at hr
  rcases Finset.mem_image.mp hr with ⟨p, _hp, rfl⟩
  by_cases hNeighbor : p.2 ∈ L.plaquetteNeighbors p.1
  · simp only [if_pos hNeighbor]
    exact finite_lattice_canonicalDobrushinInfluence_le_one L p.1 p.2
  · simp [hNeighbor]

/-- Thus the exact local influence maximum belongs to `[0,1]`. -/
theorem finite_lattice_canonicalPlaquetteLocalInfluenceBound_mem_unitInterval
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.canonicalPlaquetteLocalInfluenceBound hEdge ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨finite_lattice_canonicalPlaquetteLocalInfluenceBound_nonneg L hEdge,
    finite_lattice_canonicalPlaquetteLocalInfluenceBound_le_one L hEdge⟩

end

end MathlibAnalytic
end MGAP4D
