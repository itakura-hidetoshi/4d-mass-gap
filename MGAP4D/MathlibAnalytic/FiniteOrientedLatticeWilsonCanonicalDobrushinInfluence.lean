import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalActionOscillationTV

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Oriented single-link conditional total variation is nonnegative. -/
theorem finite_oriented_singleLinkConditionalTotalVariation_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target : L.Edge) :
    0 ≤ L.singleLinkConditionalTotalVariation A B target := by
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkConditionalTotalVariation
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun g _hg => abs_nonneg _)

/-- All exact conditional-TV changes obtained by changing only `source`, as
seen by the oriented conditional law at `target`. -/
noncomputable def
    FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluenceValues
    (L : FiniteOrientedLatticeWilsonSystem)
    (target source : L.Edge) : Finset ℝ := by
  classical
  exact Finset.univ.image fun p : L.Configuration × L.Gauge =>
    L.singleLinkConditionalTotalVariation p.1
      (L.replaceLink p.1 source p.2) target

/-- The exact finite oriented influence-value set is nonempty. -/
theorem finite_oriented_canonicalDobrushinInfluenceValues_nonempty
    (L : FiniteOrientedLatticeWilsonSystem)
    (target source : L.Edge) :
    (L.canonicalDobrushinInfluenceValues target source).Nonempty := by
  classical
  refine ⟨L.singleLinkConditionalTotalVariation default
    (L.replaceLink default source default) target, ?_⟩
  unfold FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluenceValues
  apply Finset.mem_image.mpr
  exact ⟨(default, default), Finset.mem_univ _, rfl⟩

/-- Exact oriented canonical influence, with an exact zero diagonal. -/
noncomputable def
    FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluence
    (L : FiniteOrientedLatticeWilsonSystem)
    (target source : L.Edge) : ℝ := by
  classical
  exact if target = source then 0
    else
      (L.canonicalDobrushinInfluenceValues target source).max'
        (finite_oriented_canonicalDobrushinInfluenceValues_nonempty
          L target source)

/-- Exact oriented canonical influences are nonnegative. -/
theorem finite_oriented_canonicalDobrushinInfluence_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (target source : L.Edge) :
    0 ≤ L.canonicalDobrushinInfluence target source := by
  classical
  by_cases h : target = source
  · simp [FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluence, h]
  · rw [FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluence,
      if_neg h]
    exact le_trans
      (finite_oriented_singleLinkConditionalTotalVariation_nonneg
        L default (L.replaceLink default source default) target)
      (Finset.le_max'
        (L.canonicalDobrushinInfluenceValues target source)
        (L.singleLinkConditionalTotalVariation default
          (L.replaceLink default source default) target)
        (by
          unfold FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluenceValues
          apply Finset.mem_image.mpr
          exact ⟨(default, default), Finset.mem_univ _, rfl⟩))

/-- The oriented canonical influence has exact zero diagonal. -/
@[simp] theorem finite_oriented_canonicalDobrushinInfluence_diagonal
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge) :
    L.canonicalDobrushinInfluence e e = 0 := by
  simp [FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluence]

end

end MathlibAnalytic
end MGAP4D
