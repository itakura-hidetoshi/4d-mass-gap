import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalDobrushinInfluence
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalPlaquetteSupport

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The exact oriented canonical influence vanishes outside the geometric
plaquette-neighbor set. -/
theorem finite_oriented_canonicalDobrushinInfluence_eq_zero_of_not_plaquetteNeighbor
    (L : FiniteOrientedLatticeWilsonSystem)
    (target source : L.Edge)
    (hNotNeighbor : source ∉ L.plaquetteNeighbors target) :
    L.canonicalDobrushinInfluence target source = 0 := by
  classical
  by_cases hDiagonal : target = source
  · subst source
    exact finite_oriented_canonicalDobrushinInfluence_diagonal L target
  · rw [FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluence,
      if_neg hDiagonal]
    apply le_antisymm
    · apply Finset.max'_le
      intro r hr
      unfold
        FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluenceValues at hr
      rcases Finset.mem_image.mp hr with ⟨p, _hp, rfl⟩
      rw [finite_oriented_singleLinkConditionalTotalVariation_eq_zero_of_not_plaquetteNeighbor
        L p.1 (L.replaceLink p.1 source p.2) target source hNotNeighbor]
      intro e he
      simp [FiniteOrientedLatticeWilsonSystem.replaceLink, he]
    · have hNonneg :=
        finite_oriented_canonicalDobrushinInfluence_nonneg L target source
      simpa [FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluence,
        hDiagonal] using hNonneg

/-- After removing the zero diagonal, exact oriented influence is supported on
the active plaquette-neighbor set. -/
theorem finite_oriented_canonicalDobrushinInfluence_eq_zero_of_not_mem_active
    (L : FiniteOrientedLatticeWilsonSystem)
    (target source : L.Edge)
    (hInactive : source ∉ L.activePlaquetteNeighbors target) :
    L.canonicalDobrushinInfluence target source = 0 := by
  classical
  by_cases hDiagonal : target = source
  · subst source
    exact finite_oriented_canonicalDobrushinInfluence_diagonal L target
  · have hNotNeighbor : source ∉ L.plaquetteNeighbors target := by
      intro hNeighbor
      apply hInactive
      apply
        (finite_oriented_mem_activePlaquetteNeighbors_iff
          L target source).mpr
      exact
        ⟨(finite_oriented_mem_plaquetteNeighbors_iff
            L target source).mp hNeighbor,
          Ne.symm hDiagonal⟩
    exact
      finite_oriented_canonicalDobrushinInfluence_eq_zero_of_not_plaquetteNeighbor
        L target source hNotNeighbor

end

end MathlibAnalytic
end MGAP4D
