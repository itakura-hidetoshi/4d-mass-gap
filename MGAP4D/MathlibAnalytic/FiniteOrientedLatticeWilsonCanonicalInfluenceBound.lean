import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalDobrushinInfluence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Active oriented exponential-ratio control bounds the exact canonical
influence by the sharp total-variation majorant. -/
theorem finite_oriented_canonicalDobrushinInfluence_le_expRatioBound_of_active
    (L : FiniteOrientedLatticeWilsonSystem)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hRatio : L.ActiveConditionalExpRatioBound R)
    (target source : L.Edge)
    (hActive : source ∈ L.activePlaquetteNeighbors target) :
    L.canonicalDobrushinInfluence target source ≤
      (Real.exp R - 1) / (Real.exp R + 1) := by
  classical
  have hSourceNeTarget : source ≠ target :=
    ((finite_oriented_mem_activePlaquetteNeighbors_iff
      L target source).1 hActive).2
  have hTargetNeSource : target ≠ source := Ne.symm hSourceNeTarget
  rw [FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluence,
    if_neg hTargetNeSource]
  apply Finset.max'_le
  intro value hValue
  unfold FiniteOrientedLatticeWilsonSystem.canonicalDobrushinInfluenceValues at hValue
  rcases Finset.mem_image.mp hValue with ⟨p, _hp, rfl⟩
  apply finite_oriented_singleLinkConditionalTotalVariation_le_of_mutual_exp_ratio
    L p.1 (L.replaceLink p.1 source p.2) target R hR
  · intro u
    exact (hRatio target source p.1 p.2 hActive u).1
  · intro u
    exact (hRatio target source p.1 p.2 hActive u).2

/-- A target-local action oscillation estimate directly bounds every active
exact oriented canonical influence. -/
theorem finite_oriented_canonicalDobrushinInfluence_le_of_localActionOscillation
    (L : FiniteOrientedLatticeWilsonSystem)
    (omega : ℝ)
    (hOmega : 0 ≤ omega)
    (hOsc : L.ActiveLocalActionDifferenceOscillationBound omega)
    (target source : L.Edge)
    (hActive : source ∈ L.activePlaquetteNeighbors target) :
    L.canonicalDobrushinInfluence target source ≤
      (Real.exp (L.beta * omega) - 1) /
        (Real.exp (L.beta * omega) + 1) := by
  exact finite_oriented_canonicalDobrushinInfluence_le_expRatioBound_of_active
    L (L.beta * omega) (mul_nonneg L.beta_nonneg hOmega)
      (finite_oriented_activeConditionalExpRatioBound_of_localActionOscillation
        L omega hOmega hOsc)
      target source hActive

end

end MathlibAnalytic
end MGAP4D
