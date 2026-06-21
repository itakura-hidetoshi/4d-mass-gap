import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalExpRatioTV

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A target-local action-difference oscillation bound `omega` gives the exact
conditional likelihood-ratio radius `beta * omega` after normalization. -/
theorem finite_oriented_activeConditionalExpRatioBound_of_localActionOscillation
    (L : FiniteOrientedLatticeWilsonSystem)
    (omega : ℝ)
    (_hOmega : 0 ≤ omega)
    (hOsc : L.ActiveLocalActionDifferenceOscillationBound omega) :
    L.ActiveConditionalExpRatioBound (L.beta * omega) := by
  intro target source A g hActive u
  let logA : L.Gauge → ℝ :=
    L.targetLocalSingleLinkLogWeight A target
  let logB : L.Gauge → ℝ :=
    L.targetLocalSingleLinkLogWeight (L.replaceLink A source g) target
  have hLogOsc : ∀ x y : L.Gauge,
      (logA x - logB x) - (logA y - logB y) ≤ L.beta * omega := by
    intro x y
    have hAction := hOsc target source A g hActive y x
    have hMul := mul_le_mul_of_nonneg_left hAction L.beta_nonneg
    dsimp [logA, logB,
      FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkLogWeight]
    nlinarith
  have hRatio :=
    finiteNormalizedExp_mutual_le_exp_mul_of_difference_oscillation_all
      logA logB (L.beta * omega) hLogOsc u
  rw [finite_oriented_singleLinkConditionalPMF_toReal_eq_finiteNormalizedExp,
    finite_oriented_singleLinkConditionalPMF_toReal_eq_finiteNormalizedExp]
  exact hRatio

end

end MathlibAnalytic
end MGAP4D
