import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSharedPlaquetteEnergyEstimate

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A shared-plaquette multiplicity bound and a uniform energy bound give the
oriented local-action oscillation scale `2 * sharedBound * energyBound`. -/
theorem finite_oriented_activeLocalActionDifferenceOscillationBound_of_shared_card_le
    (L : FiniteOrientedLatticeWilsonSystem)
    (energyBound : ℝ)
    (hEnergy : L.UniformPlaquetteEnergyUpperBound energyBound)
    (sharedBound : ℕ)
    (hShared : ∀ target source : L.Edge,
      source ∈ L.activePlaquetteNeighbors target →
        (L.sharedPlaquettes target source).card ≤ sharedBound) :
    L.ActiveLocalActionDifferenceOscillationBound
      (2 * (sharedBound : ℝ) * energyBound) := by
  intro target source A g hActive u v
  have hEnergyNonneg :=
    finite_oriented_uniformPlaquetteEnergyUpperBound_nonneg
      L energyBound hEnergy
  have hCardNat := hShared target source hActive
  have hCard :
      ((L.sharedPlaquettes target source).card : ℝ) ≤
        (sharedBound : ℝ) := by
    exact_mod_cast hCardNat
  have hScale :
      ((L.sharedPlaquettes target source).card : ℝ) * energyBound ≤
        (sharedBound : ℝ) * energyBound :=
    mul_le_mul_of_nonneg_right hCard hEnergyNonneg
  have huRaw :=
    finite_oriented_targetLocalAction_sub_sourceReplace_abs_le_sharedCard_mul
      L energyBound hEnergy A target source u g
  have hvRaw :=
    finite_oriented_targetLocalAction_sub_sourceReplace_abs_le_sharedCard_mul
      L energyBound hEnergy A target source v g
  have hu := le_trans huRaw hScale
  have hv := le_trans hvRaw hScale
  have huBounds := abs_le.mp hu
  have hvBounds := abs_le.mp hv
  linarith

end

end MathlibAnalytic
end MGAP4D
