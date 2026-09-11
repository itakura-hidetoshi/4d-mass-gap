import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSharedPlaquetteOscillation
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonActiveCoefficientBound
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalInfluenceBound

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Shared-plaquette geometry and a uniform energy bound give a closed scalar
upper bound for the exact oriented canonical coefficient. -/
theorem finite_oriented_canonicalDobrushinCoefficient_le_of_sharedPlaquetteEnergy
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (energyBound : ℝ)
    (hEnergy : L.UniformPlaquetteEnergyUpperBound energyBound)
    (sharedBound degreeBound : ℕ)
    (hShared : ∀ target source : L.Edge,
      source ∈ L.activePlaquetteNeighbors target →
        (L.sharedPlaquettes target source).card ≤ sharedBound)
    (hDegree : ∀ target : L.Edge,
      (L.activePlaquetteNeighbors target).card ≤ degreeBound) :
    L.canonicalDobrushinCoefficient hEdge ≤
      (degreeBound : ℝ) *
        ((Real.exp
            (L.beta * (2 * (sharedBound : ℝ) * energyBound)) - 1) /
          (Real.exp
            (L.beta * (2 * (sharedBound : ℝ) * energyBound)) + 1)) := by
  let omega : ℝ := 2 * (sharedBound : ℝ) * energyBound
  let eta : ℝ :=
    (Real.exp (L.beta * omega) - 1) /
      (Real.exp (L.beta * omega) + 1)
  have hEnergyNonneg :=
    finite_oriented_uniformPlaquetteEnergyUpperBound_nonneg
      L energyBound hEnergy
  have hOmega : 0 ≤ omega := by
    dsimp [omega]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      hEnergyNonneg
  have hR : 0 ≤ L.beta * omega :=
    mul_nonneg L.beta_nonneg hOmega
  have hEta : 0 ≤ eta := by
    dsimp [eta]
    exact div_nonneg
      (sub_nonneg.mpr (Real.one_le_exp hR))
      (by positivity)
  have hOsc :
      L.ActiveLocalActionDifferenceOscillationBound omega := by
    simpa [omega] using
      finite_oriented_activeLocalActionDifferenceOscillationBound_of_shared_card_le
        L energyBound hEnergy sharedBound hShared
  have hLocal : ∀ target source : L.Edge,
      source ∈ L.activePlaquetteNeighbors target →
        L.canonicalDobrushinInfluence target source ≤ eta := by
    intro target source hActive
    simpa [eta] using
      finite_oriented_canonicalDobrushinInfluence_le_of_localActionOscillation
        L omega hOmega hOsc target source hActive
  simpa [omega, eta] using
    finite_oriented_canonicalDobrushinCoefficient_le_activeCard_mul_eta
      L hEdge eta hEta hLocal degreeBound hDegree

/-- The shared-plaquette scalar upper bound proves strict oriented Dobrushin
contraction whenever that scalar is below one. -/
theorem finite_oriented_canonicalDobrushinCoefficient_lt_one_of_sharedPlaquetteEnergy
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (energyBound : ℝ)
    (hEnergy : L.UniformPlaquetteEnergyUpperBound energyBound)
    (sharedBound degreeBound : ℕ)
    (hShared : ∀ target source : L.Edge,
      source ∈ L.activePlaquetteNeighbors target →
        (L.sharedPlaquettes target source).card ≤ sharedBound)
    (hDegree : ∀ target : L.Edge,
      (L.activePlaquetteNeighbors target).card ≤ degreeBound)
    (hStrict :
      (degreeBound : ℝ) *
        ((Real.exp
            (L.beta * (2 * (sharedBound : ℝ) * energyBound)) - 1) /
          (Real.exp
            (L.beta * (2 * (sharedBound : ℝ) * energyBound)) + 1)) < 1) :
    L.canonicalDobrushinCoefficient hEdge < 1 :=
  lt_of_le_of_lt
    (finite_oriented_canonicalDobrushinCoefficient_le_of_sharedPlaquetteEnergy
      L hEdge energyBound hEnergy sharedBound degreeBound
      hShared hDegree)
    hStrict

end

end MathlibAnalytic
end MGAP4D
