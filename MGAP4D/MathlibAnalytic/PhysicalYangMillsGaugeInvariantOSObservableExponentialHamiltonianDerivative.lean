import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCarrierHamiltonianGeneratorDomain
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExponentialGapSlope
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

namespace PositiveTimeObservableContractionSemigroup

variable {P : D.OSPreHilbertData}

/-- If a represented positive-time observable is an exact exponential
Euclidean-time eigenstate, then its represented OS carrier Hamiltonian difference
quotient is the scalar exponential slope times the initial represented state. -/
theorem physicalState_observableCarrierRightHamiltonianDifferenceQuotient_eq_exponentialSlope_smul
    (T : P.PositiveTimeObservableContractionSemigroup)
    (mass : ℝ)
    (F : D.positiveTimeSubalgebra)
    (hEigenaction : ∀ t : NNReal,
      P.physicalState (P.carrierOfPositiveTime (T.translate t F)) =
        Real.exp (-mass * (t : ℝ)) •
          P.physicalState (P.carrierOfPositiveTime F))
    (t : NNReal) :
    P.physicalState
        (T.observableCarrierRightHamiltonianDifferenceQuotient F t) =
      ((t : ℝ)⁻¹ * (1 - Real.exp (-mass * (t : ℝ)))) •
        P.physicalState (P.carrierOfPositiveTime F) := by
  rw [T.observableCarrierRightHamiltonianDifferenceQuotient_eq]
  rw [← P.physicalStateLinearMap_apply, map_smul, map_sub,
    P.physicalStateLinearMap_apply, P.physicalStateLinearMap_apply]
  rw [hEigenaction t]
  module

/-- Exact exponential observable eigenaction automatically supplies the OS
carrier Hamiltonian derivative required for passage through the null quotient
and Hilbert completion. -/
theorem observableCarrierRightHamiltonianDifferenceQuotient_tendsto_of_exponentialEigenaction
    (T : P.PositiveTimeObservableContractionSemigroup)
    (mass : ℝ)
    (F : D.positiveTimeSubalgebra)
    (hEigenaction : ∀ t : NNReal,
      P.physicalState (P.carrierOfPositiveTime (T.translate t F)) =
        Real.exp (-mass * (t : ℝ)) •
          P.physicalState (P.carrierOfPositiveTime F)) :
    Tendsto
      (T.observableCarrierRightHamiltonianDifferenceQuotient F)
      (nhdsWithin 0 (Ioi 0))
      (nhds (mass • P.carrierOfPositiveTime F)) := by
  rw [P.physicalState_isometry.tendsto_nhds_iff]
  have hscalar := tendsto_nnreal_inv_mul_one_sub_exp_neg_mul mass
  have hstate :
      Tendsto
        (fun _ : NNReal => P.physicalState (P.carrierOfPositiveTime F))
        (nhdsWithin 0 (Ioi 0))
        (nhds (P.physicalState (P.carrierOfPositiveTime F))) :=
    tendsto_const_nhds
  have hsmul := hscalar.smul hstate
  have hlimit :
      P.physicalState (mass • P.carrierOfPositiveTime F) =
        mass • P.physicalState (P.carrierOfPositiveTime F) := by
    rw [← P.physicalStateLinearMap_apply, map_smul,
      P.physicalStateLinearMap_apply]
  rw [hlimit]
  apply hsmul.congr'
  exact Filter.Eventually.of_forall fun t => by
    change
      P.physicalState
          (T.observableCarrierRightHamiltonianDifferenceQuotient F t) =
        ((t : ℝ)⁻¹ * (1 - Real.exp (-mass * (t : ℝ)))) •
          P.physicalState (P.carrierOfPositiveTime F)
    exact
      T.physicalState_observableCarrierRightHamiltonianDifferenceQuotient_eq_exponentialSlope_smul
        mass F hEigenaction t

/-- Bundle an exponentially translating observable in the canonical continuum
right-Hamiltonian domain.  No independent carrier derivative is supplied. -/
noncomputable def rightHamiltonianDomainPointOfObservableExponentialEigenaction
    (T : P.PositiveTimeObservableContractionSemigroup)
    (hT : T.StrongContinuityOnObservableStates)
    (mass : ℝ)
    (F : D.positiveTimeSubalgebra)
    (hEigenaction : ∀ t : NNReal,
      P.physicalState (P.carrierOfPositiveTime (T.translate t F)) =
        Real.exp (-mass * (t : ℝ)) •
          P.physicalState (P.carrierOfPositiveTime F)) :
    (T.carrierStronglyContinuousPhysicalSemigroup hT).rightGeneratorDomain :=
  T.rightHamiltonianDomainPointOfObservableDerivative hT F
    (mass • P.carrierOfPositiveTime F)
    (T.observableCarrierRightHamiltonianDifferenceQuotient_tendsto_of_exponentialEigenaction
      mass F hEigenaction)

@[simp] theorem coe_rightHamiltonianDomainPointOfObservableExponentialEigenaction
    (T : P.PositiveTimeObservableContractionSemigroup)
    (hT : T.StrongContinuityOnObservableStates)
    (mass : ℝ)
    (F : D.positiveTimeSubalgebra)
    (hEigenaction : ∀ t : NNReal,
      P.physicalState (P.carrierOfPositiveTime (T.translate t F)) =
        Real.exp (-mass * (t : ℝ)) •
          P.physicalState (P.carrierOfPositiveTime F)) :
    ((T.rightHamiltonianDomainPointOfObservableExponentialEigenaction
        hT mass F hEigenaction :
      (T.carrierStronglyContinuousPhysicalSemigroup hT).rightGeneratorDomain) :
      P.PhysicalHilbert) =
        P.physicalState (P.carrierOfPositiveTime F) :=
  rfl

/-- The continuum right Hamiltonian acts on an exact exponential observable
mode by its exponential mass. -/
theorem rightHamiltonian_rightHamiltonianDomainPointOfObservableExponentialEigenaction
    (T : P.PositiveTimeObservableContractionSemigroup)
    (hT : T.StrongContinuityOnObservableStates)
    (mass : ℝ)
    (F : D.positiveTimeSubalgebra)
    (hEigenaction : ∀ t : NNReal,
      P.physicalState (P.carrierOfPositiveTime (T.translate t F)) =
        Real.exp (-mass * (t : ℝ)) •
          P.physicalState (P.carrierOfPositiveTime F)) :
    (T.carrierStronglyContinuousPhysicalSemigroup hT).rightHamiltonian
        (T.rightHamiltonianDomainPointOfObservableExponentialEigenaction
          hT mass F hEigenaction) =
      mass • P.physicalState (P.carrierOfPositiveTime F) := by
  calc
    (T.carrierStronglyContinuousPhysicalSemigroup hT).rightHamiltonian
        (T.rightHamiltonianDomainPointOfObservableExponentialEigenaction
          hT mass F hEigenaction) =
      P.physicalState (mass • P.carrierOfPositiveTime F) := by
        exact
          T.rightHamiltonian_rightHamiltonianDomainPointOfObservableDerivative
            hT F (mass • P.carrierOfPositiveTime F)
            (T.observableCarrierRightHamiltonianDifferenceQuotient_tendsto_of_exponentialEigenaction
              mass F hEigenaction)
    _ = mass • P.physicalState (P.carrierOfPositiveTime F) := by
      rw [← P.physicalStateLinearMap_apply, map_smul,
        P.physicalStateLinearMap_apply]

end PositiveTimeObservableContractionSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
