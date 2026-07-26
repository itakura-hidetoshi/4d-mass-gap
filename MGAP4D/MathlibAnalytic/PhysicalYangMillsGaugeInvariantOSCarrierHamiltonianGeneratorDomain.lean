import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositiveTimeObservableStrongContinuity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonian
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- The represented-state map from the OS seminormed carrier into its Hilbert
completion is an isometry.  In particular, carrier norm convergence descends
through the null quotient and completion without any separate compatibility
assumption. -/
theorem physicalState_isometry (P : D.OSPreHilbertData) :
    Isometry P.physicalState := by
  intro F G
  rw [dist_eq_norm, dist_eq_norm]
  have hmap :
      P.physicalState (F - G) =
        P.physicalState F - P.physicalState G := by
    rw [← P.physicalStateLinearMap_apply, map_sub,
      P.physicalStateLinearMap_apply, P.physicalStateLinearMap_apply]
  rw [← hmap, P.norm_physicalState]

namespace PositiveTimeContractionSemigroup

variable {P : D.OSPreHilbertData}

/-- The right Hamiltonian difference quotient before the OS null quotient and
Hilbert completion.  Its sign matches `rightHamiltonianDifferenceQuotient` on
the completed physical semigroup. -/
def carrierRightHamiltonianDifferenceQuotient
    (T : P.PositiveTimeContractionSemigroup)
    (F : P.Carrier) (t : NNReal) : P.Carrier :=
  (t : ℝ)⁻¹ • (F - T.translate t F)

/-- The represented carrier Hamiltonian difference quotient is exactly the
completed physical Hamiltonian difference quotient. -/
theorem physicalState_carrierRightHamiltonianDifferenceQuotient
    (T : P.PositiveTimeContractionSemigroup)
    (hT : T.StrongContinuityOnDenseStates)
    (F : P.Carrier) (t : NNReal) :
    P.physicalState (T.carrierRightHamiltonianDifferenceQuotient F t) =
      (StrongContinuityOnDenseStates.toStronglyContinuousPhysicalSemigroup T hT)
        |>.rightHamiltonianDifferenceQuotient (P.physicalState F) t := by
  change
    P.physicalState ((t : ℝ)⁻¹ • (F - T.translate t F)) = _
  have hmap :
      P.physicalState ((t : ℝ)⁻¹ • (F - T.translate t F)) =
        (t : ℝ)⁻¹ •
          (P.physicalState F - P.physicalState (T.translate t F)) := by
    rw [← P.physicalStateLinearMap_apply, map_smul, map_sub,
      P.physicalStateLinearMap_apply, P.physicalStateLinearMap_apply]
  rw [hmap]
  unfold StronglyContinuousPhysicalSemigroup.rightHamiltonianDifferenceQuotient
  change
    (t : ℝ)⁻¹ •
        (P.physicalState F - P.physicalState (T.translate t F)) =
      (t : ℝ)⁻¹ •
        (P.physicalState F - T.physicalOperator t (P.physicalState F))
  rw [T.physicalOperator_on_physicalState]

/-- A carrier Hamiltonian derivative produces the corresponding completed
right-Hamiltonian value.  The quotient, null-space, and completion steps are
handled by the canonical represented-state isometry. -/
theorem hasRightHamiltonianValue_physicalState_of_carrierDifferenceQuotient_tendsto
    (T : P.PositiveTimeContractionSemigroup)
    (hT : T.StrongContinuityOnDenseStates)
    {F G : P.Carrier}
    (hDerivative :
      Tendsto (T.carrierRightHamiltonianDifferenceQuotient F)
        (nhdsWithin 0 (Ioi 0)) (nhds G)) :
    (StrongContinuityOnDenseStates.toStronglyContinuousPhysicalSemigroup T hT)
      |>.HasRightHamiltonianValue (P.physicalState F) (P.physicalState G) := by
  let Tphys :=
    StrongContinuityOnDenseStates.toStronglyContinuousPhysicalSemigroup T hT
  have hPhysical :
      Tendsto
        (fun t : NNReal =>
          P.physicalState (T.carrierRightHamiltonianDifferenceQuotient F t))
        (nhdsWithin 0 (Ioi 0))
        (nhds (P.physicalState G)) :=
    (P.physicalState_isometry.continuous.tendsto G).comp hDerivative
  have hHamiltonian :
      Tendsto
        (fun t : NNReal =>
          Tphys.rightHamiltonianDifferenceQuotient (P.physicalState F) t)
        (nhdsWithin 0 (Ioi 0))
        (nhds (P.physicalState G)) := by
    apply hPhysical.congr'
    exact Filter.Eventually.of_forall fun t =>
      (T.physicalState_carrierRightHamiltonianDifferenceQuotient hT F t).symm
  unfold StronglyContinuousPhysicalSemigroup.HasRightHamiltonianValue
  unfold StronglyContinuousPhysicalSemigroup.HasRightGeneratorValue
  have hneg := hHamiltonian.neg
  simpa only [
    StronglyContinuousPhysicalSemigroup.rightHamiltonianDifferenceQuotient_eq_neg,
    neg_neg] using hneg

/-- Bundle a carrier-differentiable represented state in the canonical
right-generator domain. -/
noncomputable def rightHamiltonianDomainPointOfCarrierDerivative
    (T : P.PositiveTimeContractionSemigroup)
    (hT : T.StrongContinuityOnDenseStates)
    (F G : P.Carrier)
    (hDerivative :
      Tendsto (T.carrierRightHamiltonianDifferenceQuotient F)
        (nhdsWithin 0 (Ioi 0)) (nhds G)) :
    (StrongContinuityOnDenseStates.toStronglyContinuousPhysicalSemigroup T hT)
      |>.rightGeneratorDomain :=
  ⟨P.physicalState F,
    ⟨-(P.physicalState G),
      T.hasRightHamiltonianValue_physicalState_of_carrierDifferenceQuotient_tendsto
        hT hDerivative⟩⟩

@[simp] theorem coe_rightHamiltonianDomainPointOfCarrierDerivative
    (T : P.PositiveTimeContractionSemigroup)
    (hT : T.StrongContinuityOnDenseStates)
    (F G : P.Carrier)
    (hDerivative :
      Tendsto (T.carrierRightHamiltonianDifferenceQuotient F)
        (nhdsWithin 0 (Ioi 0)) (nhds G)) :
    ((T.rightHamiltonianDomainPointOfCarrierDerivative hT F G hDerivative :
        (StrongContinuityOnDenseStates.toStronglyContinuousPhysicalSemigroup T hT)
          |>.rightGeneratorDomain) : P.PhysicalHilbert) =
      P.physicalState F :=
  rfl

/-- The canonical right Hamiltonian on the constructed domain point is the
represented carrier derivative. -/
theorem rightHamiltonian_rightHamiltonianDomainPointOfCarrierDerivative
    (T : P.PositiveTimeContractionSemigroup)
    (hT : T.StrongContinuityOnDenseStates)
    (F G : P.Carrier)
    (hDerivative :
      Tendsto (T.carrierRightHamiltonianDifferenceQuotient F)
        (nhdsWithin 0 (Ioi 0)) (nhds G)) :
    (StrongContinuityOnDenseStates.toStronglyContinuousPhysicalSemigroup T hT)
        |>.rightHamiltonian
          (T.rightHamiltonianDomainPointOfCarrierDerivative hT F G hDerivative) =
      P.physicalState G := by
  let Tphys :=
    StrongContinuityOnDenseStates.toStronglyContinuousPhysicalSemigroup T hT
  apply Tphys.hasRightHamiltonianValue_unique
    (Tphys.rightHamiltonian_hasRightHamiltonianValue
      (T.rightHamiltonianDomainPointOfCarrierDerivative hT F G hDerivative))
  exact
    T.hasRightHamiltonianValue_physicalState_of_carrierDifferenceQuotient_tendsto
      hT hDerivative

end PositiveTimeContractionSemigroup

namespace PositiveTimeObservableContractionSemigroup

variable {P : D.OSPreHilbertData}

/-- The canonical strongly continuous completion routed through the carrier
semigroup.  This is the form used by the observable derivative transport below. -/
noncomputable abbrev carrierStronglyContinuousPhysicalSemigroup
    (T : P.PositiveTimeObservableContractionSemigroup)
    (hT : T.StrongContinuityOnObservableStates) :
    P.StronglyContinuousPhysicalSemigroup :=
  PositiveTimeContractionSemigroup.StrongContinuityOnDenseStates
    |>.toStronglyContinuousPhysicalSemigroup
      T.toCarrierSemigroup hT.toCarrierStrongContinuity

/-- The carrier Hamiltonian difference quotient written directly in terms of an
actual positive-time observable translation. -/
def observableCarrierRightHamiltonianDifferenceQuotient
    (T : P.PositiveTimeObservableContractionSemigroup)
    (F : D.positiveTimeSubalgebra) (t : NNReal) : P.Carrier :=
  T.toCarrierSemigroup.carrierRightHamiltonianDifferenceQuotient
    (P.carrierOfPositiveTime F) t

/-- Unfold the observable carrier Hamiltonian quotient to the translated
positive-time observable representatives. -/
theorem observableCarrierRightHamiltonianDifferenceQuotient_eq
    (T : P.PositiveTimeObservableContractionSemigroup)
    (F : D.positiveTimeSubalgebra) (t : NNReal) :
    T.observableCarrierRightHamiltonianDifferenceQuotient F t =
      (t : ℝ)⁻¹ •
        (P.carrierOfPositiveTime F -
          P.carrierOfPositiveTime (T.translate t F)) := by
  change
    (t : ℝ)⁻¹ •
        (P.carrierOfPositiveTime F -
          T.carrierTranslation t (P.carrierOfPositiveTime F)) = _
  rw [T.carrierTranslation_carrierOfPositiveTime]

/-- An observable-side OS carrier derivative constructs a canonical continuum
right-Hamiltonian domain point after quotient and completion. -/
noncomputable def rightHamiltonianDomainPointOfObservableDerivative
    (T : P.PositiveTimeObservableContractionSemigroup)
    (hT : T.StrongContinuityOnObservableStates)
    (F : D.positiveTimeSubalgebra) (G : P.Carrier)
    (hDerivative :
      Tendsto (T.observableCarrierRightHamiltonianDifferenceQuotient F)
        (nhdsWithin 0 (Ioi 0)) (nhds G)) :
    (T.carrierStronglyContinuousPhysicalSemigroup hT).rightGeneratorDomain :=
  T.toCarrierSemigroup.rightHamiltonianDomainPointOfCarrierDerivative
    hT.toCarrierStrongContinuity (P.carrierOfPositiveTime F) G
    (by
      simpa [observableCarrierRightHamiltonianDifferenceQuotient] using
        hDerivative)

@[simp] theorem coe_rightHamiltonianDomainPointOfObservableDerivative
    (T : P.PositiveTimeObservableContractionSemigroup)
    (hT : T.StrongContinuityOnObservableStates)
    (F : D.positiveTimeSubalgebra) (G : P.Carrier)
    (hDerivative :
      Tendsto (T.observableCarrierRightHamiltonianDifferenceQuotient F)
        (nhdsWithin 0 (Ioi 0)) (nhds G)) :
    ((T.rightHamiltonianDomainPointOfObservableDerivative hT F G hDerivative :
        (T.carrierStronglyContinuousPhysicalSemigroup hT).rightGeneratorDomain) :
      P.PhysicalHilbert) =
        P.physicalState (P.carrierOfPositiveTime F) :=
  rfl

/-- The continuum right Hamiltonian of the observable-derived domain point is
the represented OS carrier derivative. -/
theorem rightHamiltonian_rightHamiltonianDomainPointOfObservableDerivative
    (T : P.PositiveTimeObservableContractionSemigroup)
    (hT : T.StrongContinuityOnObservableStates)
    (F : D.positiveTimeSubalgebra) (G : P.Carrier)
    (hDerivative :
      Tendsto (T.observableCarrierRightHamiltonianDifferenceQuotient F)
        (nhdsWithin 0 (Ioi 0)) (nhds G)) :
    (T.carrierStronglyContinuousPhysicalSemigroup hT).rightHamiltonian
        (T.rightHamiltonianDomainPointOfObservableDerivative hT F G hDerivative) =
      P.physicalState G := by
  exact
    T.toCarrierSemigroup
      |>.rightHamiltonian_rightHamiltonianDomainPointOfCarrierDerivative
        hT.toCarrierStrongContinuity (P.carrierOfPositiveTime F) G
        (by
          simpa [observableCarrierRightHamiltonianDifferenceQuotient] using
            hDerivative)

end PositiveTimeObservableContractionSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
