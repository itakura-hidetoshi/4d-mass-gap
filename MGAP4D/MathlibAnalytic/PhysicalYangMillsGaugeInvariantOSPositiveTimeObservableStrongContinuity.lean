import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositiveTimeObservableSemigroup
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSStrongContinuity

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

namespace PositiveTimeObservableContractionSemigroup

variable {P : D.OSPreHilbertData}

/-- Minimal continuity input stated directly on the actual positive-time
observable algebra.  It is required only after representing translated
observables in the physical Hilbert space. -/
structure StrongContinuityOnObservableStates
    (T : P.PositiveTimeObservableContractionSemigroup) : Prop where
  continuousAt_zero_on_physicalState :
    ∀ F : D.positiveTimeSubalgebra,
      ContinuousAt
        (fun t : NNReal =>
          P.physicalState
            (P.carrierOfPositiveTime (T.translate t F))) 0

namespace StrongContinuityOnObservableStates

/-- Observable-algebra continuity supplies the dense-state continuity input for
the carrier-side contraction semigroup. -/
def toCarrierStrongContinuity
    {T : P.PositiveTimeObservableContractionSemigroup}
    (hT : T.StrongContinuityOnObservableStates) :
    T.toCarrierSemigroup.StrongContinuityOnDenseStates where
  continuousAt_zero_on_physicalState := by
    intro F
    change ContinuousAt
      (fun t : NNReal =>
        P.physicalState
          (P.carrierOfPositiveTime
            (T.translate t (P.positiveTimeElement F)))) 0
    exact hT.continuousAt_zero_on_physicalState
      (P.positiveTimeElement F)

/-- Strong continuity at time zero for every completed physical vector follows
from continuity on represented positive-time observables, contractivity, and
density. -/
theorem physicalOperator_continuousAt_zero
    {T : P.PositiveTimeObservableContractionSemigroup}
    (hT : T.StrongContinuityOnObservableStates)
    (psi : P.PhysicalHilbert) :
    ContinuousAt
      (fun t : NNReal => T.toPhysicalSemigroup.operator t psi) 0 := by
  change ContinuousAt
    (fun t : NNReal => T.toCarrierSemigroup.physicalOperator t psi) 0
  exact hT.toCarrierStrongContinuity.physicalOperator_continuousAt_zero psi

/-- Canonical strongly continuous physical contraction semigroup generated from
positive-time observable-algebra translations and continuity on represented
observable states. -/
noncomputable def toStronglyContinuousPhysicalSemigroup
    (T : P.PositiveTimeObservableContractionSemigroup)
    (hT : T.StrongContinuityOnObservableStates) :
    P.StronglyContinuousPhysicalSemigroup :=
  T.toCarrierSemigroup.toStronglyContinuousPhysicalSemigroup
    hT.toCarrierStrongContinuity

/-- The strongly continuous completion retains the observable-side physical
semigroup as its underlying contraction semigroup. -/
@[simp] theorem toStronglyContinuousPhysicalSemigroup_toPhysicalSemigroup
    (T : P.PositiveTimeObservableContractionSemigroup)
    (hT : T.StrongContinuityOnObservableStates) :
    (T.toStronglyContinuousPhysicalSemigroup hT).toPhysicalSemigroup =
      T.toPhysicalSemigroup :=
  rfl

end StrongContinuityOnObservableStates

end PositiveTimeObservableContractionSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
