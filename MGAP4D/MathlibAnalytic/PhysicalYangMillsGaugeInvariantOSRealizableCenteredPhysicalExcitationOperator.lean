import MGAP4D.MathlibAnalytic.DenseIsometricCoreOperatorCompletion
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCenteredCarrierVacuumOrthogonalDenseIsometry
import Mathlib.Tactic

noncomputable section

open Function
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableCenteredPhysicalExcitationSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableCenteredPhysicalExcitationSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableCenteredPhysicalExcitationSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableCenteredPhysicalExcitationSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableCenteredPhysicalExcitationSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableCenteredPhysicalExcitationSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- The completed finite physical excitation operator obtained from #1511's
actual centered one-step Wilson transfer through #1515's norm-preserving dense
representation of the centered carrier in `Ωₙ⊥`.

The completion is an instance of the generic dense-isometric-core construction;
no additional Yang--Mills dynamics or quantitative constant is introduced. -/
noncomputable def physicalExcitationOneStepOperator
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    Pn.VacuumOrthogonalHilbert →L[ℝ] Pn.VacuumOrthogonalHilbert := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  exact
    DenseIsometricCoreOperatorCompletion.completedOperator
      (Pn.centeredPhysicalStateLinearMap hPn)
      (A.centeredOneStepOperator n)

/-- The completed excitation operator agrees exactly with the actual one-step
Wilson translation on every represented centered carrier state. -/
theorem physicalExcitationOneStepOperator_on_centeredPhysicalState
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let hPn : Pn.IsNormalized :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    A.physicalExcitationOneStepOperator n
        (Pn.centeredPhysicalStateLinearMap hPn F) =
      Pn.centeredPhysicalStateLinearMap hPn
        (A.centeredOneStepOperator n F) := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  exact
    DenseIsometricCoreOperatorCompletion.completedOperator_on_core
      (Pn.centeredPhysicalStateLinearMap hPn)
      (Pn.centeredPhysicalStateLinearMap_denseRange hPn)
      (Pn.norm_centeredPhysicalStateLinearMap hPn)
      (A.centeredOneStepOperator n) F

/-- On represented centered states, the completed excitation operator is
literally one realizable Wilson carrier translation followed by the OS state
map. -/
theorem physicalExcitationOneStepOperator_on_centeredPhysicalState_coe
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let hPn : Pn.IsNormalized :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    ((A.physicalExcitationOneStepOperator n
        (Pn.centeredPhysicalStateLinearMap hPn F) : Pn.VacuumOrthogonalHilbert) :
      Pn.PhysicalHilbert) =
      Pn.physicalState
        (R.realizableCarrierTranslation hInvariant n 1 (F : Pn.Carrier)) := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  rw [A.physicalExcitationOneStepOperator_on_centeredPhysicalState n F]
  rfl

/-- The completed excitation operator has exactly the same operator norm as
#1511's intrinsic centered one-step operator.  Completion neither enlarges nor
shrinks the finite excitation rate. -/
@[simp] theorem physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    ‖A.physicalExcitationOneStepOperator n‖ = A.centeredTransferFactor n := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  change
    ‖DenseIsometricCoreOperatorCompletion.completedOperator
        (Pn.centeredPhysicalStateLinearMap hPn)
        (A.centeredOneStepOperator n)‖ =
      ‖A.centeredOneStepOperator n‖
  exact
    DenseIsometricCoreOperatorCompletion.completedOperator_opNorm_eq
      (Pn.centeredPhysicalStateLinearMap hPn)
      (Pn.centeredPhysicalStateLinearMap_denseRange hPn)
      (Pn.norm_centeredPhysicalStateLinearMap hPn)
      (A.centeredOneStepOperator n)

/-- Consequently the intrinsic finite mass rate can be read directly from the
actual completed finite physical excitation operator norm. -/
theorem centeredMassRate_eq_physicalExcitationOneStepOperator_opNorm
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    -Real.log (A.centeredTransferFactor n) / S.latticeSpacing n =
      -Real.log ‖A.physicalExcitationOneStepOperator n‖ / S.latticeSpacing n := by
  rw [A.physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor]

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- The derived finite mass rate is literally the logarithmic decay rate of the
actual completed one-step Wilson transfer on the finite physical excitation
Hilbert space. -/
@[simp] theorem massRate_eq_physicalExcitationOneStepOperator_opNorm
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.massRate n =
      -Real.log ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ /
        S.latticeSpacing n := by
  rw [A.boundedAnalysis.physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor]
  rfl

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate

end MathlibAnalytic
end MGAP4D

end