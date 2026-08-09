import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCenteredCarrierVacuumOrthogonalDenseIsometry
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
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

/-- One-step actual Wilson translation on the centered carrier, followed by the
norm-preserving represented-state map into the completed finite excitation
Hilbert space. -/
noncomputable def centeredDensePhysicalOneStepLinearMap
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    Pn.CenteredCarrier →ₗ[ℝ] Pn.VacuumOrthogonalHilbert := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  exact
    (Pn.centeredPhysicalStateLinearMap hPn).comp
      (A.centeredOneStepLinearMap n)

@[simp] theorem centeredDensePhysicalOneStepLinearMap_apply_coe
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    ((A.centeredDensePhysicalOneStepLinearMap n F : Pn.VacuumOrthogonalHilbert) :
      Pn.PhysicalHilbert) =
      Pn.physicalState
        (R.realizableCarrierTranslation hInvariant n 1 (F : Pn.Carrier)) := by
  rfl

/-- The dense physical one-step map has exactly the intrinsic centered operator
norm bound from #1511, measured against the isometric dense core map of #1515. -/
theorem centeredDensePhysicalOneStepLinearMap_norm_le
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
    ‖A.centeredDensePhysicalOneStepLinearMap n F‖ ≤
      A.centeredTransferFactor n *
        ‖Pn.centeredPhysicalStateLinearMap hPn F‖ := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  change
    ‖Pn.centeredPhysicalStateLinearMap hPn (A.centeredOneStepLinearMap n F)‖ ≤
      A.centeredTransferFactor n *
        ‖Pn.centeredPhysicalStateLinearMap hPn F‖
  rw [Pn.norm_centeredPhysicalStateLinearMap,
    Pn.norm_centeredPhysicalStateLinearMap]
  simpa only [centeredOneStepOperator] using
    (A.centeredOneStepOperator n).le_opNorm F

/-- The unique bounded completion of the actual centered one-step Wilson
translation to the finite physical excitation Hilbert space `Ωₙ⊥`. -/
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
    (A.centeredDensePhysicalOneStepLinearMap n).extendOfNorm
      (Pn.centeredPhysicalStateLinearMap hPn)

/-- The completed excitation operator agrees exactly with one-step Wilson
translation on every centered represented state. -/
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
        (A.centeredOneStepLinearMap n F) := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  exact LinearMap.extendOfNorm_eq
    (Pn.centeredPhysicalStateLinearMap_denseRange hPn)
    ⟨A.centeredTransferFactor n, A.centeredDensePhysicalOneStepLinearMap_norm_le n⟩ F

/-- The completed excitation operator retains the centered one-step norm bound
on every vector of `Ωₙ⊥`. -/
theorem physicalExcitationOneStepOperator_norm_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert) :
    ‖A.physicalExcitationOneStepOperator n psi‖ ≤
      A.centeredTransferFactor n * ‖psi‖ := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have h := LinearMap.norm_extendOfNorm_apply_le
    (f := A.centeredDensePhysicalOneStepLinearMap n)
    (e := Pn.centeredPhysicalStateLinearMap hPn)
    (Pn.centeredPhysicalStateLinearMap_denseRange hPn)
    (A.centeredTransferFactor n)
    (A.centeredDensePhysicalOneStepLinearMap_norm_le n)
    psi
  simpa only [physicalExcitationOneStepOperator] using h

/-- One operator-norm inequality follows immediately from the completed bound. -/
theorem physicalExcitationOneStepOperator_opNorm_le_centeredTransferFactor
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    ‖A.physicalExcitationOneStepOperator n‖ ≤ A.centeredTransferFactor n := by
  apply ContinuousLinearMap.opNorm_le_bound
    (A.physicalExcitationOneStepOperator n) (A.centeredTransferFactor_nonneg n)
  intro psi
  exact A.physicalExcitationOneStepOperator_norm_le n psi

/-- Density plus exact norm preservation gives the reverse operator-norm
inequality: completion cannot shrink the intrinsic centered norm. -/
theorem centeredTransferFactor_le_physicalExcitationOneStepOperator_opNorm
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.centeredTransferFactor n ≤ ‖A.physicalExcitationOneStepOperator n‖ := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  change ‖A.centeredOneStepOperator n‖ ≤ ‖A.physicalExcitationOneStepOperator n‖
  apply ContinuousLinearMap.opNorm_le_bound
    (A.centeredOneStepOperator n)
    (norm_nonneg (A.physicalExcitationOneStepOperator n))
  intro F
  have h := (A.physicalExcitationOneStepOperator n).le_opNorm
    (Pn.centeredPhysicalStateLinearMap hPn F)
  rw [A.physicalExcitationOneStepOperator_on_centeredPhysicalState n F] at h
  rw [Pn.norm_centeredPhysicalStateLinearMap,
    Pn.norm_centeredPhysicalStateLinearMap] at h
  simpa only [centeredOneStepOperator] using h

/-- The finite rate `rₙ` of #1511 is literally the operator norm of the actual
completed one-step Wilson transfer on the physical excitation Hilbert space. -/
@[simp] theorem physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    ‖A.physicalExcitationOneStepOperator n‖ = A.centeredTransferFactor n :=
  le_antisymm
    (A.physicalExcitationOneStepOperator_opNorm_le_centeredTransferFactor n)
    (A.centeredTransferFactor_le_physicalExcitationOneStepOperator_opNorm n)

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

/-- The derived finite mass rate can now be read directly from the actual
completed excitation-sector one-step operator norm. -/
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