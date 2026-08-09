import MGAP4D.MathlibAnalytic.DenseIsometricCoreOperatorIterates
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableCenteredPhysicalExcitationOperator
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

noncomputable section

open Filter Function Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance realizablePhysicalExcitationFloorSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizablePhysicalExcitationFloorSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizablePhysicalExcitationFloorSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizablePhysicalExcitationFloorSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizablePhysicalExcitationFloorSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizablePhysicalExcitationFloorSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

set_option maxHeartbeats 800000

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

/-- Iterating the centered one-step operator is exactly the actual realizable
integer-time Wilson translation on the centered carrier. -/
@[simp] theorem centeredOneStepOperator_iterate_apply_coe
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    (((fun G : Pn.CenteredCarrier => A.centeredOneStepOperator n G)^[k] F :
        Pn.CenteredCarrier) : Pn.Carrier) =
      R.realizableCarrierTranslation hInvariant n k (F : Pn.Carrier) := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  induction k with
  | zero =>
      simpa only [Function.iterate_zero_apply] using
        (R.realizableCarrierTranslation_zero hInvariant n (F : Pn.Carrier)).symm
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      rw [A.centeredOneStepOperator_apply_coe n]
      rw [ih]
      simpa only [Nat.add_one] using
        (R.realizableCarrierTranslation_add hInvariant n k 1
          (F : Pn.Carrier)).symm

/-- On every represented centered state, arbitrary iterates of the completed
physical excitation operator agree with the represented iterates of the
centered core operator. -/
theorem physicalExcitationOneStepOperator_iterate_on_centeredPhysicalState
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let hPn : Pn.IsNormalized :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    (fun psi : Pn.VacuumOrthogonalHilbert =>
        A.physicalExcitationOneStepOperator n psi)^[k]
          (Pn.centeredPhysicalStateLinearMap hPn F) =
      Pn.centeredPhysicalStateLinearMap hPn
        ((fun G : Pn.CenteredCarrier => A.centeredOneStepOperator n G)^[k] F) := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  change
    (fun psi : Pn.VacuumOrthogonalHilbert =>
      DenseIsometricCoreOperatorCompletion.completedOperator
        (Pn.centeredPhysicalStateLinearMap hPn)
        (A.centeredOneStepOperator n) psi)^[k]
          (Pn.centeredPhysicalStateLinearMap hPn F) =
      Pn.centeredPhysicalStateLinearMap hPn
        ((fun G : Pn.CenteredCarrier => A.centeredOneStepOperator n G)^[k] F)
  exact
    DenseIsometricCoreOperatorCompletion.completedOperator_iterate_on_core
      (Pn.centeredPhysicalStateLinearMap hPn)
      (Pn.centeredPhysicalStateLinearMap_denseRange hPn)
      (Pn.norm_centeredPhysicalStateLinearMap hPn)
      (A.centeredOneStepOperator n) k F

/-- Hence arbitrary iterates of the completed finite excitation operator are
literally the actual `k`-step Wilson translation after embedding into the
finite completed OS Hilbert space. -/
theorem physicalExcitationOneStepOperator_iterate_on_centeredPhysicalState_coe
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).CenteredCarrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let hPn : Pn.IsNormalized :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    (((fun psi : Pn.VacuumOrthogonalHilbert =>
        A.physicalExcitationOneStepOperator n psi)^[k]
          (Pn.centeredPhysicalStateLinearMap hPn F) : Pn.VacuumOrthogonalHilbert) :
      Pn.PhysicalHilbert) =
      Pn.physicalState
        (R.realizableCarrierTranslation hInvariant n k (F : Pn.Carrier)) := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  rw [A.physicalExcitationOneStepOperator_iterate_on_centeredPhysicalState n k F]
  change
    Pn.physicalState
        ((((fun G : Pn.CenteredCarrier => A.centeredOneStepOperator n G)^[k] F :
          Pn.CenteredCarrier) : Pn.Carrier)) =
      Pn.physicalState
        (R.realizableCarrierTranslation hInvariant n k (F : Pn.Carrier))
  rw [A.centeredOneStepOperator_iterate_apply_coe n k F]

/-- The completed physical excitation one-step operator obeys its intrinsic
centered operator-norm bound on every completed excitation state. -/
theorem physicalExcitationOneStepOperator_norm_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert) :
    ‖A.physicalExcitationOneStepOperator n psi‖ ≤
      A.centeredTransferFactor n * ‖psi‖ := by
  have h := (A.physicalExcitationOneStepOperator n).le_opNorm psi
  rw [A.physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor] at h
  exact h

/-- Every `k`-step iterate on the completed finite excitation Hilbert space is
bounded by the `k`-th power of the intrinsic centered one-step norm. -/
theorem physicalExcitationOneStepOperator_iterate_norm_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n k : ℕ)
    (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert) :
    ‖(fun phi :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert =>
        A.physicalExcitationOneStepOperator n phi)^[k] psi‖ ≤
      (A.centeredTransferFactor n) ^ k * ‖psi‖ := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc
        ‖A.physicalExcitationOneStepOperator n
            ((fun phi :
              (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert =>
              A.physicalExcitationOneStepOperator n phi)^[k] psi)‖ ≤
            A.centeredTransferFactor n *
              ‖(fun phi :
                (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                  S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert =>
                A.physicalExcitationOneStepOperator n phi)^[k] psi‖ :=
          A.physicalExcitationOneStepOperator_norm_le n _
        _ ≤ A.centeredTransferFactor n *
            ((A.centeredTransferFactor n) ^ k * ‖psi‖) :=
          mul_le_mul_of_nonneg_left ih (A.centeredTransferFactor_nonneg n)
        _ = (A.centeredTransferFactor n) ^ (Nat.succ k) * ‖psi‖ := by
          rw [pow_succ]
          ring

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate

set_option maxHeartbeats 800000

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

/-- At floor-selected physical time, the actual completed finite excitation
trajectory is bounded by the corresponding power of the intrinsic centered
one-step factor. -/
theorem floorPhysicalExcitationIterate_norm_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (t : NNReal)
    (n : ℕ)
    (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert) :
    ‖(fun phi :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert =>
        A.boundedAnalysis.physicalExcitationOneStepOperator n phi)^[
          physicalTemporalFloorNatStep S.latticeSpacing t n] psi‖ ≤
      (A.boundedAnalysis.centeredTransferFactor n) ^
          physicalTemporalFloorNatStep S.latticeSpacing t n * ‖psi‖ :=
  A.boundedAnalysis.physicalExcitationOneStepOperator_iterate_norm_le
    n (physicalTemporalFloorNatStep S.latticeSpacing t n) psi

/-- The same floor-time estimate written entirely with the operator norm of the
actual completed finite physical excitation operator. -/
theorem floorPhysicalExcitationIterate_norm_le_opNorm
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (t : NNReal)
    (n : ℕ)
    (psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert) :
    ‖(fun phi :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert =>
        A.boundedAnalysis.physicalExcitationOneStepOperator n phi)^[
          physicalTemporalFloorNatStep S.latticeSpacing t n] psi‖ ≤
      ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ ^
          physicalTemporalFloorNatStep S.latticeSpacing t n * ‖psi‖ := by
  rw [A.boundedAnalysis.physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor]
  exact A.floorPhysicalExcitationIterate_norm_le t n psi

/-- Floor-selected powers of the actual completed physical excitation operator
norm converge to the continuum exponential with the mass derived from those
same finite operator norms. -/
theorem floorPhysicalExcitationOpNormPow_tendsto
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (t : NNReal) :
    Tendsto
      (fun n =>
        ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ ^
          physicalTemporalFloorNatStep S.latticeSpacing t n)
      atTop
      (nhds (Real.exp (-A.mass * (t : ℝ)))) := by
  simpa only [A.boundedAnalysis.physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor] using
    A.floorPow_tendsto t

/-- Scalar limit-transfer lemma for the physical excitation trajectory.  If a
varying sequence of finite excitation states has a limiting norm and the norms
of their floor-evolved states converge, the limiting evolved norm is bounded by
the derived continuum exponential times the limiting input norm. -/
theorem floorPhysicalExcitationIterate_limit_norm_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (t : NNReal)
    (psi : (n : ℕ) →
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert)
    {inputNormLimit evolvedNormLimit : ℝ}
    (hInput : Tendsto (fun n => ‖psi n‖) atTop (nhds inputNormLimit))
    (hEvolved :
      Tendsto
        (fun n =>
          ‖(fun phi :
              (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert =>
              A.boundedAnalysis.physicalExcitationOneStepOperator n phi)^[
                physicalTemporalFloorNatStep S.latticeSpacing t n] (psi n)‖)
        atTop (nhds evolvedNormLimit)) :
    evolvedNormLimit ≤
      Real.exp (-A.mass * (t : ℝ)) * inputNormLimit := by
  apply le_of_tendsto_of_tendsto hEvolved
    ((A.floorPhysicalExcitationOpNormPow_tendsto t).mul hInput)
  exact Filter.Eventually.of_forall fun n =>
    A.floorPhysicalExcitationIterate_norm_le_opNorm t n (psi n)

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate

end MathlibAnalytic
end MGAP4D

end
