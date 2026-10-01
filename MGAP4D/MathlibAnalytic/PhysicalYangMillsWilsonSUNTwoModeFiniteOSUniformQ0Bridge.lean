import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNPrimaryPlaquetteTwoModePointwiseCoherentReadout
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryScaleUniformDecay
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2CompletedBoundaryTransferOneSlabMatrixCoefficient
import Mathlib.Tactic

/-!
# Uniform q0 bridge from concrete SU(N) two-mode OS states to one-sided dynamics

PR #5003 reduces the arbitrary-rank continuum-excitation construction to two
pointwise coherent Wilson readout obligations.

PR #5004 transports the explicit #4983 contraction

  q0 = 3071 / 3072

to the concrete one-sided shared-boundary top-orthogonal sector.

This file isolates the exact H1-D compatibility needed to connect those two
lanes.  The completed OS boundary transfer must agree with the physical
one-slab pair transfer, and the centered finite OS state must have a boundary
moment in the one-sided top-orthogonal range.

Under precisely those conditions, the actual finite OS time-one operator on
the selected centered SU(N) state satisfies the same uniform q0 contraction.

No equality between the whole canonical OS vacuum-orthogonal sector and the
whole physical top-orthogonal sector is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Topology
open scoped InnerProductSpace

noncomputable section

@[reducible] local instance sunTwoModeQ0BridgePhysicalOrthogonalNormedSpace
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
  Submodule.normedSpace
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- Pair-coordinate one-slab intertwining, restricted to a genuine physical
top-orthogonal excitation and the normalized top companion, gives exact
intertwining on the one-sided shared-boundary excitation image. -/
theorem completedBoundaryTransfer_two_oneSidedExcitationBoundary_of_pairIntertwiningAt
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (hPair : CompletedBoundaryTransferOneSlabPairIntertwiningAt
      Q hInvariant C n)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)) :
    Q.completedBoundaryTransfer hInvariant C n 2
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
          (halfExtent n) N hN (beta n) (hbeta n) x) =
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
        (halfExtent n) N hN (beta n) (hbeta n)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n) x) := by
  let f :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) N :=
    (x :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) N)
  let omega :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) N :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      (halfExtent n) N hN (beta n) (hbeta n)
  have h :=
    Q.completedBoundaryTransfer_two_oneSidedBoundary_of_oneSlabPairIntertwiningAt
      hInvariant C n hPair f omega
  change
    Q.completedBoundaryTransfer hInvariant C n 2
        (periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
          (halfExtent n) N
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
            (halfExtent n) N hN (beta n) (hbeta n) x)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
            (halfExtent n) N hN (beta n) (hbeta n))) =
      periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
        (halfExtent n) N
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
          (halfExtent n) N hN (beta n) (hbeta n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n) x))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          (halfExtent n) N hN (beta n) (hbeta n))
  simpa [f, omega,
    periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp,
    periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp,
    periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator]
    using h

/-- If a finite OS state has a one-sided top-orthogonal boundary moment, then
the actual finite OS time-one operator inherits the explicit uniform q0 bound. -/
theorem finiteOperator_one_norm_le_uniform_q0_of_oneSidedExcitationBoundary
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ m : ℕ,
        beta m ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n : ℕ)
    (hPair : CompletedBoundaryTransferOneSlabPairIntertwiningAt
      Q hInvariant C n)
    (psi :
      PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n))
    (hBoundary :
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n psi =
        periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
          (halfExtent n) N hN (beta n) (hbeta n) x) :
    ‖C.finiteOperator n 1 psi‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor *
        ‖psi‖ := by
  let J := Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
  let U :=
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
      (halfExtent n) N hN (beta n) (hbeta n)
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      (halfExtent n) N hN (beta n) (hbeta n)
  have hTransfer :
      J (C.finiteOperator n 1 psi) = U (T x) := by
    calc
      J (C.finiteOperator n 1 psi) =
          Q.completedBoundaryTransfer hInvariant C n 2 (J psi) := by
        symm
        simpa [J] using
          Q.completedBoundaryTransfer_apply_physicalHilbertBoundaryMoment
            hInvariant C n (2 : NNReal) psi
      _ =
          Q.completedBoundaryTransfer hInvariant C n 2 (U x) := by
        rw [hBoundary]
      _ = U (T x) := by
        exact
          Q.completedBoundaryTransfer_two_oneSidedExcitationBoundary_of_pairIntertwiningAt
            hInvariant C n hPair x
  have hDecay :
      ‖T x‖ ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor *
          ‖x‖ := by
    simpa [T] using
      periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalTransferOperator_pow_apply_norm_le
        halfExtent N hN beta hbeta s hs hcut n 1 (by norm_num) x
  calc
    ‖C.finiteOperator n 1 psi‖ = ‖J (C.finiteOperator n 1 psi)‖ := by
      symm
      exact J.norm_map _
    _ = ‖U (T x)‖ := by rw [hTransfer]
    _ = ‖T x‖ := U.norm_map _
    _ ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor *
          ‖x‖ := hDecay
    _ =
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor *
          ‖U x‖ := by
      rw [U.norm_map]
    _ =
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor *
          ‖J psi‖ := by
      rw [hBoundary]
    _ =
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor *
          ‖psi‖ := by
      rw [J.norm_map]

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

/-- The centered actual finite OS state selected by the #5003 two-mode
pointwise coherent readout. -/
noncomputable def
    physicalYangMillsSUNTwoModeCenteredFiniteOSState
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    {hN2 : 2 ≤ N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    (P :
      PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
        S D halfExtent N hN hN2 beta hbeta Q F R hInvariant)
    (k : Fin 2) (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  finiteVacuumCentered Pn.vacuum
    (Pn.physicalState
      (Pn.positiveTimeSubmoduleCarrierLinearMap (P.observable k)))

/-- Exact remaining H1-D compatibility for the #5003 concrete SU(N) states:
each centered boundary moment is represented by a physical top-orthogonal
one-sided excitation, while the completed boundary transfer obeys the weak pair-Haar matrix-coefficient
one-slab intertwining. Existing Hilbert separation theorem-generates the strong
pair-coordinate identity. -/
structure PhysicalYangMillsSUNTwoModeUniformQ0Compatibility
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N) (hN2 : 2 ≤ N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (P :
      PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
        S D halfExtent N hN hN2 beta hbeta Q F R hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant) where
  pairWeakIntertwining :
    ∀ n,
      Q.CompletedBoundaryTransferOneSlabPairWeakIntertwiningAt hInvariant C n
  excitation :
    (k : Fin 2) → (n : ℕ) →
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)
  centeredBoundaryMoment :
    ∀ (k : Fin 2) (n : ℕ),
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (physicalYangMillsSUNTwoModeCenteredFiniteOSState P k n) =
        periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
          (halfExtent n) N hN (beta n) (hbeta n) (excitation k n)

namespace PhysicalYangMillsSUNTwoModeUniformQ0Compatibility

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    {hN2 : 2 ≤ N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {P :
      PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
        S D halfExtent N hN hN2 beta hbeta Q F R hInvariant}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant}

/-- The concrete #5003 centered SU(N) state inherits the explicit finite
time-one q0 contraction at every scale. -/
theorem centeredFiniteOSState_one_norm_le_uniform_q0
    (A :
      PhysicalYangMillsSUNTwoModeUniformQ0Compatibility
        S D halfExtent N hN hN2 beta hbeta Q F R hInvariant P C)
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (k : Fin 2) (n : ℕ) :
    ‖C.finiteOperator n 1
        (physicalYangMillsSUNTwoModeCenteredFiniteOSState P k n)‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor *
        ‖physicalYangMillsSUNTwoModeCenteredFiniteOSState P k n‖ := by
  exact
    Q.finiteOperator_one_norm_le_uniform_q0_of_oneSidedExcitationBoundary
      hInvariant C s hs hcut n
      (Q.completedBoundaryTransferOneSlabPairIntertwiningAt_of_weak
        hInvariant C n (A.pairWeakIntertwining n))
      (physicalYangMillsSUNTwoModeCenteredFiniteOSState P k n)
      (A.excitation k n)
      (A.centeredBoundaryMoment k n)

end PhysicalYangMillsSUNTwoModeUniformQ0Compatibility

end

end MathlibAnalytic
end MGAP4D
