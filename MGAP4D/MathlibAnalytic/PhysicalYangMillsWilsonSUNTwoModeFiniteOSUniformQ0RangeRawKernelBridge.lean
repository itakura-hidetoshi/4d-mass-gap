import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNTwoModeFiniteOSUniformQ0Bridge
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2CompletedBoundaryTransferPhysicalModeRawKernel
import Mathlib.Tactic

/-!
# Canonical range/raw-kernel generation of the SU(N) two-mode q0 compatibility

The finite q0 bridge of #5005 packages two logically distinct model-facing
facts:

1. the concrete centered finite OS boundary vector lies in the range of the
   one-sided physical top-orthogonal boundary isometry;
2. the selected physical excitation satisfies the literal one-slab Wilson
   raw-kernel matrix-coefficient identity.

This file removes the arbitrary excitation choice and the abstract
`pairWeakAtFor` field from the input side.

A range proof canonically chooses the represented top-orthogonal excitation.
The generic raw-kernel equivalence then generates the selected weak pair
intertwining. Consequently the full
`PhysicalYangMillsSUNTwoModeUniformQ0Compatibility` record is theorem-generated
from exactly the two concrete H1-D residual statements above.

No equality between the finite OS vacuum line and the full normalized-transfer
top eigenspace is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance sunTwoModeRangeRawKernelTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sunTwoModeRangeRawKernelCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sunTwoModeRangeRawKernelSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sunTwoModeRangeRawKernelMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sunTwoModeRangeRawKernelBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

section SUNTwoModeRangeRawKernel

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N} {hN2 : 2 ≤ N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
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

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

/-- For a selected physical top-orthogonal excitation, the weak pair
compatibility used by #5005 is exactly the literal Wilson raw-kernel identity.

Thus `pairWeakAtFor` is not an independent model assumption once the raw
one-slab coefficient identity has been proved. -/
theorem oneSidedExcitationPairWeakAtFor_iff_rawKernel
    (n : ℕ)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)) :
    Q.OneSidedExcitationPairWeakAtFor hInvariant C n x ↔
      Q.CompletedBoundaryTransferOneSlabPhysicalTopRawKernelWeakAtFor
        hInvariant C n
        (x :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent n) N) := by
  simpa [OneSidedExcitationPairWeakAtFor] using
    (Q.completedBoundaryTransferOneSlabPairWeakAtFor_physicalTop_iff_rawKernel
      hInvariant C n
      (x :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (halfExtent n) N))

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

/-- Exact H1-D range statement for the concrete #5003 centered SU(N) states.

This says only that each actual centered boundary moment is represented by the
one-sided physical top-orthogonal boundary isometry. It does not choose an
excitation and does not identify the OS vacuum line with the full physical top
eigenspace. -/
def PhysicalYangMillsSUNTwoModeCenteredBoundaryOneSidedExcitationRange : Prop :=
  ∀ (k : Fin 2) (n : ℕ),
    Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (physicalYangMillsSUNTwoModeCenteredFiniteOSState P k n) ∈
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySector
        (halfExtent n) N hN (beta n) (hbeta n)

/-- Canonical top-orthogonal excitation chosen from the exact range statement.

The choice is proof-generated from range membership; there is no extra
excitation field on the input side. -/
noncomputable def physicalYangMillsSUNTwoModeCenteredBoundaryExcitation
    (hRange :
      PhysicalYangMillsSUNTwoModeCenteredBoundaryOneSidedExcitationRange
        (P := P))
    (k : Fin 2) (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      (halfExtent n) N hN (beta n) (hbeta n) :=
  Classical.choose (hRange k n)

/-- The canonical excitation recovers the concrete centered boundary moment
exactly. -/
theorem physicalYangMillsSUNTwoModeCenteredBoundaryExcitation_image
    (hRange :
      PhysicalYangMillsSUNTwoModeCenteredBoundaryOneSidedExcitationRange
        (P := P))
    (k : Fin 2) (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
        (halfExtent n) N hN (beta n) (hbeta n)
        (physicalYangMillsSUNTwoModeCenteredBoundaryExcitation hRange k n) =
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (physicalYangMillsSUNTwoModeCenteredFiniteOSState P k n) := by
  exact Classical.choose_spec (hRange k n)

/-- The #5005 compatibility record is theorem-generated from the two concrete
H1-D residual statements: centered boundary range membership and the literal
raw Wilson one-slab matrix-coefficient identity for the resulting canonical
excitation. -/
noncomputable def physicalYangMillsSUNTwoModeUniformQ0Compatibility_of_range_rawKernel
    (hRange :
      PhysicalYangMillsSUNTwoModeCenteredBoundaryOneSidedExcitationRange
        (P := P))
    (hRaw :
      ∀ (k : Fin 2) (n : ℕ),
        Q.CompletedBoundaryTransferOneSlabPhysicalTopRawKernelWeakAtFor
          hInvariant C n
          (physicalYangMillsSUNTwoModeCenteredBoundaryExcitation hRange k n :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N)) :
    PhysicalYangMillsSUNTwoModeUniformQ0Compatibility
      S D halfExtent N hN hN2 beta hbeta Q F R hInvariant P C where
  excitation :=
    physicalYangMillsSUNTwoModeCenteredBoundaryExcitation hRange
  pairWeakAtFor := by
    intro k n
    exact
      (Q.oneSidedExcitationPairWeakAtFor_iff_rawKernel
        (C := C) n
        (physicalYangMillsSUNTwoModeCenteredBoundaryExcitation hRange k n)).2
        (hRaw k n)
  centeredBoundaryMoment := by
    intro k n
    exact
      (physicalYangMillsSUNTwoModeCenteredBoundaryExcitation_image
        hRange k n).symm

/-- Direct q0 consequence with the old compatibility structure completely
eliminated from the theorem hypotheses. -/
theorem physicalYangMillsSUNTwoModeCenteredFiniteOSState_one_norm_le_uniform_q0_of_range_rawKernel
    (hRange :
      PhysicalYangMillsSUNTwoModeCenteredBoundaryOneSidedExcitationRange
        (P := P))
    (hRaw :
      ∀ (k : Fin 2) (n : ℕ),
        Q.CompletedBoundaryTransferOneSlabPhysicalTopRawKernelWeakAtFor
          hInvariant C n
          (physicalYangMillsSUNTwoModeCenteredBoundaryExcitation hRange k n :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N))
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
  let A :=
    physicalYangMillsSUNTwoModeUniformQ0Compatibility_of_range_rawKernel
      hRange hRaw
  exact
    PhysicalYangMillsSUNTwoModeUniformQ0Compatibility.centeredFiniteOSState_one_norm_le_uniform_q0
      A s hs hcut k n

end SUNTwoModeRangeRawKernel

end

end MathlibAnalytic
end MGAP4D
