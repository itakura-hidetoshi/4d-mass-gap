import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealizableActualSynthesisRawPathGram
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCompletedBoundaryTransfer
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelBilinear
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMM — exact genuine Wilson/OS one-step finite defect

AMJ/AMK/AML certify the actual original SU2 Wilson Gibbs static plaquette
covariance L1, Schur L2, and Gram positivity. None identifies static Gibbs
covariance with physical Euclidean-time OS transfer.

Here the completed OS boundary time-two transfer (one physical time step)
and the genuinely realizable finite Wilson integer-one-step translation
are compared WITHOUT assuming that they are equal.

The first theorem is a sharp Hilbert-norm identity for the genuine
carrier-level discrepancy. The second expresses the scalar discrepancy
against arbitrary pair-Haar tests through the ACTUAL finite Wilson
boundary/open-half Hilbert-Schmidt Gram kernel and the difference of two
positive-half translated L2 pullbacks. The third gives the sharp
Hilbert-Schmidt continuity bound for this discrepancy.

The rectangular kernel has the literal normalized unfixed Wilson
finite path kernel as its a.e. representative (existing source theorem).
No common/realizable one-step coherence, postulated zero defect,
OS spectral gap, or 4D continuum mass gap is assumed or concluded.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37AMM_sideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩
local instance p4Q2PZ37AMM_topologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2PZ37AMM_compactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2PZ37AMM_secondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2PZ37AMM_measurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2PZ37AMM_borelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4Q2PZ37AMM_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37AMM_boundarySFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance
local instance p4Q2PZ37AMM_halfSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}

/-- Exact norm identity comparing the genuine completed OS semigroup
time-one boundary image with the actual realizable Wilson integer-one-step
physical carrier. It does NOT assume their coherence or equality.

Thus the boundary defect is not an artifact of completion or changing
Hilbert coordinates; it is precisely the mismatch of the two physical
time-one states, at the level of the same actual OS Hilbert carrier. -/
theorem completedBoundaryTransfer_two_realizableOneStep_defect_norm_eq
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    ‖Q.completedBoundaryTransfer hInvariant C n 2
        (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (Pn.physicalState F)) -
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (Pn.physicalState (R.realizableCarrierTranslation hInvariant n 1 F))‖ =
    ‖C.finiteOperator n 1 (Pn.physicalState F) -
      Pn.physicalState (R.realizableCarrierTranslation hInvariant n 1 F)‖ := by
  dsimp only
  have hhalf : (2 : NNReal) / 2 = 1 := by norm_num
  rw [Q.completedBoundaryTransfer_apply_physicalHilbertBoundaryMoment, hhalf]
  let J := Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
  change
    ‖J (C.finiteOperator n 1
      ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState F)) -
      J ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).physicalState
          (R.realizableCarrierTranslation hInvariant n 1 F))‖ = _
  rw [← map_sub]
  exact J.norm_map _

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

namespace PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}

/-- The exact, UNCONDITIONAL scalar discrepancy between completed common
OS time one and actual realizable Wilson integer time one is the genuine
rectangular Wilson Gram kernel pairing with the difference of the two
open-half L2 translations.

The right side is a finite Wilson kernel computation, not an imposed
one-step intertwining hypothesis. In particular, it keeps the obstruction
visible even if it is nonzero. -/
theorem canonicalRealizableOneStep_OS_rawPath_defect_eq_kernelPairing
    (R₀ : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback E)
    (hInvariant : ∀ n,
      R₀.reflectionData.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant n).Carrier)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N) :
    let Q := R₀.toCanonicalCoherentPositiveTimePullback
    let K := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
      (halfExtent n) N hN (beta n) (hbeta n)
    let fz := periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
      (halfExtent n) N z
    let uCommon := Q.translatedPositiveHalfL2LinearMap hInvariant C n 2 F
    let uRealizable := Q.positiveHalfL2LinearMap hInvariant n
      (R.realizableCarrierTranslation hInvariant n 1 F)
    inner ℝ
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          (halfExtent n) N
          (Q.completedBoundaryTransfer hInvariant C n 2
            (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
              S R₀.reflectionData halfExtent N hN beta hbeta
                Q.toWeakStarBridge hInvariant n F))) z -
      realL2HilbertSchmidtKernelPairing K fz uRealizable =
      realL2HilbertSchmidtKernelPairing K fz
        (uCommon - uRealizable) := by
  dsimp only
  let Q := R₀.toCanonicalCoherentPositiveTimePullback
  let K := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
      (halfExtent n) N hN (beta n) (hbeta n)
  let fz := periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
      (halfExtent n) N z
  let uCommon := Q.translatedPositiveHalfL2LinearMap hInvariant C n 2 F
  let uRealizable := Q.positiveHalfL2LinearMap hInvariant n
      (R.realizableCarrierTranslation hInvariant n 1 F)
  have hCommon :
      inner ℝ
          (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
            (halfExtent n) N
            (Q.completedBoundaryTransfer hInvariant C n 2
              (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
                S R₀.reflectionData halfExtent N hN beta hbeta
                  Q.toWeakStarBridge hInvariant n F))) z =
        realL2HilbertSchmidtKernelPairing K fz uCommon := by
    rw [Q.completedBoundaryTransfer_apply_canonicalBoundaryMoment_eq_actualSynthesis]
    simpa only [Q, K, fz, uCommon] using
      (periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesis_pair_inner
        (halfExtent n) N hN (beta n) (hbeta n) uCommon z)
  have hSub :
      realL2HilbertSchmidtKernelPairing K fz
        (uCommon - uRealizable) =
        realL2HilbertSchmidtKernelPairing K fz uCommon -
          realL2HilbertSchmidtKernelPairing K fz uRealizable := by
    simpa only [realL2HilbertSchmidtKernelBilinear_apply] using
      (realL2HilbertSchmidtKernelBilinear K fz).map_sub uCommon uRealizable
  calc
    inner ℝ
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          (halfExtent n) N
          (Q.completedBoundaryTransfer hInvariant C n 2
            (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
              S R₀.reflectionData halfExtent N hN beta hbeta
                Q.toWeakStarBridge hInvariant n F))) z -
      realL2HilbertSchmidtKernelPairing K fz uRealizable =
        realL2HilbertSchmidtKernelPairing K fz uCommon -
          realL2HilbertSchmidtKernelPairing K fz uRealizable := by rw [hCommon]
    _ = realL2HilbertSchmidtKernelPairing K fz
        (uCommon - uRealizable) := hSub.symm

/-- The true finite Wilson kernel controls the scalar one-step OS/realizable
obstruction by the open-half Hilbert norm of the translation discrepancy.
This is a quantitative estimate without a zero-defect assumption. -/
theorem canonicalRealizableOneStep_OS_rawPath_defect_abs_le
    (R₀ : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback E)
    (hInvariant : ∀ n,
      R₀.reflectionData.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant n).Carrier)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent n) N) :
    let Q := R₀.toCanonicalCoherentPositiveTimePullback
    let K := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
      (halfExtent n) N hN (beta n) (hbeta n)
    let fz := periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
      (halfExtent n) N z
    let uCommon := Q.translatedPositiveHalfL2LinearMap hInvariant C n 2 F
    let uRealizable := Q.positiveHalfL2LinearMap hInvariant n
      (R.realizableCarrierTranslation hInvariant n 1 F)
    |inner ℝ
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
          (halfExtent n) N
          (Q.completedBoundaryTransfer hInvariant C n 2
            (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
              S R₀.reflectionData halfExtent N hN beta hbeta
                Q.toWeakStarBridge hInvariant n F))) z -
      realL2HilbertSchmidtKernelPairing K fz uRealizable| ≤
      ‖K‖ * ‖z‖ * ‖uCommon - uRealizable‖ := by
  dsimp only
  let Q := R₀.toCanonicalCoherentPositiveTimePullback
  let K := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
      (halfExtent n) N hN (beta n) (hbeta n)
  let fz := periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
      (halfExtent n) N z
  let uCommon := Q.translatedPositiveHalfL2LinearMap hInvariant C n 2 F
  let uRealizable := Q.positiveHalfL2LinearMap hInvariant n
      (R.realizableCarrierTranslation hInvariant n 1 F)
  have hEq :=
    R₀.canonicalRealizableOneStep_OS_rawPath_defect_eq_kernelPairing
      R hInvariant C n F z
  have hBound :=
    realL2HilbertSchmidtKernelPairing_norm_le K fz (uCommon - uRealizable)
  have hFzNorm :
      ‖fz‖ = ‖z‖ :=
    (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
      (halfExtent n) N).norm_map z
  rw [hFzNorm] at hBound
  simpa only [Real.norm_eq_abs, Q, K, fz, uCommon, uRealizable, hEq] using hBound

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback.completedBoundaryTransfer_two_realizableOneStep_defect_norm_eq
#print axioms MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection.canonicalRealizableOneStep_OS_rawPath_defect_eq_kernelPairing
#print axioms MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection.canonicalRealizableOneStep_OS_rawPath_defect_abs_le
