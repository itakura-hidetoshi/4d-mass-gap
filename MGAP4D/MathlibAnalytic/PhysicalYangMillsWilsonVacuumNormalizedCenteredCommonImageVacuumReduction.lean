import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedProjectedNonTopTopFactorization
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNPrimaryPlaquetteTwoModePointwiseCoherentReadout
import Mathlib.Tactic

/-!
# Reduce centered common-carrier convergence to the OS-vacuum pair image

PR #5070 shows that strong convergence of the canonical projected physical
non-top excitation follows from strong convergence of two common-carrier
sequences:

* the unprojected vacuum-normalized centered pair image;
* the physical pair-top image.

This file closes the first sequence up to the moving OS-vacuum pair alone.

The uncentered two-mode pair is an explicit primary-plaquette Wilson mode.
The #5003 pointwise coherent-readout package already proves exact projective
transition coherence of that concrete Haar mode.  Therefore its common-carrier
image is eventually exactly one fixed continuum mode.

The actual vacuum-normalized centered pair is

  finiteVacuumCentered (OS vacuum pair) (uncentered mode).

Since the common-carrier map is a linear isometry, this identity survives
exactly after projective embedding.  Consequently, along any scale map tending
to infinity, convergence of the OS-vacuum pair image alone implies convergence
of the unprojected centered image.

Combining with #5070 leaves only two moving vacuum-like common-carrier
sequences:

1. the canonical-sign OS-vacuum pair image;
2. the physical pair-top image.

No H1-D5 compatibility, vacuum/top alignment, or continuum dynamics is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance centeredCommonVacuumReductionTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance centeredCommonVacuumReductionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance centeredCommonVacuumReductionSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance centeredCommonVacuumReductionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance centeredCommonVacuumReductionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance centeredCommonVacuumReductionSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance centeredCommonVacuumReductionSpatialHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section CenteredCommonVacuumReduction

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N} {hN2 : 2 ≤ N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)

/-- Common-carrier image of the canonical-sign finite OS vacuum pair. -/
noncomputable def
    physicalYangMillsVacuumNormalizedSUNOSVacuumPairContinuumImage
    (n : ℕ) :
    Lp ℝ 2 L.continuumMeasure :=
  R.spatialSlicePairHaarProjectiveContinuumL2Isometry L n
    (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)

/-- Common-carrier image of the explicit uncentered primary-plaquette two-mode
pair. -/
noncomputable def
    physicalYangMillsSUNTwoModeUncenteredPairContinuumImage
    (k : Fin 2) (n : ℕ) :
    Lp ℝ 2 L.continuumMeasure :=
  R.spatialSlicePairHaarProjectiveContinuumL2Isometry L n
    (physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2
      (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n)

/-- Projective embedding commutes exactly with the actual vacuum-centering used
by the canonical-sign finite OS pair. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeCenteredPairContinuumImage_eq_finiteVacuumCentered
    (k : Fin 2) (n : ℕ) :
    physicalYangMillsVacuumNormalizedSUNTwoModeCenteredPairContinuumImage
        (hN2 := hN2) Q hInvariant R L k n =
      finiteVacuumCentered
        (physicalYangMillsVacuumNormalizedSUNOSVacuumPairContinuumImage
          Q hInvariant R L n)
        (physicalYangMillsSUNTwoModeUncenteredPairContinuumImage
          (hN2 := hN2) (Q := Q) R L k n) := by
  let I := R.spatialSlicePairHaarProjectiveContinuumL2Isometry L n
  let vac :=
    physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n
  let u :=
    physicalYangMillsSUNTwoModeExplicitUncenteredBoundaryPairL2
      (halfExtent := halfExtent) (N := N) (hN2 := hN2) k n
  change
    I
        (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN) (hN2 := hN2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n) =
      finiteVacuumCentered (I vac) (I u)
  rw [
    physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2_eq_finiteVacuumCentered
      (S := S) (D := D) (halfExtent := halfExtent)
      (N := N) (hN := hN) (hN2 := hN2)
      (beta := beta) (hbeta := hbeta)
      (Q := Q.vacuumNormalized) (hInvariant := hInvariant) k n]
  exact linearIsometry_finiteVacuumCentered I vac u

/-- Once scale n contains the source support of mode k, the explicit
uncentered pair image is exactly the named continuum mode supplied by #5003. -/
theorem
    physicalYangMillsSUNTwoModeUncenteredPairContinuumImage_eq_continuumMode
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
        S D halfExtent N hN hN2 beta hbeta Q F R hInvariant)
    (k : Fin 2) (n : ℕ)
    (hkn :
      (C.toTwoModeCylinderData L).cylinderIndex k ⊆ R.marginalIndex n) :
    physicalYangMillsSUNTwoModeUncenteredPairContinuumImage
        (hN2 := hN2) (Q := Q) R L k n =
      (C.toTwoModeCylinderData L).continuumMode k := by
  let C2 := C.toTwoModeCylinderData L
  let b :=
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
      (halfExtent n) hN2 k
  change
    L.finiteMarginalL2Pullback (R.marginalIndex n)
      (R.boundaryHaarProjectiveL2Isometry n
        (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
          (halfExtent n) N
          (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
            (halfExtent n) N b))) =
      C2.continuumMode k
  rw [periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundary_leftInverse]
  change
    L.finiteMarginalL2Pullback (R.marginalIndex n)
      (R.primarySpatialPlaquetteHaarProjectiveL2Isometry n
        (specialUnitaryWilsonHaarTwoMode hN2 k)) =
      L.finiteMarginalL2Pullback (C2.cylinderIndex k) (C2.cylinderVector k)
  rw [C2.primaryPlaquetteWilsonTwoMode_eq_transition k n hkn]
  exact
    (L.finiteMarginalL2Pullback_compatible hkn (C2.cylinderVector k)).symm

/-- The explicit uncentered pair common image is eventually literally constant
at the named continuum Wilson mode. -/
theorem
    physicalYangMillsSUNTwoModeUncenteredPairContinuumImage_eventually_eq_continuumMode
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
        S D halfExtent N hN hN2 beta hbeta Q F R hInvariant)
    (k : Fin 2) :
    (fun _ : ℕ => (C.toTwoModeCylinderData L).continuumMode k) =ᶠ[atTop]
      (fun n =>
        physicalYangMillsSUNTwoModeUncenteredPairContinuumImage
          (hN2 := hN2) (Q := Q) R L k n) := by
  let C2 := C.toTwoModeCylinderData L
  filter_upwards [C2.supportEventually k] with n hn
  exact
    (physicalYangMillsSUNTwoModeUncenteredPairContinuumImage_eq_continuumMode
      (hN2 := hN2) Q hInvariant R L C k n hn).symm

/-- Hence the uncentered pair image converges strongly to its fixed continuum
mode. -/
theorem
    physicalYangMillsSUNTwoModeUncenteredPairContinuumImage_tendsto
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
        S D halfExtent N hN hN2 beta hbeta Q F R hInvariant)
    (k : Fin 2) :
    Tendsto
      (fun n =>
        physicalYangMillsSUNTwoModeUncenteredPairContinuumImage
          (hN2 := hN2) (Q := Q) R L k n)
      atTop
      (𝓝 ((C.toTwoModeCylinderData L).continuumMode k)) := by
  exact tendsto_const_nhds.congr'
    (physicalYangMillsSUNTwoModeUncenteredPairContinuumImage_eventually_eq_continuumMode
      (hN2 := hN2) Q hInvariant R L C k)

/-- Along any cofinal scale map, convergence of the canonical OS-vacuum pair
image alone implies convergence of the actual unprojected centered pair image. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeCenteredPairContinuumImage_tendsto_of_vacuumPair_tendsto
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
        S D halfExtent N hN hN2 beta hbeta Q F R hInvariant)
    (k : Fin 2)
    (scale : ℕ → ℕ)
    (hScale : Tendsto scale atTop atTop)
    (vacuumLimit : Lp ℝ 2 L.continuumMeasure)
    (hVacuum :
      Tendsto
        (fun j =>
          physicalYangMillsVacuumNormalizedSUNOSVacuumPairContinuumImage
            Q hInvariant R L (scale j))
        atTop
        (𝓝 vacuumLimit)) :
    Tendsto
      (fun j =>
        physicalYangMillsVacuumNormalizedSUNTwoModeCenteredPairContinuumImage
          (hN2 := hN2) Q hInvariant R L k (scale j))
      atTop
      (𝓝
        (finiteVacuumCentered
          vacuumLimit
          ((C.toTwoModeCylinderData L).continuumMode k))) := by
  have hUncentered :
      Tendsto
        (fun j =>
          physicalYangMillsSUNTwoModeUncenteredPairContinuumImage
            (hN2 := hN2) (Q := Q) R L k (scale j))
        atTop
        (𝓝 ((C.toTwoModeCylinderData L).continuumMode k)) :=
    (physicalYangMillsSUNTwoModeUncenteredPairContinuumImage_tendsto
      (hN2 := hN2) Q hInvariant R L C k).comp hScale
  have hCentered :
      Tendsto
        (fun j =>
          finiteVacuumCentered
            (physicalYangMillsVacuumNormalizedSUNOSVacuumPairContinuumImage
              Q hInvariant R L (scale j))
            (physicalYangMillsSUNTwoModeUncenteredPairContinuumImage
              (hN2 := hN2) (Q := Q) R L k (scale j)))
        atTop
        (𝓝
          (finiteVacuumCentered
            vacuumLimit
            ((C.toTwoModeCylinderData L).continuumMode k))) := by
    unfold finiteVacuumCentered
    exact
      hUncentered.sub
        ((hVacuum.inner hUncentered).smul hVacuum)
  apply hCentered.congr'
  filter_upwards with j
  exact
    (physicalYangMillsVacuumNormalizedSUNTwoModeCenteredPairContinuumImage_eq_finiteVacuumCentered
      (hN2 := hN2) Q hInvariant R L k (scale j)).symm

/-- Combined post-H1-D5 convergence reduction.

Along any cofinal scale map, strong convergence of only the OS-vacuum pair and
the physical pair-top image theorem-generates strong convergence of the
canonical projected physical non-top excitation. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage_tendsto_of_vacuumPair_top_tendsto
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
        S D halfExtent N hN hN2 beta hbeta Q F R hInvariant)
    (k : Fin 2)
    (scale : ℕ → ℕ)
    (hScale : Tendsto scale atTop atTop)
    (vacuumLimit topLimit : Lp ℝ 2 L.continuumMeasure)
    (hVacuum :
      Tendsto
        (fun j =>
          physicalYangMillsVacuumNormalizedSUNOSVacuumPairContinuumImage
            Q hInvariant R L (scale j))
        atTop
        (𝓝 vacuumLimit))
    (hTop :
      Tendsto
        (fun j =>
          physicalYangMillsSUNPhysicalPairTopContinuumImage
            (Q := Q) R L (scale j))
        atTop
        (𝓝 topLimit)) :
    Tendsto
      (fun j =>
        physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage
          (hN2 := hN2) Q hInvariant R L k (scale j))
      atTop
      (𝓝
        (let centeredLimit :=
          finiteVacuumCentered
            vacuumLimit
            ((C.toTwoModeCylinderData L).continuumMode k)
        centeredLimit - inner ℝ topLimit centeredLimit • topLimit)) := by
  let centeredLimit :=
    finiteVacuumCentered
      vacuumLimit
      ((C.toTwoModeCylinderData L).continuumMode k)
  have hCentered :
      Tendsto
        (fun j =>
          physicalYangMillsVacuumNormalizedSUNTwoModeCenteredPairContinuumImage
            (hN2 := hN2) Q hInvariant R L k (scale j))
        atTop
        (𝓝 centeredLimit) := by
    simpa [centeredLimit] using
      physicalYangMillsVacuumNormalizedSUNTwoModeCenteredPairContinuumImage_tendsto_of_vacuumPair_tendsto
        (hN2 := hN2) Q hInvariant R L C k scale hScale vacuumLimit hVacuum
  simpa [centeredLimit] using
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage_tendsto_of_centered_top_tendsto
      (hN2 := hN2) Q hInvariant R L k scale centeredLimit topLimit hCentered hTop

end CenteredCommonVacuumReduction

end

end MathlibAnalytic
end MGAP4D
