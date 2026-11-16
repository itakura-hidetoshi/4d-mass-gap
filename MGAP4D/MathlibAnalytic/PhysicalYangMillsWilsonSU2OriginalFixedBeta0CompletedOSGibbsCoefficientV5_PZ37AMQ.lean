import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedBeta0FullPairFourHaarV5_PZ37AMP
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCompletedBoundaryTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSPullback
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMQ — actual finite Wilson Gibbs coefficient on the OS side

AMP proved the original SU(2) beta0 pair Wilson four-Haar coefficient. The
present unit independently expands the *completed OS boundary* coefficient
at boundary time two, first as the reflected OS positive-time bilinear form,
then as an integral under the original finite oriented Wilson Gibbs measure.

The proved OS integral has a reflected positive-time observable as its
integrand; AMP has two normalized one-slab Wilson kernels under pair Haar
integration. No identification of these different integrands, finite-time
observable readout, Markov disintegration, or OS/Wilson one-slab equality is
assumed or asserted. The remaining mismatch is deliberately retained.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37AMQ_sideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩
local instance p4Q2PZ37AMQ_group (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2PZ37AMQ_compact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2PZ37AMQ_countable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2PZ37AMQ_measurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2PZ37AMQ_borel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- On genuine positive-time carrier observables, the completed boundary
time-two coefficient equals the actual reflected finite OS bilinear form,
without any hypothetical OS/physical-one-slab weak intertwining hypothesis.
This is an OS-side equality, not the AMP four-Haar coefficient. -/
theorem p4Q2PZ37AMQ_completedBoundary_two_canonicalMoments_inner_eq_OSForm
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (F G : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let Tn := C.toPositiveTimeObservableContractionSemigroup n
    inner ℝ
      (Q.completedBoundaryTransfer hInvariant C n 2
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F))
      (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n G) =
      D.osBilinForm Pn.omega
        (Pn.toPositiveTime (Tn.carrierTranslation 1 F))
        (Pn.toPositiveTime G) := by
  dsimp only
  let Pn := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  have hTransfer :
      Q.completedBoundaryTransfer hInvariant C n 2
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          (Tn.carrierTranslation 1 F) := by
    simpa only [show (2 : NNReal) / 2 = 1 by norm_num] using
      Q.completedBoundaryTransfer_apply_canonicalBoundaryMoment
        hInvariant C n (2 : NNReal) F
  calc
    inner ℝ
      (Q.completedBoundaryTransfer hInvariant C n 2
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F))
      (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n G) =
      inner ℝ
        (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (Pn.physicalState (Tn.carrierTranslation 1 F)))
        (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (Pn.physicalState G)) := by
      rw [hTransfer]
      rw [Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState]
      rw [Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState]
    _ = inner ℝ (Pn.physicalState (Tn.carrierTranslation 1 F))
        (Pn.physicalState G) := by
      exact (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n).inner_map_map _ _
    _ = D.osBilinForm Pn.omega
        (Pn.toPositiveTime (Tn.carrierTranslation 1 F))
        (Pn.toPositiveTime G) := by
      rw [Pn.inner_physicalState_physicalState, Pn.inner_eq_osBilinForm]

/-- The same genuine completed OS boundary coefficient is an integral with
respect to the *original finite oriented Wilson Gibbs measure*, with the
reflected translated positive-time observable as the integrand.

No Markov/Fubini disintegration into AMP's pair-Haar four-fold integral has
been used; proving that specific disintegration and its typed readout remains
the next task. -/
theorem p4Q2PZ37AMQ_completedBoundary_two_canonicalMoments_inner_eq_originalGibbs
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    (Gauge : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit E.toLatticeEmbedding)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData (Gauge.toSymmetryLimit L))
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      (Gauge.toSymmetryLimit L) D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState
          (Gauge.toSymmetryLimit L) n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      (Gauge.toSymmetryLimit L) D halfExtent N hN beta hbeta
        Q.toWeakStarBridge hInvariant)
    (n : ℕ)
    (F G : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      (Gauge.toSymmetryLimit L) D halfExtent N hN beta hbeta
      Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      (Gauge.toSymmetryLimit L) D halfExtent N hN beta hbeta
        Q.toWeakStarBridge hInvariant n
    let Tn := C.toPositiveTimeObservableContractionSemigroup n
    let O : physicalYangMillsGaugeInvariantObservableSubalgebra (Gauge.toSymmetryLimit L) :=
      D.reflection
        ((Pn.toPositiveTime (Tn.carrierTranslation 1 F)) :
          physicalYangMillsGaugeInvariantObservableSubalgebra (Gauge.toSymmetryLimit L)) *
        ((Pn.toPositiveTime G) :
          physicalYangMillsGaugeInvariantObservableSubalgebra (Gauge.toSymmetryLimit L))
    inner ℝ
      (Q.completedBoundaryTransfer hInvariant C n 2
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          (Gauge.toSymmetryLimit L) D halfExtent N hN beta hbeta
          Q.toWeakStarBridge hInvariant n F))
      (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        (Gauge.toSymmetryLimit L) D halfExtent N hN beta hbeta
        Q.toWeakStarBridge hInvariant n G) =
      ∫ U,
        (O : BoundedContinuousFunction (Gauge.toSymmetryLimit L).Configuration ℝ)
          (E.interpolate (L.subsequence n) U)
        ∂(E.system (L.subsequence n)).gibbsMeasure := by
  dsimp only
  let Pn := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    (Gauge.toSymmetryLimit L) D halfExtent N hN beta hbeta
      Q.toWeakStarBridge hInvariant n
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  let O : physicalYangMillsGaugeInvariantObservableSubalgebra (Gauge.toSymmetryLimit L) :=
    D.reflection
      ((Pn.toPositiveTime (Tn.carrierTranslation 1 F)) :
        physicalYangMillsGaugeInvariantObservableSubalgebra (Gauge.toSymmetryLimit L)) *
      ((Pn.toPositiveTime G) :
        physicalYangMillsGaugeInvariantObservableSubalgebra (Gauge.toSymmetryLimit L))
  calc
    inner ℝ
      (Q.completedBoundaryTransfer hInvariant C n 2
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          (Gauge.toSymmetryLimit L) D halfExtent N hN beta hbeta
          Q.toWeakStarBridge hInvariant n F))
      (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        (Gauge.toSymmetryLimit L) D halfExtent N hN beta hbeta
        Q.toWeakStarBridge hInvariant n G) =
      D.osBilinForm Pn.omega
        (Pn.toPositiveTime (Tn.carrierTranslation 1 F))
        (Pn.toPositiveTime G) := by
      exact p4Q2PZ37AMQ_completedBoundary_two_canonicalMoments_inner_eq_OSForm
        Q hInvariant C n F G
    _ = ∫ U,
        (O : BoundedContinuousFunction (Gauge.toSymmetryLimit L).Configuration ℝ)
          (E.interpolate (L.subsequence n) U)
        ∂(E.system (L.subsequence n)).gibbsMeasure := by
      rw [D.osBilinForm_apply]
      change
        physicalYangMillsApproximatingGaugeInvariantWeakStarState
          (Gauge.toSymmetryLimit L) n O =
        ∫ U,
          (O : BoundedContinuousFunction (Gauge.toSymmetryLimit L).Configuration ℝ)
            (E.interpolate (L.subsequence n) U)
          ∂(E.system (L.subsequence n)).gibbsMeasure
      exact physical_yang_mills_oriented_approximatingWeakStarState_eq_gibbs_pullback
        Gauge L n O

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMQ_completedBoundary_two_canonicalMoments_inner_eq_OSForm
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMQ_completedBoundary_two_canonicalMoments_inner_eq_originalGibbs
