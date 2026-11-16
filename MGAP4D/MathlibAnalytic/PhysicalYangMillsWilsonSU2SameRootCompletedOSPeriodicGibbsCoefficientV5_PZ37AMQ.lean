import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedBeta0CompletedOSGibbsCoefficientV5_PZ37AMQ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMQ — same-root *periodic* Wilson Gibbs OS coefficient

The general oriented-Gibbs readback of the first AMQ file is insufficient for
identifying the particular finite periodic SU(N) system underlying AMP.

Here the completed OS boundary coefficient is pulled back through the *exact*
interpolation, fixed lattice and Gibbs measure of the same coherent Q object:

  μ_n = (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n))
          N hN (beta n) (hbeta n)).gibbsMeasure.

Thus there is no replacement of the original periodic Wilson action or its
measure. The integrand remains the reflected positive-time observable
Theta(translate_1 F) * G. There is still no identification of the positive-time
readout with arbitrary physical Gauss-law endpoint functions, nor a proof that
the resulting integral equals AMP's literal normalized pair four-Haar integral.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37AMQ_periodicSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩
local instance p4Q2PZ37AMQ_periodicGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2PZ37AMQ_periodicCompact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2PZ37AMQ_periodicCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2PZ37AMQ_periodicMeasurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2PZ37AMQ_periodicBorel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Genuine finite periodic Wilson Gibbs coefficient of the *completed OS*
boundary operator at boundary time 2, derived from the same coherent model Q,
with its exact lattice side length, gauge group, beta n, interpolation, and
original Wilson Gibbs measure. No four-Haar kernel identification is asserted. -/
theorem p4Q2PZ37AMQ_completedBoundary_two_canonicalMoments_inner_eq_periodicWilsonGibbs
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
    let O : physicalYangMillsGaugeInvariantObservableSubalgebra S :=
      D.reflection
        ((Pn.toPositiveTime (Tn.carrierTranslation 1 F)) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) *
        ((Pn.toPositiveTime G) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S)
    inner ℝ
      (Q.completedBoundaryTransfer hInvariant C n 2
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F))
      (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n G) =
      ∫ U : PeriodicHypercubicEvenEdge (halfExtent n) →
          Matrix.specialUnitaryGroup (Fin N) ℂ,
        (O : BoundedContinuousFunction S.Configuration ℝ)
          (Q.interpolate n U)
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n))
          N hN (beta n) (hbeta n)).gibbsMeasure := by
  dsimp only
  let Pn := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  let O : physicalYangMillsGaugeInvariantObservableSubalgebra S :=
    D.reflection
      ((Pn.toPositiveTime (Tn.carrierTranslation 1 F)) :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) *
      ((Pn.toPositiveTime G) :
        physicalYangMillsGaugeInvariantObservableSubalgebra S)
  calc
    inner ℝ
      (Q.completedBoundaryTransfer hInvariant C n 2
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F))
      (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n G) =
      D.osBilinForm Pn.omega
        (Pn.toPositiveTime (Tn.carrierTranslation 1 F))
        (Pn.toPositiveTime G) := by
      exact p4Q2PZ37AMQ_completedBoundary_two_canonicalMoments_inner_eq_OSForm
        Q hInvariant C n F G
    _ = physicalYangMillsApproximatingGaugeInvariantWeakStarState S n O := by
      rw [D.osBilinForm_apply]
      rfl
    _ = ∫ U : PeriodicHypercubicEvenEdge (halfExtent n) →
          Matrix.specialUnitaryGroup (Fin N) ℂ,
        (O : BoundedContinuousFunction S.Configuration ℝ)
          (Q.interpolate n U)
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n))
          N hN (beta n) (hbeta n)).gibbsMeasure := by
      rw [physicalYangMillsApproximatingGaugeInvariantWeakStarState_apply,
        physicalYangMillsApproximatingGaugeInvariantExpectation_apply,
        Q.approximatingMeasure_toMeasure_eq n]
      exact MeasureTheory.integral_map
        (Q.interpolate_measurable n).aemeasurable
        ((O : BoundedContinuousFunction S.Configuration ℝ).continuous.aestronglyMeasurable)

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMQ_completedBoundary_two_canonicalMoments_inner_eq_periodicWilsonGibbs
