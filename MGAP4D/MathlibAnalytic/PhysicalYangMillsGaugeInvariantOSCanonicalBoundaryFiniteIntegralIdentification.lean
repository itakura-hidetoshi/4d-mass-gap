import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalBoundaryTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingFiniteIntegralGap
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance canonicalBoundaryFiniteIntegralSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundaryFiniteIntegralSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundaryFiniteIntegralSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundaryFiniteIntegralSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundaryFiniteIntegralSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundaryFiniteIntegralSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The squared norm of the canonical actual Wilson boundary moment is exactly
its actual finite reflected Wilson Gibbs integral.

This is the direct scalar identification behind the completed boundary
isometry: no decay, coercivity, closed-range, or spectral assumption is used. -/
theorem
    physical_yang_mills_evenPeriodicWilsonOS_canonicalBoundaryMomentL2_norm_sq_eq_finiteReflectedIntegral
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F‖ ^ 2 =
      physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n F := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  calc
    ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F‖ ^ 2 = ‖F‖ ^ 2 :=
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_norm_sq
        S D halfExtent N hN beta hbeta B hInvariant n F
    _ = Pn.osQuadraticValue F :=
      (Pn.osQuadraticValue_eq_norm_sq F).symm
    _ = physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n F :=
      physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n F

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- On a centered raw Wilson observable, applying the actual canonical boundary
transfer for boundary time `2 * t` and taking squared norm is exactly the
finite reflected Wilson integral of the physical time-`t` translated centered
observable.

Thus the canonical boundary strict-decay problem and the model-facing finite
reflected-integral decay problem are literally the same scalar quantity on the
dense physical boundary image. -/
theorem canonicalBoundaryTransfer_centeredBoundaryMoment_norm_sq_eq_finiteReflectedIntegral
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    let Tn := C.toPositiveTimeObservableContractionSemigroup n
    ‖L.canonicalBoundaryTransfer C n (2 * t)
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n
          (Pn.vacuumCenteredCarrier F))‖ ^ 2 =
      physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n
        (Tn.carrierTranslation t (Pn.vacuumCenteredCarrier F)) := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  have htime : (2 * t) / 2 = t := by
    ext
    norm_num
  rw [L.canonicalBoundaryTransfer_canonicalBoundaryMoment_intertwining
    C n (2 * t) (Pn.vacuumCenteredCarrier F)]
  rw [htime]
  exact
    physical_yang_mills_evenPeriodicWilsonOS_canonicalBoundaryMomentL2_norm_sq_eq_finiteReflectedIntegral
      S D halfExtent N hN beta hbeta B hInvariant n
      (Tn.carrierTranslation t (Pn.vacuumCenteredCarrier F))

/-- The actual finite reflected-integral decay inequality is equivalent, with
no loss and no auxiliary closed-range hypothesis, to squared-norm decay of the
actual canonical boundary transfer on the centered canonical boundary moment.

This fixes the remaining model-specific finite Wilson gap input as one scalar
inequality. -/
theorem finiteReflectedIntegral_decay_iff_canonicalBoundaryTransfer_centeredBoundaryMoment_decay
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal) (q : ℝ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    let Tn := C.toPositiveTimeObservableContractionSemigroup n
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n
        (Tn.carrierTranslation t (Pn.vacuumCenteredCarrier F)) ≤
      q * physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n
        (Pn.vacuumCenteredCarrier F) ↔
    ‖L.canonicalBoundaryTransfer C n (2 * t)
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n
          (Pn.vacuumCenteredCarrier F))‖ ^ 2 ≤
      q * ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n
        (Pn.vacuumCenteredCarrier F)‖ ^ 2 := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  have htranslated :=
    L.canonicalBoundaryTransfer_centeredBoundaryMoment_norm_sq_eq_finiteReflectedIntegral
      C n t F
  dsimp only at htranslated
  have hinitial :=
    physical_yang_mills_evenPeriodicWilsonOS_canonicalBoundaryMomentL2_norm_sq_eq_finiteReflectedIntegral
      S D halfExtent N hN beta hbeta B hInvariant n
      (Pn.vacuumCenteredCarrier F)
  constructor
  · intro h
    calc
      ‖L.canonicalBoundaryTransfer C n (2 * t)
          (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Pn.vacuumCenteredCarrier F))‖ ^ 2 =
        physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
          S D halfExtent N hN beta hbeta B hInvariant n
          (Tn.carrierTranslation t (Pn.vacuumCenteredCarrier F)) := htranslated
      _ ≤ q * physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
          S D halfExtent N hN beta hbeta B hInvariant n
          (Pn.vacuumCenteredCarrier F) := h
      _ = q * ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n
          (Pn.vacuumCenteredCarrier F)‖ ^ 2 := by
        rw [hinitial]
  · intro h
    calc
      physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
          S D halfExtent N hN beta hbeta B hInvariant n
          (Tn.carrierTranslation t (Pn.vacuumCenteredCarrier F)) =
        ‖L.canonicalBoundaryTransfer C n (2 * t)
          (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Pn.vacuumCenteredCarrier F))‖ ^ 2 := htranslated.symm
      _ ≤ q * ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n
          (Pn.vacuumCenteredCarrier F)‖ ^ 2 := h
      _ = q * physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
          S D halfExtent N hN beta hbeta B hInvariant n
          (Pn.vacuumCenteredCarrier F) := by
        rw [hinitial]

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

end MathlibAnalytic
end MGAP4D

end
