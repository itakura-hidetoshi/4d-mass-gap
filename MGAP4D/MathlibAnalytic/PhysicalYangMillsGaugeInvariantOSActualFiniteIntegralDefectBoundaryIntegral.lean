import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualFiniteIntegralDefectGeometry
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualAdjointSynthesisBoundaryTransferGap
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance actualDefectBoundarySideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance actualDefectBoundarySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance actualDefectBoundarySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance actualDefectBoundarySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance actualDefectBoundarySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance actualDefectBoundarySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Pointwise shared-boundary integrand of the actual finite Wilson transfer
defect.  It compares the squared canonical boundary Gram moment before and
after physical finite-OS transfer time `t`. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentDefectIntegrand
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
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
      (halfExtent n) N) : ℝ :=
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
      S D halfExtent N hN beta hbeta B hInvariant n F b‖ ^ 2 -
    ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
      S D halfExtent N hN beta hbeta B hInvariant n
      (Tn.carrierTranslation t F) b‖ ^ 2

/-- Integrated shared-boundary form of the actual finite Wilson transfer
defect. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentDefect
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
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) : ℝ :=
  ∫ b,
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentDefectIntegrand
      S D halfExtent N hN beta hbeta B hInvariant C n t F b
    ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentDefect

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
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}

/-- The squared boundary moment is integrable for every actual finite Wilson OS
carrier element; no certificate field is required. -/
theorem boundaryMoment_norm_sq_integrable
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    Integrable
      (fun b =>
        ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b‖ ^ 2)
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
  let hF :=
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_memLp_two
      S D halfExtent N hN beta hbeta B hInvariant n F
  exact (memLp_two_iff_integrable_sq_norm hF.1).1 hF

/-- The pointwise defect integrand is integrable, generated entirely from the
actual finite Wilson boundary-moment `L²` theorem. -/
theorem integrand_integrable
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    Integrable
      (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentDefectIntegrand
        S D halfExtent N hN beta hbeta B hInvariant C n t F)
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  unfold physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentDefectIntegrand
  exact
    (boundaryMoment_norm_sq_integrable n F).sub
      (boundaryMoment_norm_sq_integrable n (Tn.carrierTranslation t F))

/-- The actual finite reflected-integral defect is exactly one local
shared-boundary integral of the pointwise Gram-moment squared-norm loss.

This removes the last full-configuration integral from the defect geometry:
the quantity which must eventually receive a scale-uniform lower bound is now
an explicit boundary integral. -/
theorem finiteReflectedIntegralDefect_eq_boundaryMomentDefect
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegralDefect
        S D halfExtent N hN beta hbeta B hInvariant C n t F =
      physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentDefect
        S D halfExtent N hN beta hbeta B hInvariant C n t F := by
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  have hFgram : ∀ b, Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        (halfExtent n) N hN (beta n) (hbeta n)
        (fun x =>
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent N hN beta hbeta B hInvariant n F x)
        b)
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N) :=
    fun b =>
      PhysicalYangMillsEvenPeriodicWilsonOSActualAdjointSynthesisBoundaryTransferGapCertificate.gram_integrable
        (S := S) (D := D) (halfExtent := halfExtent) (N := N)
        (hN := hN) (beta := beta) (hbeta := hbeta) (B := B)
        (hInvariant := hInvariant) n F b
  have hTFgram : ∀ b, Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        (halfExtent n) N hN (beta n) (hbeta n)
        (fun x =>
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent N hN beta hbeta B hInvariant n
            (Tn.carrierTranslation t F) x)
        b)
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N) :=
    fun b =>
      PhysicalYangMillsEvenPeriodicWilsonOSActualAdjointSynthesisBoundaryTransferGapCertificate.gram_integrable
        (S := S) (D := D) (halfExtent := halfExtent) (N := N)
        (hN := hN) (beta := beta) (hbeta := hbeta) (B := B)
        (hInvariant := hInvariant) n (Tn.carrierTranslation t F) b
  have hFint := boundaryMoment_norm_sq_integrable n F
  have hTFint :=
    boundaryMoment_norm_sq_integrable n (Tn.carrierTranslation t F)
  change
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n F -
      physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n
        (Tn.carrierTranslation t F) =
      ∫ b,
        (‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta B hInvariant n F b‖ ^ 2 -
          ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta B hInvariant n
            (Tn.carrierTranslation t F) b‖ ^ 2)
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)
  rw [physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq
        S D halfExtent N hN beta hbeta B hInvariant n F hFgram,
      physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq
        S D halfExtent N hN beta hbeta B hInvariant n
        (Tn.carrierTranslation t F) hTFgram]
  exact (integral_sub hFint hTFint).symm

/-- The integrated boundary defect is nonnegative.  Pointwise nonnegativity is
not asserted: only its actual boundary average is forced nonnegative by finite
OS contraction. -/
theorem nonneg
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    0 ≤
      physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentDefect
        S D halfExtent N hN beta hbeta B hInvariant C n t F := by
  rw [← finiteReflectedIntegralDefect_eq_boundaryMomentDefect (C := C) n t F]
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegralDefect.nonneg
      (C := C) n t F

/-- The local shared-boundary defect inherits the exact finite-time cocycle law.
This expresses accumulated loss using only boundary integrals. -/
theorem add
    (n : ℕ) (s t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    let Tn := C.toPositiveTimeObservableContractionSemigroup n
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentDefect
        S D halfExtent N hN beta hbeta B hInvariant C n (s + t) F =
      physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentDefect
          S D halfExtent N hN beta hbeta B hInvariant C n t F +
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentDefect
          S D halfExtent N hN beta hbeta B hInvariant C n s
          (Tn.carrierTranslation t F) := by
  dsimp only
  rw [← finiteReflectedIntegralDefect_eq_boundaryMomentDefect (C := C),
      ← finiteReflectedIntegralDefect_eq_boundaryMomentDefect (C := C),
      ← finiteReflectedIntegralDefect_eq_boundaryMomentDefect (C := C)]
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegralDefect.add
      (C := C) n s t F

/-- The #2022 exponential gap input is exactly a lower bound on the local
shared-boundary defect integral of the centered carrier. -/
theorem exponential_lower_bound
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSActualFiniteIntegralExponentialGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    (1 - Real.exp (-Q.mass * (t : ℝ))) *
        physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
          S D halfExtent N hN beta hbeta B hInvariant n
          (Pn.vacuumCenteredCarrier F) ≤
      physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentDefect
        S D halfExtent N hN beta hbeta B hInvariant C n (t / 2)
        (Pn.vacuumCenteredCarrier F) := by
  dsimp only
  rw [← finiteReflectedIntegralDefect_eq_boundaryMomentDefect (C := C)]
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegralDefect.exponential_lower_bound
      (C := C) Q n t F

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentDefect

end MathlibAnalytic
end MGAP4D

end
