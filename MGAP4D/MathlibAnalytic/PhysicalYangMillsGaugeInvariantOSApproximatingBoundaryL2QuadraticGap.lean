import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2TransferGap
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- A shared-boundary `L²` transfer-gap package stated as a quadratic norm
estimate rather than an operator-norm estimate.

For an actual Wilson transfer kernel, the estimate

`‖K_{n,t} v‖² ≤ q(t) ‖v‖²`

is the natural Rayleigh-type analytic input.  Positivity of `q(t)` lets Mathlib
take the square root and `ContinuousLinearMap.opNorm_le_bound` then generates

`‖K_{n,t}‖ ≤ sqrt (q(t))`.

All remaining Wilson OS and continuum Hamiltonian conclusions are inherited
from the existing boundary-`L²` transfer package. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2QuadraticGapCertificate
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
      S D halfExtent N hN beta hbeta B hInvariant) where
  mass : ℝ
  mass_pos : 0 < mass
  quadraticDecayFactor : NNReal → ℝ
  quadraticDecayFactor_nonneg : ∀ t, 0 ≤ quadraticDecayFactor t
  slope_tendsto :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (1 - Real.sqrt (quadraticDecayFactor (t + t))))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass)
  exchange : ∀ n,
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
      (C.toPositiveTimeObservableContractionSemigroup n)
  gram_integrable :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
      (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
        (halfExtent n) N),
      Integrable
        (periodicHypercubicEvenBoundaryObservableGramFeature
          (halfExtent n) N hN (beta n) (hbeta n)
          (fun x =>
            physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
              S D halfExtent N hN beta hbeta B hInvariant n F x)
          b)
        (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N)
  boundaryMoment_memLp :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier),
      MemLp
        (fun b =>
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta B hInvariant n F b)
        2
        (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)
  boundaryTransfer :
    (n : ℕ) → NNReal →
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N
  boundaryMoment_intertwining :
    ∀ (n : ℕ) (t : NNReal),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      let Tn := C.toPositiveTimeObservableContractionSemigroup n
      ∀ F : Pn.Carrier,
        boundaryTransfer n t
            (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
              S D halfExtent N hN beta hbeta B hInvariant n
              (Pn.vacuumCenteredCarrier F)
              (boundaryMoment_memLp n (Pn.vacuumCenteredCarrier F))) =
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F))
            (boundaryMoment_memLp n
              (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F)))
  boundaryTransfer_quadratic_bound :
    ∀ (n : ℕ) (t : NNReal)
      (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2
        (halfExtent n) N),
      ‖boundaryTransfer n t v‖ ^ 2 ≤
        quadraticDecayFactor t * ‖v‖ ^ 2

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2QuadraticGapCertificate

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

/-- The quadratic transfer estimate yields the boundary-transfer operator-norm
estimate. -/
theorem boundaryTransfer_opNorm_le
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2QuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal) :
    ‖Q.boundaryTransfer n t‖ ≤
      Real.sqrt (Q.quadraticDecayFactor t) := by
  apply ContinuousLinearMap.opNorm_le_bound
    (Q.boundaryTransfer n t) (Real.sqrt_nonneg _)
  intro v
  have hsq := Q.boundaryTransfer_quadratic_bound n t v
  have hq : 0 ≤ Q.quadraticDecayFactor t :=
    Q.quadraticDecayFactor_nonneg t
  have hsqrt : 0 ≤ Real.sqrt (Q.quadraticDecayFactor t) :=
    Real.sqrt_nonneg _
  have hrhs :
      0 ≤ Real.sqrt (Q.quadraticDecayFactor t) * ‖v‖ :=
    mul_nonneg hsqrt (norm_nonneg v)
  have hsqrt_sq :
      (Real.sqrt (Q.quadraticDecayFactor t)) ^ 2 =
        Q.quadraticDecayFactor t :=
    Real.sq_sqrt hq
  nlinarith [norm_nonneg (Q.boundaryTransfer n t v), norm_nonneg v]

/-- Convert the quadratic boundary-transfer package into the operator-norm
boundary-`L²` transfer package. -/
noncomputable def toApproximatingBoundaryL2TransferGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2QuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  quadraticDecayFactor := Q.quadraticDecayFactor
  quadraticDecayFactor_nonneg := Q.quadraticDecayFactor_nonneg
  slope_tendsto := Q.slope_tendsto
  exchange := Q.exchange
  gram_integrable := Q.gram_integrable
  boundaryMoment_memLp := Q.boundaryMoment_memLp
  boundaryTransfer := Q.boundaryTransfer
  boundaryMoment_intertwining := Q.boundaryMoment_intertwining
  boundaryTransfer_opNorm_le := Q.boundaryTransfer_opNorm_le

/-- A quadratic boundary-transfer estimate therefore supplies the integrated
boundary-moment gap certificate. -/
noncomputable def toApproximatingBoundaryMomentGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2QuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2TransferGapCertificate
    |>.toApproximatingBoundaryMomentGapCertificate

/-- A quadratic boundary-transfer estimate therefore supplies the completed
finite Wilson OS vacuum-sector norm-decay certificate. -/
noncomputable def toApproximatingVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2QuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2TransferGapCertificate
    |>.toApproximatingVacuumGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2QuadraticGapCertificate

end MathlibAnalytic
end MGAP4D

end
