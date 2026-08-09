import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableOneStepExact3320Gap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryMomentGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundedContinuousReflectionPositivity
import Mathlib.Tactic

noncomputable section

open MeasureTheory

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableOneStepBoundaryMomentSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableOneStepBoundaryMomentSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableOneStepBoundaryMomentSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableOneStepBoundaryMomentSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableOneStepBoundaryMomentSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableOneStepBoundaryMomentSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The Gram feature belonging to every actual finite Wilson OS carrier is
integrable automatically: the positive-half observable is bounded continuous,
and compact-Haar finiteness supplies the domination. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_boundaryMoment_gram_integrable
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
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
      (halfExtent n) N) :
    Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        (halfExtent n) N hN (beta n) (hbeta n)
        (fun x =>
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent N hN beta hbeta B hInvariant n F x)
        b)
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N) := by
  exact
    periodicHypercubicEvenBoundaryObservableGramFeature_integrable_of_boundedContinuous
      (halfExtent n) N hN (beta n) (hbeta n)
      (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S D halfExtent N hN beta hbeta B hInvariant n F)
      b

/-- For actual Wilson OS carriers, the full reflected Gibbs integral equals the
boundary-Haar squared Gram-moment integral with no separate integrability
assumption. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq_auto
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
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n F =
      ∫ b,
        ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
  exact
    physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq
      S D halfExtent N hN beta hbeta B hInvariant n F
      (fun b =>
        physical_yang_mills_evenPeriodicWilsonOS_boundaryMoment_gram_integrable
          S D halfExtent N hN beta hbeta B hInvariant n F b)

/-- The exact one-slab quantitative input stated literally on the actual
compact-Haar `SU(N)` finite Wilson Gibbs reflected integral.

This is equivalent to the centered one-step OS norm estimate of #1485; no
heat-bath dynamics or foreign coercivity constant is introduced. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320FiniteIntegralGapCertificate
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  oneStep_centered_finiteReflectedIntegral_le :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          (R.realizableCarrierTranslation hInvariant n 1
            (Pn.vacuumCenteredCarrier F)) ≤
        (physicalYangMillsExact3320OneStepNormFactor S n) ^ 2 *
          physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
            (Pn.vacuumCenteredCarrier F)

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320FiniteIntegralGapCertificate

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

/-- Literal one-step Wilson Gibbs reflected-integral decay generates exactly
the centered one-step OS norm certificate used by the discrete semigroup lane. -/
noncomputable def toOneStepExact3320GapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320FiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  oneStep_centered_norm_le := by
    intro n F
    dsimp only
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    have h := A.oneStep_centered_finiteReflectedIntegral_le n F
    dsimp only at h
    rw [← physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral,
      ← physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral] at h
    rw [Pn.osQuadraticValue_eq_norm_sq, Pn.osQuadraticValue_eq_norm_sq] at h
    have hr : 0 ≤ physicalYangMillsExact3320OneStepNormFactor S n :=
      (physicalYangMillsExact3320OneStepNormFactor_pos S n).le
    have hx :
        0 ≤ ‖R.realizableCarrierTranslation hInvariant n 1
          (Pn.vacuumCenteredCarrier F)‖ := norm_nonneg _
    have hy : 0 ≤ ‖Pn.vacuumCenteredCarrier F‖ := norm_nonneg _
    nlinarith [mul_nonneg hr hy]

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320FiniteIntegralGapCertificate

/-- The same genuine one-slab input localized to the shared boundary Gram
moments.  Full-configuration Wilson Gibbs integration, boundary-coordinate
transport, and Gram integrability are all theorem-generated. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryMomentGapCertificate
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  oneStep_centered_boundaryMoment_le :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      (∫ b,
        ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          (R.realizableCarrierTranslation hInvariant n 1
            (Pn.vacuumCenteredCarrier F)) b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) ≤
      (physicalYangMillsExact3320OneStepNormFactor S n) ^ 2 *
        ∫ b,
          ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
            (Pn.vacuumCenteredCarrier F) b‖ ^ 2
          ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryMomentGapCertificate

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

/-- Boundary Gram-moment one-step decay reconstructs the literal full Wilson
Gibbs reflected-integral certificate. -/
noncomputable def toFiniteIntegralGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320FiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  oneStep_centered_finiteReflectedIntegral_le := by
    intro n F
    dsimp only
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    rw [physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq_auto,
      physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq_auto]
    exact A.oneStep_centered_boundaryMoment_le n F

/-- Boundary-local one-step decay therefore generates the exact centered OS
one-step norm certificate and all downstream discrete/continuum gap machinery. -/
noncomputable def toOneStepExact3320GapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant :=
  A.toFiniteIntegralGapCertificate.toOneStepExact3320GapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryMomentGapCertificate

end MathlibAnalytic
end MGAP4D

end
