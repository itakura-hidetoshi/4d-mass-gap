import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualFiniteIntegralDefectBoundaryIntegral
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableDiscreteSemigroup
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableDefectSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableDefectSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableDefectSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableDefectSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableDefectSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableDefectSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Finite reflected-integral defect at an actually realizable nonnegative
integer lattice-time displacement.

Unlike the all-`NNReal` approximating-semigroup defect, this quantity uses only
the discrete physical Wilson translation supplied by realizable temporal
covariance.  No finite-lattice interpolation to arbitrary real time is used. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSRealizableFiniteReflectedIntegralDefect
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
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) : ℝ :=
  physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F -
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      (R.realizableCarrierTranslation hInvariant n k F)

/-- Pointwise shared-boundary integrand of the realizable finite Wilson defect. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryMomentDefectIntegrand
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
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
      (halfExtent n) N) : ℝ :=
  ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F b‖ ^ 2 -
    ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      (R.realizableCarrierTranslation hInvariant n k F) b‖ ^ 2

/-- Shared-boundary Haar integral of the realizable finite Wilson defect. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryMomentDefect
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
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) : ℝ :=
  ∫ b,
    physicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryMomentDefectIntegrand
      S D halfExtent N hN beta hbeta Q E R hInvariant n k F b
    ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableFiniteReflectedIntegralDefect

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

/-- The realizable reflected-integral defect is exactly the squared OS carrier
norm loss.  This identity does not assert that the loss is nonnegative. -/
theorem eq_carrier_norm_sq_sub
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSRealizableFiniteReflectedIntegralDefect
        S D halfExtent N hN beta hbeta Q E R hInvariant n k F =
      ‖F‖ ^ 2 - ‖R.realizableCarrierTranslation hInvariant n k F‖ ^ 2 := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  change
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F -
      physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        (R.realizableCarrierTranslation hInvariant n k F) =
      ‖F‖ ^ 2 - ‖R.realizableCarrierTranslation hInvariant n k F‖ ^ 2
  rw [← physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F,
      ← physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        (R.realizableCarrierTranslation hInvariant n k F),
      Pn.osQuadraticValue_eq_norm_sq, Pn.osQuadraticValue_eq_norm_sq]

/-- The realizable defect has the exact additive cocycle law on nonnegative
integer lattice-step counts. -/
theorem add
    (n k l : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSRealizableFiniteReflectedIntegralDefect
        S D halfExtent N hN beta hbeta Q E R hInvariant n (k + l) F =
      physicalYangMillsEvenPeriodicWilsonOSRealizableFiniteReflectedIntegralDefect
          S D halfExtent N hN beta hbeta Q E R hInvariant n k F +
        physicalYangMillsEvenPeriodicWilsonOSRealizableFiniteReflectedIntegralDefect
          S D halfExtent N hN beta hbeta Q E R hInvariant n l
          (R.realizableCarrierTranslation hInvariant n k F) := by
  rw [eq_carrier_norm_sq_sub, eq_carrier_norm_sq_sub,
    eq_carrier_norm_sq_sub]
  rw [R.realizableCarrierTranslation_add hInvariant n k l F]
  ring

/-- Any explicit one-step norm contraction immediately becomes a lower bound on
the realizable reflected-integral defect.  The square on `q` is essential:
`I_n` is a squared OS norm. -/
theorem oneStep_lower_bound_of_norm_le
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier)
    (q : ℝ) (hq : 0 ≤ q)
    (hnorm : ‖R.realizableCarrierTranslation hInvariant n 1 F‖ ≤ q * ‖F‖) :
    (1 - q ^ 2) *
        physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F ≤
      physicalYangMillsEvenPeriodicWilsonOSRealizableFiniteReflectedIntegralDefect
        S D halfExtent N hN beta hbeta Q E R hInvariant n 1 F := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have hI :
      physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F =
        ‖F‖ ^ 2 := by
    rw [← physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F,
        Pn.osQuadraticValue_eq_norm_sq]
  rw [hI, eq_carrier_norm_sq_sub]
  nlinarith [norm_nonneg F,
    norm_nonneg (R.realizableCarrierTranslation hInvariant n 1 F)]

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableFiniteReflectedIntegralDefect

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryMomentDefect

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

/-- The realizable pointwise boundary defect integrand is integrable. -/
theorem integrand_integrable
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    Integrable
      (physicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryMomentDefectIntegrand
        S D halfExtent N hN beta hbeta Q E R hInvariant n k F)
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
  unfold physicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryMomentDefectIntegrand
  exact
    (PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentDefect.boundaryMoment_norm_sq_integrable
      (B := Q.toWeakStarBridge) n F).sub
      (PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentDefect.boundaryMoment_norm_sq_integrable
        (B := Q.toWeakStarBridge) n
        (R.realizableCarrierTranslation hInvariant n k F))

/-- The realizable finite reflected-integral defect is exactly the corresponding
single shared-boundary Haar integral. -/
theorem finiteReflectedIntegralDefect_eq_boundaryMomentDefect
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSRealizableFiniteReflectedIntegralDefect
        S D halfExtent N hN beta hbeta Q E R hInvariant n k F =
      physicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryMomentDefect
        S D halfExtent N hN beta hbeta Q E R hInvariant n k F := by
  let Fk := R.realizableCarrierTranslation hInvariant n k F
  have hFgram : ∀ b, Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        (halfExtent n) N hN (beta n) (hbeta n)
        (fun x =>
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F x)
        b)
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N) :=
    fun b =>
      PhysicalYangMillsEvenPeriodicWilsonOSActualAdjointSynthesisBoundaryTransferGapCertificate.gram_integrable
        (S := S) (D := D) (halfExtent := halfExtent) (N := N)
        (hN := hN) (beta := beta) (hbeta := hbeta) (B := Q.toWeakStarBridge)
        (hInvariant := hInvariant) n F b
  have hFkgram : ∀ b, Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        (halfExtent n) N hN (beta n) (hbeta n)
        (fun x =>
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fk x)
        b)
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N) :=
    fun b =>
      PhysicalYangMillsEvenPeriodicWilsonOSActualAdjointSynthesisBoundaryTransferGapCertificate.gram_integrable
        (S := S) (D := D) (halfExtent := halfExtent) (N := N)
        (hN := hN) (beta := beta) (hbeta := hbeta) (B := Q.toWeakStarBridge)
        (hInvariant := hInvariant) n Fk b
  have hFint :=
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentDefect.boundaryMoment_norm_sq_integrable
      (B := Q.toWeakStarBridge) n F
  have hFkint :=
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentDefect.boundaryMoment_norm_sq_integrable
      (B := Q.toWeakStarBridge) n Fk
  change
    physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F -
      physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fk =
      ∫ b,
        (‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F b‖ ^ 2 -
          ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fk b‖ ^ 2)
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)
  rw [physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F hFgram,
      physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fk hFkgram]
  exact (integral_sub hFint hFkint).symm

/-- The shared-boundary realizable defect inherits the exact integer-step
cocycle law. -/
theorem add
    (n k l : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryMomentDefect
        S D halfExtent N hN beta hbeta Q E R hInvariant n (k + l) F =
      physicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryMomentDefect
          S D halfExtent N hN beta hbeta Q E R hInvariant n k F +
        physicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryMomentDefect
          S D halfExtent N hN beta hbeta Q E R hInvariant n l
          (R.realizableCarrierTranslation hInvariant n k F) := by
  rw [← finiteReflectedIntegralDefect_eq_boundaryMomentDefect,
      ← finiteReflectedIntegralDefect_eq_boundaryMomentDefect,
      ← finiteReflectedIntegralDefect_eq_boundaryMomentDefect]
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableFiniteReflectedIntegralDefect.add
      n k l F

/-- A one-step norm estimate can be read equivalently as a lower bound on the
explicit shared-boundary defect integral. -/
theorem oneStep_lower_bound_of_norm_le
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier)
    (q : ℝ) (hq : 0 ≤ q)
    (hnorm : ‖R.realizableCarrierTranslation hInvariant n 1 F‖ ≤ q * ‖F‖) :
    (1 - q ^ 2) *
        physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F ≤
      physicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryMomentDefect
        S D halfExtent N hN beta hbeta Q E R hInvariant n 1 F := by
  rw [← finiteReflectedIntegralDefect_eq_boundaryMomentDefect]
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableFiniteReflectedIntegralDefect.oneStep_lower_bound_of_norm_le
      n F q hq hnorm

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryMomentDefect

end MathlibAnalytic
end MGAP4D

end
