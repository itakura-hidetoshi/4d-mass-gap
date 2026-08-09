import MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableOneStepDerivedRateGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsDerivedDiscreteTransferRate
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance realizablePositiveHalfBoundedFactorSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizablePositiveHalfBoundedFactorSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizablePositiveHalfBoundedFactorSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizablePositiveHalfBoundedFactorSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizablePositiveHalfBoundedFactorSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizablePositiveHalfBoundedFactorSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A bounded realization of the *actual integer one-step* positive-half Wilson
analysis.

At scale `n` the underlying linear map is not arbitrary: it is definitionally

`F ↦ positiveHalfL2 (T_{n,1} F)`,

where `T_{n,1}` is the realizable one-lattice-step positive-time translation.
The only analytic input is that this already-constructed linear map extends to a
bounded linear operator. No contraction factor or mass value is supplied. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
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
  analysis :
    (n : ℕ) →
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier →L[ℝ]
        PhysicalYangMillsEvenPeriodicWilsonOSOpenHalfFeatureL2 halfExtent N n
  analysis_apply :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      analysis n F =
        Q.positiveHalfL2LinearMap hInvariant n
          (R.realizableCarrierTranslation hInvariant n 1 F)

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

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

/-- Actual Wilson adjoint synthesis of the bounded integer-step analysis is
exactly the canonical boundary realization of the translated OS carrier.

This is theorem-generated from the existing identity
`boundaryMoment = actualSynthesis (positiveHalfL2)`; no transfer intertwining is
postulated. -/
theorem actualSynthesis_analysis_apply
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent N hN beta hbeta n
        (A.analysis n F) =
      Q.boundaryMomentLinearIsometry hInvariant n
        (R.realizableCarrierTranslation hInvariant n 1 F) := by
  rw [A.analysis_apply, Q.positiveHalfL2LinearMap_apply,
    Q.boundaryMomentLinearIsometry_apply]
  exact
    (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      (R.realizableCarrierTranslation hInvariant n 1 F)).symm

/-- The one-step factor is derived from the two actual bounded Wilson factors:
the canonical adjoint synthesis norm times the norm of the actual bounded
integer-step positive-half analysis. -/
def transferFactor
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) : ℝ :=
  ‖physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
      halfExtent N hN beta hbeta n‖ * ‖A.analysis n‖

/-- The theorem-generated factor is automatically nonnegative. -/
theorem transferFactor_nonneg
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    0 ≤ A.transferFactor n :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The actual integer one-step Wilson OS carrier norm is controlled by the
product of the two actual operator norms.

The boundary map `J_n` contributes no constant because it is a theorem-generated
linear isometry. -/
theorem oneStep_norm_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    ‖R.realizableCarrierTranslation hInvariant n 1 F‖ ≤
      A.transferFactor n * ‖F‖ := by
  let J := Q.boundaryMomentLinearIsometry hInvariant n
  let Syn := physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
    halfExtent N hN beta hbeta n
  have hfactor : Syn (A.analysis n F) =
      J (R.realizableCarrierTranslation hInvariant n 1 F) := by
    simpa [J, Syn] using A.actualSynthesis_analysis_apply n F
  calc
    ‖R.realizableCarrierTranslation hInvariant n 1 F‖ =
        ‖J (R.realizableCarrierTranslation hInvariant n 1 F)‖ := by
      symm
      exact J.norm_map _
    _ = ‖Syn (A.analysis n F)‖ := by rw [← hfactor]
    _ ≤ ‖Syn‖ * ‖A.analysis n F‖ := Syn.le_opNorm _
    _ ≤ ‖Syn‖ * (‖A.analysis n‖ * ‖F‖) := by
      exact mul_le_mul_of_nonneg_left ((A.analysis n).le_opNorm F) (norm_nonneg Syn)
    _ = A.transferFactor n * ‖F‖ := by
      simp only [transferFactor]
      ring

/-- Therefore the actual bounded positive-half factorization canonically
produces the finite one-step certificate consumed by the genuine integer-time
iteration spine. -/
noncomputable def toRealizableOneStepGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant A.transferFactor where
  transferFactor_nonneg := A.transferFactor_nonneg
  oneStep_centered_norm_le := by
    intro n F
    dsimp only
    exact A.oneStep_norm_le n
      ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuumCenteredCarrier F)

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

/-- Positive continuum-rate data attached to the factor which is *already
derived from actual Wilson bounded operators*.

The remaining quantitative Yang--Mills content is exactly strict contraction
and a positive logarithmic scaling limit for these theorem-generated factors. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfDerivedRateCertificate
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
  boundedAnalysis :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant
  transferFactor_pos : ∀ n, 0 < boundedAnalysis.transferFactor n
  transferFactor_le_one : ∀ n, boundedAnalysis.transferFactor n ≤ 1
  mass : ℝ
  mass_pos : 0 < mass
  massRate_tendsto :
    Tendsto
      (fun n =>
        -Real.log (boundedAnalysis.transferFactor n) / S.latticeSpacing n)
      atTop (nhds mass)

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfDerivedRateCertificate

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

/-- Forget only the positive scaling-limit data and recover the genuine
integer-time one-step Wilson estimate with its derived factor. -/
noncomputable def toRealizableOneStepGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant
        A.boundedAnalysis.transferFactor :=
  A.boundedAnalysis.toRealizableOneStepGapCertificate

/-- Package the actual bounded-factor sequence into the generic discrete
logarithmic rate limit. -/
noncomputable def toPositiveDiscreteTransferRateLimit
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PositiveDiscreteTransferRateLimit
      S.latticeSpacing A.boundedAnalysis.transferFactor where
  latticeSpacing_pos := S.latticeSpacing_pos
  latticeSpacing_tendsto_zero := S.latticeSpacing_tendsto_zero
  transferFactor_pos := A.transferFactor_pos
  transferFactor_le_one := A.transferFactor_le_one
  mass := A.mass
  mass_pos := A.mass_pos
  massRate_tendsto := A.massRate_tendsto

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfDerivedRateCertificate

end MathlibAnalytic
end MGAP4D

end