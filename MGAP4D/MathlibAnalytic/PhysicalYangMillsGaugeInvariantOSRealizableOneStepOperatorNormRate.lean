import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizablePositiveHalfBoundedOneStepFactor
import MGAP4D.MathlibAnalytic.PhysicalYangMillsDerivedDiscreteTransferRate
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableOneStepOperatorNormRateSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableOneStepOperatorNormRateSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableOneStepOperatorNormRateSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableOneStepOperatorNormRateSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableOneStepOperatorNormRateSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableOneStepOperatorNormRateSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

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

/-- The actual integer one-step Wilson OS carrier translation promoted to a
bounded linear operator.

The underlying map is exactly `R.realizableCarrierTranslation ... n 1`.
Continuity is theorem-generated from the operator-product estimate proved in the
preceding layer; no new transfer map is introduced. -/
noncomputable def oneStepOperator
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier →L[ℝ]
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier :=
  (R.realizableCarrierTranslation hInvariant n 1).mkContinuous
    (A.transferFactor n) (A.oneStep_norm_le n)

@[simp] theorem oneStepOperator_apply
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    A.oneStepOperator n F =
      R.realizableCarrierTranslation hInvariant n 1 F :=
  rfl

/-- The canonical finite transfer factor is the operator norm of the actual
integer one-step Wilson translation itself.

This is the quantity whose logarithmic lattice-spacing rate is physically
natural. It is not a separately supplied number and it is not merely a product
upper bound from an auxiliary factorization. -/
def operatorTransferFactor
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) : ℝ :=
  ‖A.oneStepOperator n‖

/-- The actual one-step operator norm is nonnegative. -/
theorem operatorTransferFactor_nonneg
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    0 ≤ A.operatorTransferFactor n :=
  norm_nonneg _

/-- The actual one-step operator norm is bounded by the previously derived
adjoint-synthesis/positive-half product bound.

Thus the product factor remains a useful certificate, but the physical rate is
now attached to the smaller, intrinsic operator norm. -/
theorem operatorTransferFactor_le_transferFactor
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.operatorTransferFactor n ≤ A.transferFactor n := by
  apply ContinuousLinearMap.opNorm_le_bound
    (A.oneStepOperator n) (A.transferFactor_nonneg n)
  intro F
  simpa only [oneStepOperator_apply] using A.oneStep_norm_le n F

/-- Any unit upper bound on the factorization estimate automatically gives the
same unit bound for the intrinsic one-step operator norm. -/
theorem operatorTransferFactor_le_one
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (hFactor : ∀ n, A.transferFactor n ≤ 1)
    (n : ℕ) :
    A.operatorTransferFactor n ≤ 1 :=
  (A.operatorTransferFactor_le_transferFactor n).trans (hFactor n)

/-- The realizable one-step gap certificate can therefore be stated with the
intrinsic operator norm `‖T_{n,1}‖` itself. -/
noncomputable def toOperatorNormRealizableOneStepGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant A.operatorTransferFactor where
  transferFactor_nonneg := A.operatorTransferFactor_nonneg
  oneStep_centered_norm_le := by
    intro n F
    dsimp only
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    have h := (A.oneStepOperator n).le_opNorm (Pn.vacuumCenteredCarrier F)
    simpa only [oneStepOperator_apply, operatorTransferFactor] using h

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

/-- Positive continuum-rate data for the *intrinsic* actual integer one-step
Wilson operator norms.

The finite number entering the logarithm is now definitionally

`rₙ = ‖T_{n,1}‖`.

The remaining Yang--Mills content is exactly strict positivity/nonexpansiveness
of these actual operator norms and convergence of their logarithmic rates to a
positive continuum mass. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepOperatorNormDerivedRateCertificate
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
  transferFactor_pos : ∀ n, 0 < boundedAnalysis.operatorTransferFactor n
  transferFactor_le_one : ∀ n, boundedAnalysis.operatorTransferFactor n ≤ 1
  mass : ℝ
  mass_pos : 0 < mass
  massRate_tendsto :
    Tendsto
      (fun n =>
        -Real.log (boundedAnalysis.operatorTransferFactor n) / S.latticeSpacing n)
      atTop (nhds mass)

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepOperatorNormDerivedRateCertificate

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

/-- The intrinsic actual-operator norm supplies the genuine integer-time
one-step Wilson gap certificate. -/
noncomputable def toRealizableOneStepGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepOperatorNormDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant
        A.boundedAnalysis.operatorTransferFactor :=
  A.boundedAnalysis.toOperatorNormRealizableOneStepGapCertificate

/-- Package the intrinsic actual one-step operator-norm sequence into the
generic positive discrete logarithmic-rate limit. -/
noncomputable def toPositiveDiscreteTransferRateLimit
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepOperatorNormDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PositiveDiscreteTransferRateLimit
      S.latticeSpacing A.boundedAnalysis.operatorTransferFactor where
  latticeSpacing_pos := S.latticeSpacing_pos
  latticeSpacing_tendsto_zero := S.latticeSpacing_tendsto_zero
  transferFactor_pos := A.transferFactor_pos
  transferFactor_le_one := A.transferFactor_le_one
  mass := A.mass
  mass_pos := A.mass_pos
  massRate_tendsto := A.massRate_tendsto

/-- The finite physical mass rate is literally the logarithmic rate of the
actual integer one-step Wilson operator norm. -/
def massRate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepOperatorNormDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) : ℝ :=
  -Real.log (A.boundedAnalysis.operatorTransferFactor n) / S.latticeSpacing n

@[simp] theorem massRate_eq_actual_oneStep_opNorm
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepOperatorNormDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.massRate n =
      -Real.log ‖A.boundedAnalysis.oneStepOperator n‖ / S.latticeSpacing n :=
  rfl

/-- The intrinsic finite rates converge to the derived continuum mass. -/
theorem massRate_tendsto_mass
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepOperatorNormDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    Tendsto A.massRate atTop (nhds A.mass) := by
  simpa only [massRate] using A.massRate_tendsto

/-- For every fixed physical time, the floor-selected integer powers of the
actual one-step Wilson operator norm converge to the continuum exponential
with the mass derived from those norms. -/
theorem floorPow_tendsto
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepOperatorNormDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (t : NNReal) :
    Tendsto
      (fun n =>
        (A.boundedAnalysis.operatorTransferFactor n) ^
          physicalTemporalFloorNatStep S.latticeSpacing t n)
      atTop
      (nhds (Real.exp (-A.mass * (t : ℝ)))) := by
  exact A.toPositiveDiscreteTransferRateLimit.floorPow_tendsto t

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepOperatorNormDerivedRateCertificate

end MathlibAnalytic
end MGAP4D

end