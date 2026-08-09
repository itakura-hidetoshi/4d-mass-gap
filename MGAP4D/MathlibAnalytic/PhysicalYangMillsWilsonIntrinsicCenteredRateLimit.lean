import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableCenteredOneStepOperatorRate
import Mathlib.Tactic

noncomputable section

open Filter Topology

namespace MGAP4D
namespace MathlibAnalytic

/-- The intrinsic finite spectral-decay rate of the actual vacuum-centered
one-step Wilson transfer operator.

This is defined directly from the operator norm and the physical lattice
spacing.  No continuum mass value is supplied:

`g_n = -log ||T_n^centered|| / a_n`. -/
def physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
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
    (B : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) : ℝ :=
  -Real.log (B.centeredTransferFactor n) / S.latticeSpacing n

@[simp] theorem physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate_eq_opNorm
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
    (B : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate B n =
      -Real.log ‖B.centeredOneStepOperator n‖ / S.latticeSpacing n :=
  rfl

/-- Convergence data for the intrinsic centered Wilson rate sequence, with no
selected continuum mass field.

The only quantitative assumptions are the actual operator norm lying in
`(0,1]` and existence of a real limit of its logarithmic physical-time rate.
The limit value itself is reconstructed from the sequence. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
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
  transferFactor_pos : ∀ n, 0 < boundedAnalysis.centeredTransferFactor n
  transferFactor_le_one : ∀ n, boundedAnalysis.centeredTransferFactor n ≤ 1
  rate_converges :
    ∃ q : ℝ,
      Tendsto
        (physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate boundedAnalysis)
        atTop (nhds q)

namespace PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence

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

/-- The continuum centered Wilson rate is reconstructed as the unique limit of
the intrinsic finite operator-norm rate sequence.  No numerical value is an
input to this definition. -/
noncomputable def limit
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant) : ℝ :=
  Classical.choose C.rate_converges

/-- The reconstructed value is actually the limit of the intrinsic finite
Wilson rates. -/
theorem rate_tendsto_limit
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    Tendsto
      (physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate C.boundedAnalysis)
      atTop (nhds C.limit) :=
  Classical.choose_spec C.rate_converges

/-- Uniqueness: any independently proved limit of the actual finite Wilson rate
sequence equals the reconstructed intrinsic value. -/
theorem limit_eq_of_tendsto
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    {q : ℝ}
    (hq : Tendsto
      (physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate C.boundedAnalysis)
      atTop (nhds q)) :
    C.limit = q :=
  tendsto_nhds_unique C.rate_tendsto_limit hq

end PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate

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

/-- Every legacy derived-rate certificate canonically yields mass-free intrinsic
rate-convergence data.  Its `mass` field is not used to define the new limit;
it is only a witness that the intrinsic sequence converges. -/
noncomputable def toIntrinsicCenteredRateConvergence
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  boundedAnalysis := A.boundedAnalysis
  transferFactor_pos := A.transferFactor_pos
  transferFactor_le_one := A.transferFactor_le_one
  rate_converges := ⟨A.mass, by
    simpa [physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate]
      using A.massRate_tendsto⟩

/-- The old certificate-selected `mass` is theorem-equal to the limit derived
from the actual Wilson operator-norm sequence.  Thus it carries no independent
numerical information once convergence has been established. -/
theorem mass_eq_intrinsicCenteredRateLimit
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    A.mass = A.toIntrinsicCenteredRateConvergence.limit := by
  symm
  apply A.toIntrinsicCenteredRateConvergence.limit_eq_of_tendsto
  simpa [physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate]
    using A.massRate_tendsto

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate

end MathlibAnalytic
end MGAP4D

end