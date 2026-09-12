import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalExcitationDirichletScalingRate
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance physicalExcitationDirichletScaling3320SideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance physicalExcitationDirichletScaling3320SpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalExcitationDirichletScaling3320SpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalExcitationDirichletScaling3320SpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalExcitationDirichletScaling3320SpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalExcitationDirichletScaling3320SpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Exact quantitative Wilson input for the normalized `33/20` mass route.

The mass is not a field of this certificate.  The only exact numerical input is
the first-order slope of the *actual* completed physical-excitation Dirichlet
defect

`delta_n = 1 - ||T_n^exc||^2`,

namely

`delta_n / a_n -> 33/10`.

Because `delta_n = 1-r_n^2`, #1521 and #1522 then force the logarithmic
one-step mass rate to converge to exactly half that slope, `33/20`. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScaling3320Certificate
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
  defect_nonneg : ∀ n,
    0 ≤ boundedAnalysis.physicalExcitationDirichletCoefficient n
  defect_lt_one : ∀ n,
    boundedAnalysis.physicalExcitationDirichletCoefficient n < 1
  defectRate_tendsto :
    Tendsto
      (fun n =>
        boundedAnalysis.physicalExcitationDirichletCoefficient n /
          S.latticeSpacing n)
      atTop (nhds ((33 : ℝ) / 10))

namespace PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScaling3320Certificate

set_option maxHeartbeats 800000

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

/-- The exact Dirichlet slope is twice the normalized exact mass. -/
theorem exactDirichletSlope3320_eq_two_mul_exactMass3320 :
    (33 : ℝ) / 10 = 2 * ((33 : ℝ) / 20) := by
  norm_num

/-- Convert the exact-slope certificate to #1522's mass-free-generated-rate
package.  The generic mass field is filled by `33/20`, while its required
Dirichlet limit follows from the supplied `33/10` slope by exact arithmetic. -/
noncomputable def toPhysicalExcitationDirichletScalingCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScaling3320Certificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScalingCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  boundedAnalysis := A.boundedAnalysis
  defect_nonneg := A.defect_nonneg
  defect_lt_one := A.defect_lt_one
  mass := (33 : ℝ) / 20
  mass_pos := by norm_num
  defectRate_tendsto := by
    have hmass : (2 : ℝ) * ((33 : ℝ) / 20) = (33 : ℝ) / 10 := by
      norm_num
    simpa only [hmass] using A.defectRate_tendsto

/-- The exact route therefore produces a strictly positive actual centered
one-step norm at every finite scale. -/
theorem centeredTransferFactor_pos
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScaling3320Certificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    0 < A.boundedAnalysis.centeredTransferFactor n :=
  A.toPhysicalExcitationDirichletScalingCertificate.centeredTransferFactor_pos n

/-- The exact route also produces the unit upper bound on the actual centered
one-step norm from nonnegativity of the Wilson Dirichlet defect. -/
theorem centeredTransferFactor_le_one
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScaling3320Certificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.boundedAnalysis.centeredTransferFactor n ≤ 1 :=
  A.toPhysicalExcitationDirichletScalingCertificate.centeredTransferFactor_le_one n

/-- Exact `33/20` logarithmic mass-rate convergence for the actual centered
finite Wilson one-step operator.  No logarithmic rate is assumed in the exact
certificate. -/
theorem centeredMassRate_tendsto_33_over_20
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScaling3320Certificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    Tendsto
      (fun n =>
        -Real.log (A.boundedAnalysis.centeredTransferFactor n) /
          S.latticeSpacing n)
      atTop (nhds ((33 : ℝ) / 20)) := by
  exact A.toPhysicalExcitationDirichletScalingCertificate.centeredMassRate_tendsto

/-- The same exact rate written directly with the completed physical-excitation
operator norm. -/
theorem physicalExcitationMassRate_tendsto_33_over_20
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScaling3320Certificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    Tendsto
      (fun n =>
        -Real.log ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ /
          S.latticeSpacing n)
      atTop (nhds ((33 : ℝ) / 20)) := by
  simpa only [A.boundedAnalysis.physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor] using
    A.centeredMassRate_tendsto_33_over_20

/-- Repackage the exact Dirichlet-slope route as the existing centered
operator-derived-rate certificate.  Its mass is definitionally `33/20`; no free
mass parameter remains on this exact route. -/
noncomputable def toCenteredOneStepOperatorDerivedRateCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScaling3320Certificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant :=
  A.toPhysicalExcitationDirichletScalingCertificate.toCenteredOneStepOperatorDerivedRateCertificate

@[simp] theorem toCenteredOneStepOperatorDerivedRateCertificate_mass
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScaling3320Certificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    A.toCenteredOneStepOperatorDerivedRateCertificate.mass = (33 : ℝ) / 20 :=
  rfl

/-- The genuine integer/floor-time completed physical-excitation trajectory has
exact continuum decay `exp(-(33/20)t)`.  This is generated from the actual
Dirichlet slope, not supplied as a decay assumption. -/
theorem floorPhysicalExcitationOpNormPow_tendsto_33_over_20
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScaling3320Certificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (t : NNReal) :
    Tendsto
      (fun n =>
        ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ ^
          physicalTemporalFloorNatStep S.latticeSpacing t n)
      atTop
      (nhds (Real.exp (-((33 : ℝ) / 20) * (t : ℝ)))) := by
  exact
    A.toPhysicalExcitationDirichletScalingCertificate.floorPhysicalExcitationOpNormPow_tendsto t

end PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScaling3320Certificate

end MathlibAnalytic
end MGAP4D

end