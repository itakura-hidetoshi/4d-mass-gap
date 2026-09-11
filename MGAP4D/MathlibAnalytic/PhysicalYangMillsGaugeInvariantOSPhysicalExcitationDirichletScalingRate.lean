import MGAP4D.MathlibAnalytic.DirichletDefectScalingToDiscreteTransferRate
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalExcitationBoundaryDirichletCoefficient
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableCenteredPhysicalExcitationFloorDecay
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance physicalExcitationDirichletScalingSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance physicalExcitationDirichletScalingSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalExcitationDirichletScalingSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalExcitationDirichletScalingSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalExcitationDirichletScalingSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalExcitationDirichletScalingSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The remaining quantitative Wilson input after #1517 and #1521.

At each lattice scale the Dirichlet defect is not a free number: it is the
squared operator-norm defect of the actual completed finite physical excitation
transfer

`delta_n = 1 - ||T_n^exc||^2`.

This certificate asks only that those theorem-generated coefficients lie in
`[0,1)` and have the physical first-order scaling

`delta_n / a_n -> 2 m`

for some positive continuum mass `m`.

Crucially, logarithmic transfer-rate convergence is *not* a field here; #1521
generates it from this Dirichlet scaling.  No exact numerical mass value is
assumed. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScalingCertificate
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
  mass : ℝ
  mass_pos : 0 < mass
  defectRate_tendsto :
    Tendsto
      (fun n =>
        boundedAnalysis.physicalExcitationDirichletCoefficient n /
          S.latticeSpacing n)
      atTop (nhds (2 * mass))

namespace PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScalingCertificate

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

/-- Forget the Wilson origin of the coefficient and obtain #1521's generic
positive Dirichlet-defect scaling package. -/
noncomputable def toPositiveDirichletDefectScaling
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScalingCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PositiveDirichletDefectScaling
      S.latticeSpacing A.boundedAnalysis.physicalExcitationDirichletCoefficient where
  latticeSpacing_pos := S.latticeSpacing_pos
  latticeSpacing_tendsto_zero := S.latticeSpacing_tendsto_zero
  defect_nonneg := A.defect_nonneg
  defect_lt_one := A.defect_lt_one
  mass := A.mass
  mass_pos := A.mass_pos
  defectRate_tendsto := A.defectRate_tendsto

/-- For the actual Wilson defect, #1521's square-root transfer factor is exactly
the operator norm of the centered/physical one-step transfer:

`sqrt (1 - (1 - r_n^2)) = r_n`.

Thus the generic defect route introduces no auxiliary finite contraction
factor. -/
@[simp] theorem defectTransferFactor_eq_centeredTransferFactor
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScalingCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.toPositiveDirichletDefectScaling.transferFactor n =
      A.boundedAnalysis.centeredTransferFactor n := by
  unfold PositiveDirichletDefectScaling.transferFactor
  rw [A.boundedAnalysis.physicalExcitationDirichletCoefficient_eq_centeredTransferFactor]
  rw [show
      1 - (1 - (A.boundedAnalysis.centeredTransferFactor n) ^ 2) =
        (A.boundedAnalysis.centeredTransferFactor n) ^ 2 by ring]
  rw [Real.sqrt_sq_eq_abs,
    abs_of_nonneg (A.boundedAnalysis.centeredTransferFactor_nonneg n)]

/-- The same defect-derived factor is exactly the norm of the completed finite
physical excitation operator. -/
@[simp] theorem defectTransferFactor_eq_physicalExcitationOpNorm
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScalingCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.toPositiveDirichletDefectScaling.transferFactor n =
      ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ := by
  rw [A.defectTransferFactor_eq_centeredTransferFactor,
    A.boundedAnalysis.physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor]

/-- The defect hypotheses generate strict positivity of every actual finite
centered transfer factor.  This is not a separate rate assumption. -/
theorem centeredTransferFactor_pos
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScalingCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    0 < A.boundedAnalysis.centeredTransferFactor n := by
  rw [← A.defectTransferFactor_eq_centeredTransferFactor n]
  exact A.toPositiveDirichletDefectScaling.transferFactor_pos n

/-- Nonnegativity of the physical Dirichlet defect generates the unit upper
bound on the actual finite centered transfer norm. -/
theorem centeredTransferFactor_le_one
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScalingCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.boundedAnalysis.centeredTransferFactor n ≤ 1 := by
  rw [← A.defectTransferFactor_eq_centeredTransferFactor n]
  exact A.toPositiveDirichletDefectScaling.transferFactor_le_one n

/-- The logarithmic mass rate of the actual finite completed excitation
operators converges to the mass selected by the first-order Wilson Dirichlet
scaling.  This theorem is generated by #1521's squeeze argument. -/
theorem centeredMassRate_tendsto
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScalingCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    Tendsto
      (fun n =>
        -Real.log (A.boundedAnalysis.centeredTransferFactor n) /
          S.latticeSpacing n)
      atTop (nhds A.mass) := by
  have h := A.toPositiveDirichletDefectScaling.massRate_tendsto_mass
  change
    Tendsto
      (fun n =>
        -Real.log (A.toPositiveDirichletDefectScaling.transferFactor n) /
          S.latticeSpacing n)
      atTop (nhds A.mass) at h
  simpa only [A.defectTransferFactor_eq_centeredTransferFactor] using h

/-- Repackage the actual Wilson Dirichlet scaling as the existing centered
one-step derived-rate certificate.  Its `massRate_tendsto` field is now a
conclusion, not an independent assumption. -/
noncomputable def toCenteredOneStepOperatorDerivedRateCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScalingCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  boundedAnalysis := A.boundedAnalysis
  transferFactor_pos := A.centeredTransferFactor_pos
  transferFactor_le_one := A.centeredTransferFactor_le_one
  mass := A.mass
  mass_pos := A.mass_pos
  massRate_tendsto := A.centeredMassRate_tendsto

/-- Consequently the genuine integer/floor-time finite physical excitation
trajectory inherits the continuum exponential rate generated solely from the
actual Wilson Dirichlet-coefficient scaling. -/
theorem floorPhysicalExcitationOpNormPow_tendsto
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScalingCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (t : NNReal) :
    Tendsto
      (fun n =>
        ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ ^
          physicalTemporalFloorNatStep S.latticeSpacing t n)
      atTop
      (nhds (Real.exp (-A.mass * (t : ℝ)))) :=
  A.toCenteredOneStepOperatorDerivedRateCertificate.floorPhysicalExcitationOpNormPow_tendsto t

end PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletScalingCertificate

end MathlibAnalytic
end MGAP4D

end