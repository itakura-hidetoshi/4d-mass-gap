import MGAP4D.MathlibAnalytic.DirichletDefectLowerBoundToExponentialTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalExcitationDirichletScalingRate
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance physicalExcitationDirichletLowerSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance physicalExcitationDirichletLowerSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalExcitationDirichletLowerSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalExcitationDirichletLowerSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalExcitationDirichletLowerSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalExcitationDirichletLowerSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Mass-gap lower-bound data stated directly for the actual finite Wilson
physical excitation operator.

The coefficient is fixed by #1517:

`delta_n = 1 - ||T_n^exc||^2`.

For proving positivity of the continuum mass gap it is enough to assume an
eventual one-sided bound

`2 m a_n <= delta_n`

with `m > 0`.  No exact defect limit and no exact mass value are included. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletLowerBoundCertificate
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
  eventually_defect_lower :
    ∀ᶠ n in atTop,
      2 * mass * S.latticeSpacing n ≤
        boundedAnalysis.physicalExcitationDirichletCoefficient n

namespace PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletLowerBoundCertificate

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

/-- Forget the Wilson origin of the coefficient and obtain the generic one-sided
Dirichlet-defect lower-bound package. -/
noncomputable def toPositiveDirichletDefectLowerBound
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PositiveDirichletDefectLowerBound
      S.latticeSpacing A.boundedAnalysis.physicalExcitationDirichletCoefficient where
  latticeSpacing_pos := S.latticeSpacing_pos
  latticeSpacing_tendsto_zero := S.latticeSpacing_tendsto_zero
  defect_nonneg := A.defect_nonneg
  defect_lt_one := A.defect_lt_one
  mass := A.mass
  mass_pos := A.mass_pos
  eventually_defect_lower := A.eventually_defect_lower

/-- The generic defect-derived transfer factor is exactly the norm of the actual
completed finite physical excitation operator. -/
@[simp] theorem defectTransferFactor_eq_physicalExcitationOpNorm
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.toPositiveDirichletDefectLowerBound.transferFactor n =
      ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ := by
  unfold PositiveDirichletDefectLowerBound.transferFactor
  unfold PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis.physicalExcitationDirichletCoefficient
  rw [show
      1 - (1 - ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ ^ 2) =
        ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ ^ 2 by ring]
  rw [Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg (A.boundedAnalysis.physicalExcitationOneStepOperator n))]

/-- The actual completed one-step physical excitation operator eventually has
the exponential norm bound generated by the Wilson Dirichlet lower bound. -/
theorem eventually_physicalExcitationOpNorm_le_exp
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    ∀ᶠ n in atTop,
      ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ ≤
        Real.exp (-A.mass * S.latticeSpacing n) := by
  filter_upwards [
    A.toPositiveDirichletDefectLowerBound.eventually_transferFactor_le_exp_neg_mass_mul]
      with n hn
  simpa only [A.defectTransferFactor_eq_physicalExcitationOpNorm] using hn

/-- At all sufficiently fine lattice scales, arbitrary finite excitation states
satisfy the exact one-step exponential norm contraction. -/
theorem eventually_physicalExcitationOneStep_norm_le_exp
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    ∀ᶠ n in atTop,
      ∀ psi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert,
        ‖A.boundedAnalysis.physicalExcitationOneStepOperator n psi‖ ≤
          Real.exp (-A.mass * S.latticeSpacing n) * ‖psi‖ := by
  filter_upwards [A.eventually_physicalExcitationOpNorm_le_exp] with n hn
  intro psi
  calc
    ‖A.boundedAnalysis.physicalExcitationOneStepOperator n psi‖ ≤
        ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ * ‖psi‖ :=
      (A.boundedAnalysis.physicalExcitationOneStepOperator n).le_opNorm psi
    _ ≤ Real.exp (-A.mass * S.latticeSpacing n) * ‖psi‖ :=
      mul_le_mul_of_nonneg_right hn (norm_nonneg psi)

/-- The one-step bound iterates along the genuine floor-selected integer Wilson
time trajectory on the actual finite physical excitation Hilbert spaces. -/
theorem eventually_floorPhysicalExcitationIterate_norm_le_exponential
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (t : NNReal)
    (psi : (n : ℕ) →
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert) :
    ∀ᶠ n in atTop,
      ‖(fun phi :
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert =>
          A.boundedAnalysis.physicalExcitationOneStepOperator n phi)^[
            physicalTemporalFloorNatStep S.latticeSpacing t n] (psi n)‖ ≤
        Real.exp
            (-A.mass *
              ((physicalTemporalFloorNatStep S.latticeSpacing t n : ℝ) *
                S.latticeSpacing n)) *
          ‖psi n‖ := by
  filter_upwards [A.eventually_physicalExcitationOneStep_norm_le_exp] with n hn
  let k := physicalTemporalFloorNatStep S.latticeSpacing t n
  have hiter := norm_iterate_le_exp_pow_of_norm_le
    (fun phi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert =>
      A.boundedAnalysis.physicalExcitationOneStepOperator n phi)
    A.mass (S.latticeSpacing n) hn k (psi n)
  calc
    ‖(fun phi :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert =>
        A.boundedAnalysis.physicalExcitationOneStepOperator n phi)^[k] (psi n)‖ ≤
        (Real.exp (-A.mass * S.latticeSpacing n)) ^ k * ‖psi n‖ := hiter
    _ = Real.exp (-A.mass * ((k : ℝ) * S.latticeSpacing n)) * ‖psi n‖ := by
      rw [PositiveDirichletDefectLowerBound.exp_neg_mass_spacing_pow]

/-- Scalar continuum handoff for the lower-bound route.  Whenever the input and
floor-evolved finite excitation norms have limits, the limiting evolved norm is
bounded by `exp(-m t)` times the limiting input norm.  Exact mass-rate
convergence is not required. -/
theorem floorPhysicalExcitationIterate_limit_norm_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (t : NNReal)
    (psi : (n : ℕ) →
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert)
    {inputNormLimit evolvedNormLimit : ℝ}
    (hInput : Tendsto (fun n => ‖psi n‖) atTop (nhds inputNormLimit))
    (hEvolved :
      Tendsto
        (fun n =>
          ‖(fun phi :
              (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert =>
              A.boundedAnalysis.physicalExcitationOneStepOperator n phi)^[
                physicalTemporalFloorNatStep S.latticeSpacing t n] (psi n)‖)
        atTop (nhds evolvedNormLimit)) :
    evolvedNormLimit ≤
      Real.exp (-A.mass * (t : ℝ)) * inputNormLimit := by
  apply le_of_tendsto_of_tendsto hEvolved
    ((A.toPositiveDirichletDefectLowerBound.floorExponential_tendsto t).mul hInput)
  exact A.eventually_floorPhysicalExcitationIterate_norm_le_exponential t psi

end PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletLowerBoundCertificate

end MathlibAnalytic
end MGAP4D

end