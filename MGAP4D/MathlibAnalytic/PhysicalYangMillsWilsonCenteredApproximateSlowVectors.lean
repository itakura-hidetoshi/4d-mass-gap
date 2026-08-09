import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableCenteredPhysicalExcitationOperator
import Mathlib.Tactic

noncomputable section

open Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- A continuous linear operator has a vector beating every nonnegative strict
lower threshold for its operator norm.

This is the generic approximation principle needed for finite Wilson slow
modes.  It uses only Mathlib's `ContinuousLinearMap.opNorm_le_bound`; no
finite-dimensionality or norm-attaining eigenvector is assumed. -/
theorem continuousLinearMap_exists_apply_norm_gt_mul_norm_of_lt_opNorm
    {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) {r : ℝ}
    (hr_nonneg : 0 ≤ r) (hr_lt : r < ‖T‖) :
    ∃ x : E, r * ‖x‖ < ‖T x‖ := by
  by_contra h
  push_neg at h
  have hop : ‖T‖ ≤ r := T.opNorm_le_bound hr_nonneg h
  exact (not_le_of_gt hr_lt) hop

/-- The strict operator-norm approximation witness is automatically nonzero. -/
theorem continuousLinearMap_exists_nonzero_apply_norm_gt_mul_norm_of_lt_opNorm
    {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) {r : ℝ}
    (hr_nonneg : 0 ≤ r) (hr_lt : r < ‖T‖) :
    ∃ x : E, x ≠ 0 ∧ r * ‖x‖ < ‖T x‖ := by
  rcases continuousLinearMap_exists_apply_norm_gt_mul_norm_of_lt_opNorm
      T hr_nonneg hr_lt with ⟨x, hx⟩
  refine ⟨x, ?_, hx⟩
  intro hzero
  subst x
  simpa using hx

local instance approximateSlowSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance approximateSlowSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance approximateSlowSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance approximateSlowSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance approximateSlowSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance approximateSlowSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

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

/-- For every finite scale and every factor `theta` strictly between zero and
one, the **completed finite physical excitation operator** has a nonzero slow
state beating `theta` times its exact operator norm.

The exact identity

`‖T_n^phys,exc‖ = centeredTransferFactor n`

is supplied by the already integrated dense-isometric completion theorem.
Consequently no centered-carrier quotient inversion, finite-dimensionality,
eigenvector existence, logarithmic rate, continuum mass, or target exact value
enters this finite-side result. -/
theorem exists_physicalExcitationApproximateSlowVector
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) {theta : ℝ} (htheta_pos : 0 < theta) (htheta_lt_one : theta < 1) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    ∃ psi : Pn.VacuumOrthogonalHilbert,
      psi ≠ 0 ∧
      (A.centeredTransferFactor n * theta) * ‖psi‖ <
        ‖A.physicalExcitationOneStepOperator n psi‖ := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let Tn : Pn.VacuumOrthogonalHilbert →L[ℝ] Pn.VacuumOrthogonalHilbert :=
    A.physicalExcitationOneStepOperator n
  let r : ℝ := A.centeredTransferFactor n * theta
  have hfactor_nonneg : 0 ≤ A.centeredTransferFactor n := by
    rw [← A.physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor n]
    exact norm_nonneg _
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr_lt_factor : r < A.centeredTransferFactor n := by
    dsimp [r]
    have hfactor_pos : 0 < A.centeredTransferFactor n := by
      by_contra h
      have hfactor_zero : A.centeredTransferFactor n = 0 :=
        le_antisymm (le_of_not_gt h) hfactor_nonneg
      rw [hfactor_zero] at htheta_pos htheta_lt_one
      linarith
    nlinarith
  have hr_lt : r < ‖Tn‖ := by
    dsimp [Tn]
    rw [A.physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor]
    exact hr_lt_factor
  rcases continuousLinearMap_exists_nonzero_apply_norm_gt_mul_norm_of_lt_opNorm
      Tn hr_nonneg hr_lt with ⟨psi, hpsi, hslow⟩
  exact ⟨psi, hpsi, hslow⟩

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

end MathlibAnalytic
end MGAP4D

end