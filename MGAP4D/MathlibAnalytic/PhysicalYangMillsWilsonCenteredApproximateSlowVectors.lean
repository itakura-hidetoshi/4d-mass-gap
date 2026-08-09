import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableCenteredOneStepOperatorRate
import Mathlib.Tactic

noncomputable section

open Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- A continuous linear operator has a vector beating every nonnegative strict
lower threshold for its operator norm.

This is the approximation principle needed for finite Wilson slow modes. It
uses only Mathlib's characterization of the operator norm as the least uniform
bound; no finite-dimensionality or norm-attaining eigenvector is assumed. -/
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

/-- The approximate operator-norm vector supplied above is automatically
nonzero. -/
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

/-- For every finite lattice scale with positive centered transfer factor and
every strictly positive rate excess `eps`, the actual centered Wilson one-step
operator has a nonzero vector beating the strict threshold

`centeredTransferFactor n * exp (-eps * latticeSpacing n)`.

Since `centeredTransferFactor n` is definitionally the actual centered operator
norm, finite slow-mode existence is automatic from generic operator-norm
approximation.  No logarithmic-rate definition, convergence package, continuum
mass, finite-dimensionality, or exact target value enters this theorem. -/
theorem exists_centeredApproximateSlowVector
    (B : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) (hfactor : 0 < B.centeredTransferFactor n)
    {eps : ℝ} (heps : 0 < eps) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    ∃ F : Pn.CenteredCarrier,
      F ≠ 0 ∧
      (B.centeredTransferFactor n *
          Real.exp (-eps * S.latticeSpacing n)) * ‖F‖ <
        ‖B.centeredOneStepOperator n F‖ := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let Tn : Pn.CenteredCarrier →L[ℝ] Pn.CenteredCarrier :=
    B.centeredOneStepOperator n
  let r : ℝ :=
    B.centeredTransferFactor n * Real.exp (-eps * S.latticeSpacing n)
  have ha : 0 < S.latticeSpacing n := S.latticeSpacing_pos n
  have hepsa : 0 < eps * S.latticeSpacing n := mul_pos heps ha
  have hexp_pos : 0 < Real.exp (-eps * S.latticeSpacing n) := Real.exp_pos _
  have hexp_lt_one : Real.exp (-eps * S.latticeSpacing n) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hr_lt_factor : r < B.centeredTransferFactor n := by
    dsimp [r]
    nlinarith
  have hr_lt : r < ‖Tn‖ := by
    dsimp [Tn]
    change r < B.centeredTransferFactor n
    exact hr_lt_factor
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  rcases continuousLinearMap_exists_nonzero_apply_norm_gt_mul_norm_of_lt_opNorm
      Tn hr_nonneg hr_lt with ⟨F, hF, hslow⟩
  exact ⟨F, hF, hslow⟩

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

end MathlibAnalytic
end MGAP4D

end