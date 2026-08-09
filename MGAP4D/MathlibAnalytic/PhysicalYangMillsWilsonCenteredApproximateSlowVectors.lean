import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonIntrinsicRateRayleighLimsupRecovery
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- A continuous linear operator has a vector beating every nonnegative strict
lower threshold for its operator norm.

This is the approximation principle needed for finite Wilson slow modes.  It
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
  have hop : ‖T‖ ≤ r :=
    T.opNorm_le_bound hr_nonneg h
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

namespace PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence

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

/-- The intrinsic centered operator norm is exactly the exponential of minus
its logarithmic mass rate times the physical lattice spacing.

This is a theorem about the actual finite Wilson operator norm, not a mass
normalization convention. -/
theorem centeredTransferFactor_eq_exp_neg_rate_mul_latticeSpacing
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    C.boundedAnalysis.centeredTransferFactor n =
      Real.exp
        (-physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
            C.boundedAnalysis n * S.latticeSpacing n) := by
  have ha : 0 < S.latticeSpacing n := S.latticeSpacing_pos n
  have hfactor : 0 < C.boundedAnalysis.centeredTransferFactor n :=
    C.transferFactor_pos n
  have hlog :
      -physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
          C.boundedAnalysis n * S.latticeSpacing n =
        Real.log (C.boundedAnalysis.centeredTransferFactor n) := by
    unfold physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
    field_simp [ne_of_gt ha]
  rw [hlog, Real.exp_log hfactor]

/-- For every finite lattice scale and every strictly positive rate excess
`eps`, the **actual centered Wilson one-step operator** has a nonzero slow
vector whose one-step norm beats the exponential threshold corresponding to
`g_n + eps`.

Equivalently, finite slow-mode existence is automatic from the operator-norm
definition.  The genuinely Yang--Mills-specific reverse problem starts only
when these moving finite vectors must be recovered as continuum Hamiltonian
states with a Rayleigh limsup bound. -/
theorem exists_centeredApproximateSlowVector
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) {eps : ℝ} (heps : 0 < eps) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    ∃ F : Pn.CenteredCarrier,
      F ≠ 0 ∧
      Real.exp
          (-(physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
                C.boundedAnalysis n + eps) * S.latticeSpacing n) * ‖F‖ <
        ‖C.boundedAnalysis.centeredOneStepOperator n F‖ := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let Tn : Pn.CenteredCarrier →L[ℝ] Pn.CenteredCarrier :=
    C.boundedAnalysis.centeredOneStepOperator n
  let gn : ℝ :=
    physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
      C.boundedAnalysis n
  let an : ℝ := S.latticeSpacing n
  let r : ℝ := Real.exp (-(gn + eps) * an)
  have ha : 0 < an := by
    dsimp [an]
    exact S.latticeSpacing_pos n
  have hstep : -(gn + eps) * an < -gn * an := by
    have hepsa : 0 < eps * an := mul_pos heps ha
    nlinarith
  have hrexp : r < Real.exp (-gn * an) := by
    dsimp [r]
    exact Real.exp_lt_exp.mpr hstep
  have hfactor :
      Real.exp (-gn * an) = C.boundedAnalysis.centeredTransferFactor n := by
    dsimp [gn, an]
    symm
    exact C.centeredTransferFactor_eq_exp_neg_rate_mul_latticeSpacing n
  have hr_lt : r < ‖Tn‖ := by
    rw [hfactor] at hrexp
    exact hrexp
  have hr_nonneg : 0 ≤ r := Real.exp_pos _ |>.le
  rcases continuousLinearMap_exists_nonzero_apply_norm_gt_mul_norm_of_lt_opNorm
      Tn hr_nonneg hr_lt with ⟨F, hF, hslow⟩
  exact ⟨F, hF, hslow⟩

end PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence

end MathlibAnalytic
end MGAP4D

end