import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConditionalResponseRMSV5_FG
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousGroundStateFiberCrossRatio
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumKernelHarnack
import MGAP4D.MathlibAnalytic.ContinuousNormalizedExponentialOscillation
import Mathlib.Tactic

/-!
# P4-Q2-FK: a volume-independent density floor for FG's genuine posterior

For the ACTUAL positive continuous ground-state Wilson posterior used by
P4-Q2-FG, the one-link conditional density relative to normalized compact Haar
has an explicit pointwise lower and upper bound:

  exp (-16 * beta) <= posteriorDensity(z,e,g) <= exp (16 * beta).

It holds for EVERY finite periodic spatial volume H, group rank N>0, link,
source boundary and right background, with the original Wilson kernel and
canonical physical vacuum left intact.

The proof uses the independently proved volume-uniform 8*beta
one-slab-kernel oscillation and 8*beta physical vacuum Harnack, then
passes through the EXACT normalized exponential posterior density.
It does not replace the inner posterior by Haar, nor prove an
all-link frame floor, locality, H1-C3 closure or mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 650000

local instance p4Q2FK_topologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2FK_compactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2FK_secondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2FK_measurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2FK_borelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace GroundStatePosteriorJoint

/-- Volume-independent Harnack inequality for the EXACT continuous
one-link Wilson kernel times the updated physical ground-state vacuum.
The factors are each exp(8 beta); no arbitrary global sup appears. -/
theorem p4Q2FK_actualWilsonCompleteLinkWeight_le_exp_sixteen
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
        H N hN beta hbeta left right e g ≤
      Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
          H N hN beta hbeta left right e h := by
  let Bg := Function.update right e g
  let Bh := Function.update right e h
  let R : ℝ := Real.exp (8 * beta)
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
  let Omega := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H N hN beta hbeta
  have hk : K left Bg ≤ R * K left Bh := by
    simpa [Bg, Bh, R, K] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_le_exp_eight_mul_update_right
        H N hN beta hbeta left right e g h
  have ho : Omega Bg ≤ R * Omega Bh := by
    simpa [Bg, Bh, R, Omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_update_right_le_exp_eight_mul_update_right
        H N hN beta hbeta right e g h
  have hOg : 0 ≤ Omega Bg := by
    exact (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta Bg).le
  have hKh : 0 ≤ K left Bh := by
    exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta left Bh).le
  have hR : 0 ≤ R := (Real.exp_pos _).le
  have hRR : R * R = Real.exp (16 * beta) := by
    dsimp [R]
    rw [← Real.exp_add]
    congr 1
    ring
  change K left Bg * Omega Bg ≤
    Real.exp (16 * beta) * (K left Bh * Omega Bh)
  calc
    K left Bg * Omega Bg ≤
        (R * K left Bh) * Omega Bg :=
      mul_le_mul_of_nonneg_right hk hOg
    _ ≤ (R * K left Bh) * (R * Omega Bh) :=
      mul_le_mul_of_nonneg_left ho (mul_nonneg hR hKh)
    _ = (R * R) * (K left Bh * Omega Bh) := by ring
    _ = Real.exp (16 * beta) * (K left Bh * Omega Bh) := by rw [hRR]

/-- The exact complete one-link log weight oscillates by at most 16 beta,
uniformly over all links, boundary configurations and finite volumes. -/
theorem p4Q2FK_actualWilsonCompleteLinkLogWeight_oscillation
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left right e g -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left right e h ≤ 16 * beta := by
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
      H N hN beta hbeta left right e
  have hWh : 0 < W h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight_pos
      H N hN beta hbeta left right e h
  have hW : W g ≤ Real.exp (16 * beta) * W h :=
    p4Q2FK_actualWilsonCompleteLinkWeight_le_exp_sixteen
      H N hN beta hbeta left right e g h
  have hLog : Real.log (W g) ≤
      Real.log (Real.exp (16 * beta) * W h) :=
    Real.log_le_log hWh hW
  rw [Real.log_mul (Real.exp_pos _).ne' hWh.ne', Real.log_exp] at hLog
  change Real.log (W g) - Real.log (W h) ≤ 16 * beta
  linarith

/-- The REAL normalized conditional density of the exact interacting
Wilson posterior is bounded between exp(-16 beta) and exp(16 beta)
relative to normalized SU(N) Haar. This is NOT a surrogate law. -/
theorem p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp (-16 * beta) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H N hN beta hbeta left right e g ∧
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H N hN beta hbeta left right e g ≤ Real.exp (16 * beta) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let L :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H N hN beta hbeta left right e
  have hCont : Continuous L :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H N hN beta hbeta left right e
  have hOsc : ∀ x y : Matrix.specialUnitaryGroup (Fin N) ℂ,
      (L x - (0 : ℝ)) - (L y - 0) ≤ 16 * beta := by
    intro x y
    have hx :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_eq_groundStateCompleteLogWeight
        H N hN beta hbeta left right e x
    have hy :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_eq_groundStateCompleteLogWeight
        H N hN beta hbeta left right e y
    simp only [sub_zero]
    change L x - L y ≤ 16 * beta
    rw [hx, hy]
    exact p4Q2FK_actualWilsonCompleteLinkLogWeight_oscillation
      H N hN beta hbeta left right e x y
  have hBounds :=
    continuousNormalizedExp_mutual_le_exp_mul_of_difference_oscillation
      μ L (fun _ => (0 : ℝ)) hCont continuous_const (16 * beta) hOsc g
  have hZero :
      continuousNormalizedExp μ (fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => (0 : ℝ)) g =
        (1 : ℝ) := by
    simp [continuousNormalizedExp, continuousExpPartition, μ]
  have hUpper :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H N hN beta hbeta left right e g ≤ Real.exp (16 * beta) := by
    change continuousNormalizedExp μ L g ≤ Real.exp (16 * beta)
    simpa [hZero] using hBounds.1
  have hLowerOne : (1 : ℝ) ≤
      Real.exp (16 * beta) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H N hN beta hbeta left right e g := by
    change (1 : ℝ) ≤ Real.exp (16 * beta) * continuousNormalizedExp μ L g
    simpa [hZero] using hBounds.2
  have hLower :
      Real.exp (-16 * beta) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H N hN beta hbeta left right e g := by
    have hp : 0 < Real.exp (16 * beta) := Real.exp_pos _
    have hdiv :
        (1 : ℝ) / Real.exp (16 * beta) ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
            H N hN beta hbeta left right e g :=
      (div_le_iff₀ hp).mpr (by simpa [mul_comm] using hLowerOne)
    simpa [Real.exp_neg, div_eq_mul_inv] using hdiv
  exact ⟨hLower, hUpper⟩

/-- At beta=0 the true one-link Wilson posterior density is literally Haar:
the pointwise equality is a consequence of the explicit two-sided bounds. -/
theorem p4Q2FK_originalWilsonPosteriorConditionalDensity_beta_zero
    (H N : ℕ) (hN : 0 < N)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H N hN 0 (le_refl 0) left right e g = 1 := by
  have hBound :=
    p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H N hN 0 (le_refl 0) left right e g
  have hLo : 1 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H N hN 0 (le_refl 0) left right e g := by
    simpa using hBound.1
  have hHi :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H N hN 0 (le_refl 0) left right e g ≤ 1 := by
    simpa using hBound.2
  exact le_antisymm hHi hLo

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FK_actualWilsonCompleteLinkWeight_le_exp_sixteen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FK_actualWilsonCompleteLinkLogWeight_oscillation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FK_originalWilsonPosteriorConditionalDensity_beta_zero
