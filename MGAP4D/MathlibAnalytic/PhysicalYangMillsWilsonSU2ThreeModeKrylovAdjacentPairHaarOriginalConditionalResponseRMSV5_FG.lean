import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedPhysicalRelativeLinkProfileV5_FF
import Mathlib.Tactic

/-!
# P4-Q2-FG: original Wilson link-response conditional RMS BEFORE supremum

The previously verified FC/FF lane constructs the true signed
original-Wilson relative right-link response

  R(e,f,z,g) := [O_f(z) - O_f(z[e<-g])] / [W_beta(z)/Omega_beta(B)]

as an actual BCF. FE and FF then take the global supremum over (z,g)
to produce finite physical link profiles.

Here retain the original PHYSICAL Wilson conditional law nu(e,z) and
define its conditional RMS *at each actual pair-Haar configuration z*:

  M2(e,f,z) := integral_g R(e,f,z,g)^2 d nu(e,z)(g).

This is an actual finite nonnegative quantity, not a newly invented
independent Haar posterior. The original signed two-copy
posterior-resampling SQUARE at z equals the original positive
density-cancellation weight squared times M2:

  posteriorResamplingSquare(e,O_f,z)
    = (W_beta(z)/Omega_beta(B))^2 * M2(e,f,z).

This pointwise relation is stronger than an upper bound by a global
supremum, and is the target for a subsequent exact pair-Haar moment
identity. No fake localization or spatial decay is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 900000

local instance p4Q2FG_topologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2FG_compactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2FG_secondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2FG_measurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2FG_borelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
private noncomputable instance p4Q2FG_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Source- and spatial-link-specific actual conditional mean square
of the signed physical relative Wilson right-link response. The
conditioning is the ORIGINAL normalized Wilson one-link posterior,
not an independent Haar kernel. -/
noncomputable def p4Q2FG_originalWilsonRelativeResponseConditionalSquare
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
    (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF H N hN beta hbeta f e
      (z,g)) ^ 2
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta z.1 z.2 e

/-- Each ACTUAL Wilson posterior-fiber conditional response square is
nonnegative at every original physical pair-boundary configuration. -/
theorem p4Q2FG_originalWilsonRelativeResponseConditionalSquare_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 ≤ p4Q2FG_originalWilsonRelativeResponseConditionalSquare H N hN beta hbeta f e z := by
  unfold p4Q2FG_originalWilsonRelativeResponseConditionalSquare
  exact integral_nonneg fun g => sq_nonneg _

/-- Genuine conditional RMS is bounded by its actual link/source BCF
norm, not by the universal FC Harnack coefficient. -/
theorem p4Q2FG_originalWilsonRelativeResponseConditionalSquare_le_relativeSupSq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    p4Q2FG_originalWilsonRelativeResponseConditionalSquare H N hN beta hbeta f e z ≤
      ‖p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        H N hN beta hbeta f e‖ ^ 2 := by
  let B := p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H N hN beta hbeta f e
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta z.1 z.2 e
  letI : IsProbabilityMeasure ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_isProbabilityMeasure
      H N hN beta hbeta z.1 z.2 e
  have hc : Continuous (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (B (z,g)) ^ 2) :=
    (B.continuous.comp (continuous_const.prodMk continuous_id)).pow 2
  have hi : Integrable (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (B (z,g)) ^ 2) ν :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ g, (B (z,g)) ^ 2 ∂ν) ≤ ‖B‖ ^ 2
  calc
    (∫ g, (B (z,g)) ^ 2 ∂ν) ≤
      ∫ _g : Matrix.specialUnitaryGroup (Fin N) ℂ, ‖B‖ ^ 2 ∂ν := by
        apply integral_mono hi (integrable_const _)
        intro g
        have hb : |B (z,g)| ≤ ‖B‖ := by
          simpa only [Real.norm_eq_abs] using B.norm_coe_le_norm (z,g)
        have hs := pow_le_pow_left₀ (abs_nonneg _) hb 2
        simpa only [sq_abs] using hs
    _ = ‖B‖ ^ 2 := by simp

/-- The LITERAL physical signed original Wilson posterior two-copy
SQUARE equals its positive density-normalizing weight squared times
the TRUE conditional RMS of its signed relative link response.
No supremum is taken in z or candidate Wilson posterior link value g. -/
theorem p4Q2FG_originalWilsonPosteriorSquare_eq_weight_sq_conditionalRMS
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    posteriorResamplingSquare H N hN beta hbeta e
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) z =
      (normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta z *
        normalizedPhysicalOneSlabContinuousVacuumInverseBCF
          H N hN beta hbeta z.2) ^ 2 *
      p4Q2FG_originalWilsonRelativeResponseConditionalSquare
        H N hN beta hbeta f e z := by
  let O := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
  let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
  let B := p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H N hN beta hbeta f e
  let q : ℝ := W z * V z.2
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta z.1 z.2 e
  have hq : q ≠ 0 :=
    (p4Q2FF_originalWilsonDensityCancellationWeight_pos H N hN beta hbeta z).ne'
  have hb (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      B (z,g) * q = O z - O (z.1, Function.update z.2 e g) := by
    rw [p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF_apply]
    exact div_mul_cancel₀ _ hq
  have hp (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      (O z - O (z.1, Function.update z.2 e g)) ^ 2 =
        q ^ 2 * (B (z,g)) ^ 2 := by
    calc
      (O z - O (z.1, Function.update z.2 e g)) ^ 2 =
          (B (z,g) * q) ^ 2 := congrArg (fun t : ℝ => t ^ 2) (hb g).symm
      _ = q ^ 2 * (B (z,g)) ^ 2 := by ring
  change (∫ g, (O z - O (z.1, Function.update z.2 e g)) ^ 2 ∂ν) =
    q ^ 2 * (∫ g, (B (z,g)) ^ 2 ∂ν)
  calc
    (∫ g, (O z - O (z.1, Function.update z.2 e g)) ^ 2 ∂ν) =
        ∫ g, q ^ 2 * (B (z,g)) ^ 2 ∂ν := by
          exact integral_congr_ae (Filter.Eventually.of_forall hp)
    _ = q ^ 2 * ∫ g, (B (z,g)) ^ 2 ∂ν := integral_const_mul _ _

/-- At frozen beta zero the TRUE original-Wilson signed relative link
response vanishes for EVERY physical source and all physical links.
This is a pointwise statement about the BCF, not just an L²-a.e.
claim for a selected Krylov family. -/
theorem p4Q2FG_originalWilsonRelativeResponse_eq_zero_beta_zero
    (H N : ℕ) (hN : 0 < N)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      H N hN 0 (le_refl 0) f e = 0 := by
  let B := p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H N hN 0 (le_refl 0) f e
  have h := p4Q2FF_originalWilsonRelativeSignedLinkResponse_norm_le_FC
    H N hN 0 (le_refl 0) f e
  have hbound : ‖B‖ ≤ 0 := by
    simpa only [Real.exp_zero, zero_mul, one_pow, sub_self, mul_zero, zero_mul]
      using h
  have hzero : ‖B‖ = 0 := le_antisymm hbound (norm_nonneg _)
  exact norm_eq_zero.mp hzero

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FG_originalWilsonRelativeResponseConditionalSquare_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FG_originalWilsonRelativeResponseConditionalSquare_le_relativeSupSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FG_originalWilsonPosteriorSquare_eq_weight_sq_conditionalRMS
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FG_originalWilsonRelativeResponse_eq_zero_beta_zero
