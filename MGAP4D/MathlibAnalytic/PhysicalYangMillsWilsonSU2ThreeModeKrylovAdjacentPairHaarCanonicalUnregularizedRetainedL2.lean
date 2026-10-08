import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarCanonicalSqrtErrorJointL2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarRegularizedFrozenRightLinkCandidate
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumWilsonDensityHaarWitness
import Mathlib.Tactic

/-!
# P4-Q1: unregularized original-Wilson joint L² witnesses are truly retained

The original one-right-link sqrt-ratio r_e was constructed in the
ORIGINAL pair-Haar L² by PR #5307. PR #5308 transported r_e
to the ORIGINAL ground-state Wilson joint L² using the exact
half-density linear isometry U_beta and bounded each approximation
error by (exp(16 beta)-1)², independently of finite H.

Here we prove the crucial a.e. representative identity under the
GENUINE original joint law:

  U_beta(r_e)(A,B) = 1 / sqrt(W_(beta,c)(A,B[e<-1]))

The original canonical continuous W_(beta,c) is positive at every
point and agrees with the ORIGINAL quotient density W_beta only
pair-Haar-a.e.; that a.e. equality is explicitly transported to
the original joint law by absolute continuity. No arbitrary L²
quotient representative is evaluated at an exceptional point.

The original right-link identity-frozen inverse-sqrt is measurable
for the ACTUAL retained sigma algebra of all left coordinates and
all right coordinates except e, by specializing the already-proved
P4-Q1 measurable regularized function to delta=0 (absolute value
removes by strict pointwise positivity). The genuine joint L²
vector U_beta(r_e) is therefore retained-a.e. strongly measurable.

This completes an EXPLICIT unregularized retained witness and
allows the existing sharp original conditional-expectation
best-approximation theorem to yield a true finite-volume all-link
posterior-vacuum residual bound with its NECESSARY link count.

The separate frozen-beta-zero receiver drift is bounded likewise.
The all-link cardinality is NOT removed here; no volume-uniform
positive-beta gap or continuum mass gap is asserted. No Dobrushin.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4Q1UnregTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q1UnregCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q1UnregSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q1UnregMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q1UnregBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q1UnregSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The true original-joint L² isometric image of the original
pair-Haar sqrt ratio has the concrete one-right-link frozen
inverse-sqrt continuous-Wilson-density representative, joint-a.e. -/
theorem originalWilsonCanonicalRightLinkJointVacuumApproximant_ae_eq_invSqrtFrozen
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (fun z => originalWilsonCanonicalRightLinkJointVacuumApproximant
      H beta hbeta e z) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H 2 (Nat.zero_lt_succ 1) beta hbeta]
      (fun z => (1 : ℝ) / Real.sqrt
        (originalWilsonContinuousPhysicalJointWeight H beta hbeta
          (z.1, Function.update z.2 e
            (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)))) := by
  classical
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let ν := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H 2 (Nat.zero_lt_succ 1) beta hbeta
  let q := originalWilsonNormalizedFrozenRightLinkSqrtRatioL2 H beta hbeta e
  let w := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
    H 2 (Nat.zero_lt_succ 1) beta hbeta
  let c := originalWilsonContinuousPhysicalJointWeight H beta hbeta
  have hνμ : ν ≪ μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_absolutelyContinuous_pairHaar
      H 2 (Nat.zero_lt_succ 1) beta hbeta
  have hqμ :
      (fun z => q z) =ᵐ[μ]
        (originalWilsonNormalizedFrozenRightLinkSqrtRatio H beta hbeta e) :=
    originalWilsonNormalizedFrozenRightLinkSqrtRatioL2_ae_eq H beta hbeta e
  have hqν :
      (fun z => q z) =ᵐ[ν]
        (originalWilsonNormalizedFrozenRightLinkSqrtRatio H beta hbeta e) :=
    hνμ.ae_eq hqμ
  have hcμ : c =ᵐ[μ] w := by
    simpa only [c, w, μ,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure] using
      (originalWilsonContinuousPhysicalJointWeight_ae_eq_original H beta hbeta)
  have hcν : c =ᵐ[ν] w := hνμ.ae_eq hcμ
  have hU :
      (fun z => originalWilsonCanonicalRightLinkJointVacuumApproximant
        H beta hbeta e z) =ᵐ[ν]
      (fun z => q z /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
          H 2 (Nat.zero_lt_succ 1) beta hbeta z) := by
    simpa only [originalWilsonCanonicalRightLinkJointVacuumApproximant,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv_apply,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointFunction] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_coeFn
        H 2 (Nat.zero_lt_succ 1) beta hbeta q)
  filter_upwards [hU, hqν, hcν] with z hzU hzQ hzC
  rw [hzU, hzQ]
  let a := c z
  let b := c (z.1, Function.update z.2 e
    (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
  have ha : 0 < a := originalWilsonContinuousPhysicalJointWeight_pos
    H beta hbeta z
  have hb : 0 < b := originalWilsonContinuousPhysicalJointWeight_pos
    H beta hbeta
      (z.1, Function.update z.2 e
        (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
  change Real.sqrt (a / b) / Real.sqrt (w z) = (1 : ℝ) / Real.sqrt b
  rw [← hzC, Real.sqrt_div ha.le]
  have hane : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
  have hbne : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hb)
  field_simp [hane, hbne]

/-- The same ORIGINAL physical Wilson one-link candidate actually
belongs to the retained sigma algebra, as required by the real
CondExpL2 best-approximation theorem. -/
theorem originalWilsonCanonicalRightLinkJointVacuumApproximant_retained
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    AEStronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H 2 e]
      (fun z => originalWilsonCanonicalRightLinkJointVacuumApproximant
        H beta hbeta e z)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H 2 (Nat.zero_lt_succ 1) beta hbeta) := by
  let ν := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H 2 (Nat.zero_lt_succ 1) beta hbeta
  let frozen := fun z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
    (1 : ℝ) / Real.sqrt
      (originalWilsonContinuousPhysicalJointWeight H beta hbeta
        (z.1, Function.update z.2 e
          (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)))
  have hraw : AEStronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H 2 e]
      (originalWilsonRegularizedFrozenRightLinkVacuumFunction
        H beta hbeta 0 e) ν :=
    (originalWilsonRegularizedFrozenRightLinkVacuumFunction_measurable_retained
      H beta hbeta 0 e).aestronglyMeasurable
  have hfun : (originalWilsonRegularizedFrozenRightLinkVacuumFunction
        H beta hbeta 0 e) = frozen := by
    funext z
    change (1 : ℝ) / Real.sqrt
      (0 + |originalWilsonContinuousPhysicalJointWeight H beta hbeta
        (z.1, Function.update z.2 e
          (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))|) =
      (1 : ℝ) / Real.sqrt
        (originalWilsonContinuousPhysicalJointWeight H beta hbeta
          (z.1, Function.update z.2 e
            (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)))
    rw [abs_of_pos (originalWilsonContinuousPhysicalJointWeight_pos H beta hbeta
      (z.1, Function.update z.2 e
        (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)))]
    simp
  have hfrozen : AEStronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H 2 e]
      frozen ν := by
    simpa only [hfun] using hraw
  have hae := originalWilsonCanonicalRightLinkJointVacuumApproximant_ae_eq_invSqrtFrozen
    H beta hbeta e
  exact hfrozen.congr hae.symm

/-- Quantitative genuine SU(2) Wilson positive-beta posterior
vacuum fiber upper bound, with the honest finite-volume
spatial-link cardinality. The actual original conditional
expectations are unchanged. -/
theorem originalGroundStateJointTransportedPairHaarOne_fullResidual_le_card_SU2
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖originalGroundStateJointTransportedPairHaarOne H 2
          (Nat.zero_lt_succ 1) beta hbeta -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H 2 (Nat.zero_lt_succ 1) beta hbeta e
          (originalGroundStateJointTransportedPairHaarOne H 2
            (Nat.zero_lt_succ 1) beta hbeta)‖ ^ 2) ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        (Real.exp (16 * beta) - 1) ^ 2 := by
  exact
    (originalGroundStateJointTransportedPairHaarOne_fullResidual_le_candidates
      H 2 (Nat.zero_lt_succ 1) beta hbeta
      (fun e => originalWilsonCanonicalRightLinkJointVacuumApproximant H beta hbeta e)
      (originalWilsonCanonicalRightLinkJointVacuumApproximant_retained H beta hbeta)).trans
      (originalWilsonCanonicalRightLinkJointVacuumApproximant_fullError_le_card H beta hbeta)

/-- The genuine frozen beta-zero original physical receiver
projection drift is bounded by the same explicitly stated
finite-volume link-count factor. This is NOT the independent
positive-beta orthogonal receiver drift (P4-Q2). -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_beta_frozenDrift_le_card_SU2
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖pairHaarTransportedGroundStateSpatialLinkProjection H 2
          (Nat.zero_lt_succ 1) 0 (by norm_num) e
          (normalizedPhysicalOneSlabPairHaarReceiver H 2
            (Nat.zero_lt_succ 1) 0 (by norm_num) f) -
        pairHaarTransportedGroundStateSpatialLinkProjection H 2
          (Nat.zero_lt_succ 1) beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H 2
            (Nat.zero_lt_succ 1) 0 (by norm_num) f)‖ ^ 2) ≤
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) f) ^ 2 *
        ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          (Real.exp (16 * beta) - 1) ^ 2) := by
  have hbound :=
    normalizedPhysicalOneSlabPairHaarReceiver_beta_fullProjectionDrift_le_jointCandidates
      H 2 (Nat.zero_lt_succ 1) beta hbeta f
      (fun e => originalWilsonCanonicalRightLinkJointVacuumApproximant H beta hbeta e)
      (originalWilsonCanonicalRightLinkJointVacuumApproximant_retained H beta hbeta)
  have herror :=
    originalWilsonCanonicalRightLinkJointVacuumApproximant_fullError_le_card
      H beta hbeta
  exact le_trans hbound
    (mul_le_mul_of_nonneg_left herror (sq_nonneg _))

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
