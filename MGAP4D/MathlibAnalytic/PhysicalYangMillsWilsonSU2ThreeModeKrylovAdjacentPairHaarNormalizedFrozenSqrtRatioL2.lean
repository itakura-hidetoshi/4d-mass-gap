import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarCanonicalWeightedSqrtError
import Mathlib.Tactic

/-!
# P4-Q1: physical Wilson normalized frozen-right-link sqrt ratio in the ORIGINAL pair Haar L²

The actual physical Wilson joint density has the canonical everywhere
positive continuous representative W_(beta,c), agreeing pair-Haar-a.e.
with the ORIGINAL density from the genuine positive-beta joint law.

PRs #5304–#5306 proved the volume-independent ONE-link Harnack ratio
and normalized squared error.  Here we construct the explicit real
pair-Haar L² vector represented by

  r_e(A,B) = sqrt(W_(beta,c)(A,B) / W_(beta,c)(A,B[e<-1])).

We prove measurable/continuous, MemLp(2), and the EXACT Hilbert
one-link error bound

  ‖1 - r_e‖_(L²(pair Haar))² <= (exp(16 beta) - 1)²,

independent of finite volume H and with no use of Dobrushin.
The equality of this pair-Haar error with the ORIGINAL joint
posterior vacuum approximation is a separate transport step
using the already established half-density isometry U_beta.
An ALL-link sum of these individual errors can still scale with
the number of spatial links; no uniform full-sum claim is made.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4Q1SqrtTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q1SqrtCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q1SqrtSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q1SqrtMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q1SqrtBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q1SqrtSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q1SqrtSpatialHaarProbability (H : ℕ) :
    IsProbabilityMeasure (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

/-- The original canonical Wilson density ratio on the ordered
pair-Haar carrier, freezing just one right link to identity. -/
noncomputable def originalWilsonNormalizedFrozenRightLinkSqrtRatio
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) : ℝ :=
  Real.sqrt (
    originalWilsonContinuousPhysicalJointWeight H beta hbeta z /
    originalWilsonContinuousPhysicalJointWeight H beta hbeta
      (z.1, Function.update z.2 e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)))

/-- Continuity for the actual physical Wilson normalized ratio,
rather than measurability of a surrogate probability law. -/
theorem originalWilsonNormalizedFrozenRightLinkSqrtRatio_continuous
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (originalWilsonNormalizedFrozenRightLinkSqrtRatio H beta hbeta e) := by
  classical
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let G := Matrix.specialUnitaryGroup (Fin 2) ℂ
  have hright : Continuous (fun z : X × X => Function.update z.2 e (1 : G)) := by
    apply continuous_pi
    intro k
    by_cases hk : k = e
    · subst k
      simpa using
        (continuous_const : Continuous (fun _z : X × X => (1 : G)))
    · simpa [Function.update, hk] using
        ((continuous_apply k).comp (continuous_snd : Continuous (Prod.snd : X × X → X)))
  have hpair : Continuous (fun z : X × X =>
      (z.1, Function.update z.2 e (1 : G))) :=
    continuous_fst.prodMk hright
  have hW : Continuous (originalWilsonContinuousPhysicalJointWeight H beta hbeta) :=
    originalWilsonContinuousPhysicalJointWeight_continuous H beta hbeta
  have hfrozen : Continuous (fun z : X × X =>
      originalWilsonContinuousPhysicalJointWeight H beta hbeta
        (z.1, Function.update z.2 e (1 : G))) :=
    hW.comp hpair
  have hratio : Continuous (fun z : X × X =>
      originalWilsonContinuousPhysicalJointWeight H beta hbeta z /
      originalWilsonContinuousPhysicalJointWeight H beta hbeta
        (z.1, Function.update z.2 e (1 : G))) := by
    apply hW.div hfrozen
    intro z
    exact ne_of_gt
      (originalWilsonContinuousPhysicalJointWeight_pos H beta hbeta
        (z.1, Function.update z.2 e (1 : G)))
  exact Real.continuous_sqrt.comp hratio

/-- The one-link ratio itself is bounded by the ORIGINAL physical
Harnack coefficient exp(16 beta), independently of H. -/
theorem originalWilsonNormalizedFrozenRightLinkSqrtRatio_norm_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    ‖originalWilsonNormalizedFrozenRightLinkSqrtRatio H beta hbeta e z‖ ≤
      Real.exp (16 * beta) := by
  let a := originalWilsonContinuousPhysicalJointWeight H beta hbeta z
  let b := originalWilsonContinuousPhysicalJointWeight H beta hbeta
    (z.1, Function.update z.2 e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
  let R : ℝ := Real.exp (16 * beta)
  have hb : 0 < b :=
    originalWilsonContinuousPhysicalJointWeight_pos H beta hbeta
      (z.1, Function.update z.2 e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
  have hR : 1 ≤ R := by
    have hx : 0 ≤ (16 : ℝ) * beta := mul_nonneg (by norm_num) hbeta
    have he := Real.add_one_le_exp (16 * beta)
    dsimp [R]
    linarith
  have hdiv : a / b ≤ R :=
    (div_le_iff₀ hb).mpr
      (originalWilsonContinuousPhysicalJointWeight_le_exp_sixteen_mul_frozen
        H beta hbeta z.1 z.2 e)
  have hrootR : Real.sqrt R ≤ R := by
    have hrootNonneg := Real.sqrt_nonneg R
    have hrootSquare := Real.sq_sqrt (le_trans (by norm_num : (0 : ℝ) ≤ 1) hR)
    nlinarith [sq_nonneg (R - 1)]
  have hbound : Real.sqrt (a / b) ≤ R :=
    (Real.sqrt_le_sqrt hdiv).trans hrootR
  change ‖Real.sqrt (a / b)‖ ≤ R
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg (a / b))] using hbound

/-- The concrete normalized one-right-link ratio belongs to
the ORIGINAL finite-volume pair-Haar real L² carrier. -/
theorem originalWilsonNormalizedFrozenRightLinkSqrtRatio_memLp
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    MemLp (originalWilsonNormalizedFrozenRightLinkSqrtRatio H beta hbeta e)
      2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure]
    infer_instance
  have hmeas : AEStronglyMeasurable
      (originalWilsonNormalizedFrozenRightLinkSqrtRatio H beta hbeta e) μ :=
    (originalWilsonNormalizedFrozenRightLinkSqrtRatio_continuous
      H beta hbeta e).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂μ,
      ‖originalWilsonNormalizedFrozenRightLinkSqrtRatio H beta hbeta e z‖ ≤
        Real.exp (16 * beta) :=
    Filter.Eventually.of_forall
      (originalWilsonNormalizedFrozenRightLinkSqrtRatio_norm_le H beta hbeta e)
  exact MemLp.of_bound hmeas (Real.exp (16 * beta)) hbound

/-- The literal original-pair-Haar L² ratio vector, without adding
a new reference law. -/
noncomputable def originalWilsonNormalizedFrozenRightLinkSqrtRatioL2
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2 :=
  (originalWilsonNormalizedFrozenRightLinkSqrtRatio_memLp H beta hbeta e).toLp
    (originalWilsonNormalizedFrozenRightLinkSqrtRatio H beta hbeta e)

/-- Canonical ratio L² vector has exactly the intended representative,
up to the unavoidable pair-Haar null set. -/
theorem originalWilsonNormalizedFrozenRightLinkSqrtRatioL2_ae_eq
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (fun z => originalWilsonNormalizedFrozenRightLinkSqrtRatioL2 H beta hbeta e z) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2]
      originalWilsonNormalizedFrozenRightLinkSqrtRatio H beta hbeta e :=
  (originalWilsonNormalizedFrozenRightLinkSqrtRatio_memLp H beta hbeta e).coeFn_toLp

/-- The TRUE pair-Haar Hilbert squared error of the explicit physical
normalized right-link ratio is bounded by (exp(16 beta)-1)².
This holds uniformly in each right target e at every finite H,
but the SUM over all targets may still grow with H. -/
theorem originalWilsonNormalizedFrozenRightLinkSqrtRatioL2_error_sq_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ‖(Lp.const 2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)
        (1 : ℝ)) -
      originalWilsonNormalizedFrozenRightLinkSqrtRatioL2 H beta hbeta e‖ ^ 2 ≤
      (Real.exp (16 * beta) - 1) ^ 2 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let one : Lp ℝ 2 μ := Lp.const 2 μ (1 : ℝ)
  let q : Lp ℝ 2 μ := originalWilsonNormalizedFrozenRightLinkSqrtRatioL2 H beta hbeta e
  let f := originalWilsonNormalizedFrozenRightLinkSqrtRatio H beta hbeta e
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure]
    infer_instance
  have hq : (fun z => q z) =ᵐ[μ] f :=
    originalWilsonNormalizedFrozenRightLinkSqrtRatioL2_ae_eq H beta hbeta e
  have hone : (fun z => one z) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
    change (fun z => (Lp.const 2 μ (1 : ℝ)) z) =ᵐ[μ] fun _ => (1 : ℝ)
    simp
  have hsub :
      (fun z => (one - q) z) =ᵐ[μ] (fun z => (1 : ℝ) - f z) := by
    filter_upwards [Lp.coeFn_sub one q, hone, hq] with z hs ho hqz
    rw [hs]
    simp only [Pi.sub_apply, ho, hqz]
  have hint : Integrable (fun z => ‖(one - q) z‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (one - q))).1
      (Lp.memLp (one - q))
  have hle : ∀ᵐ z ∂μ,
      ‖(one - q) z‖ ^ 2 ≤ (Real.exp (16 * beta) - 1) ^ 2 := by
    filter_upwards [hsub] with z hz
    rw [hz]
    simpa only [Real.norm_eq_abs, sq_abs] using
      (originalWilsonContinuousPhysicalJointWeight_rightLink_sqrtRatio_sq_le
        H beta hbeta z.1 z.2 e)
  calc
    ‖one - q‖ ^ 2 = ∫ z, ‖(one - q) z‖ ^ 2 ∂μ :=
      realL2_norm_sq_eq_integral_norm_sq _
    _ ≤ ∫ _z, (Real.exp (16 * beta) - 1) ^ 2 ∂μ :=
      integral_mono_ae hint (integrable_const _) hle
    _ = (Real.exp (16 * beta) - 1) ^ 2 := by simp

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
