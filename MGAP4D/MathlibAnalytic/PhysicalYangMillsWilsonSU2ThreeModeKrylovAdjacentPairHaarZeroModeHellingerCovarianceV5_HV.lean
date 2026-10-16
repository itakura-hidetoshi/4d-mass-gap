import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLMassFiniteGISOSDirectComparisonV5_HU
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalUnitKrylovTransferPositiveV5_GV
import Mathlib.Tactic

/-!
# P4-Q2-HV: positive-transfer two-posterior Hellinger noncancellation

The next source-separation gate is a real Wilson posterior expectation gap
for the actual positive constant-unit zero-depth Krylov source. Positivity
of a squared LEFT-RECEIVER DIFFERENCE (GT/GV) does not alone prove that
the ORIGINAL two-interacting-posterior GI expectation gap is nonzero.

This file supplies the missing generic *two-density* ingredient: for ANY
strictly positive source-transfer function T and two strictly positive,
continuous, genuinely different densities P0,P1, the integral

  int T * (P0-P1) * (1/sqrt(P1) - 1/sqrt(P0)) d(mu)

is STRICTLY POSITIVE under a finite, full-support reference measure. This
is a positive Hellinger-type covariance, not a square of the original GI
receiver and not a substitute posterior law. Consequently, the TWO
positive-source-weighted density-contrast projections cannot BOTH vanish.

The eventual physical bridge must instantiate T with the original Wilson
constant-unit transfer, and use GR's *original* relative signed receiver
formula and GI's true Haar pairing. Until that bridge is Lean-verified,
this abstract analytic result does not itself claim ker(source)=K, physical
GI nonvanishing, uniformity, H1-C3, or a continuum Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 950000

namespace GroundStatePosteriorJoint

section AbstractHellinger

/-- Exact real algebra for strictly positive densities. This makes the
sign of the symmetrized two-posterior projection manifestly positive
when the two density rows differ. -/
theorem p4Q2HV_real_sqrt_density_contrast_identity
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (p - q) * (1 / Real.sqrt q - 1 / Real.sqrt p) =
      (Real.sqrt p - Real.sqrt q) ^ 2 *
        (Real.sqrt p + Real.sqrt q) /
          (Real.sqrt p * Real.sqrt q) := by
  have hs : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp.le
  have ht : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq.le
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have htq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  calc
    (p - q) * (1 / Real.sqrt q - 1 / Real.sqrt p) =
        ((Real.sqrt p) ^ 2 - (Real.sqrt q) ^ 2) *
          (1 / Real.sqrt q - 1 / Real.sqrt p) := by rw [hs, ht]
    _ = (Real.sqrt p - Real.sqrt q) ^ 2 *
          (Real.sqrt p + Real.sqrt q) /
            (Real.sqrt p * Real.sqrt q) := by
          field_simp [hsp.ne', htq.ne']
          ring

/-- The Hellinger density contrast has a positive, and at unequal
densities strictly positive, pointwise pairing with a positive source. -/
theorem p4Q2HV_real_weighted_sqrt_density_contrast_nonneg
    (t p q : ℝ) (ht : 0 < t) (hp : 0 < p) (hq : 0 < q) :
    0 ≤ t * ((p - q) *
      (1 / Real.sqrt q - 1 / Real.sqrt p)) := by
  rw [p4Q2HV_real_sqrt_density_contrast_identity p q hp hq]
  apply mul_nonneg ht.le
  apply div_nonneg
  · exact mul_nonneg (sq_nonneg _)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Strict pointwise positivity whenever the two densities are unequal. -/
theorem p4Q2HV_real_weighted_sqrt_density_contrast_pos
    (t p q : ℝ) (ht : 0 < t) (hp : 0 < p) (hq : 0 < q)
    (hpq : p ≠ q) :
    0 < t * ((p - q) *
      (1 / Real.sqrt q - 1 / Real.sqrt p)) := by
  rw [p4Q2HV_real_sqrt_density_contrast_identity p q hp hq]
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have htq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsne : Real.sqrt p ≠ Real.sqrt q := by
    intro hEq
    apply hpq
    calc
      p = (Real.sqrt p) ^ 2 := (Real.sq_sqrt hp.le).symm
      _ = (Real.sqrt q) ^ 2 := by rw [hEq]
      _ = q := Real.sq_sqrt hq.le
  exact mul_pos ht
    (div_pos
      (mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hsne))
        (add_pos hsp htq))
      (mul_pos hsp htq))

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Compact, full-support, finite reference integration upgrades one
nonzero density-row difference to strictly positive weighted contrast.

No independent Haar conditional is assumed: the lemma is analytic,
ready for instantiation on actual normalized SU(2) Haar as a COMMON
reference for TWO DISTINCT interacting Wilson posterior densities. -/
theorem p4Q2HV_positive_weight_sqrt_density_contrast_integral
    (μ : Measure X) [IsFiniteMeasure μ]
    (hFull : ∀ U : Set X, IsOpen U → U.Nonempty → 0 < μ U)
    (T P0 P1 : X → ℝ)
    (hT : Continuous T) (hP0 : Continuous P0) (hP1 : Continuous P1)
    (hTpos : ∀ x, 0 < T x)
    (hP0pos : ∀ x, 0 < P0 x)
    (hP1pos : ∀ x, 0 < P1 x)
    (hDifferent : ∃ x, P0 x ≠ P1 x) :
    0 < ∫ x, T x * ((P0 x - P1 x) *
      (1 / Real.sqrt (P1 x) - 1 / Real.sqrt (P0 x))) ∂μ := by
  let F : X → ℝ := fun x =>
    T x * ((P0 x - P1 x) *
      (1 / Real.sqrt (P1 x) - 1 / Real.sqrt (P0 x)))
  have hInv0 :
      Continuous (fun x : X => (1 : ℝ) / Real.sqrt (P0 x)) :=
    continuous_const.div (Real.continuous_sqrt.comp hP0)
      (fun x => (Real.sqrt_pos.mpr (hP0pos x)).ne')
  have hInv1 :
      Continuous (fun x : X => (1 : ℝ) / Real.sqrt (P1 x)) :=
    continuous_const.div (Real.continuous_sqrt.comp hP1)
      (fun x => (Real.sqrt_pos.mpr (hP1pos x)).ne')
  have hFcont : Continuous F :=
    hT.mul ((hP0.sub hP1).mul (hInv1.sub hInv0))
  have hFint : Integrable F μ :=
    hFcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFnonneg (x : X) : 0 ≤ F x :=
    p4Q2HV_real_weighted_sqrt_density_contrast_nonneg
      (T x) (P0 x) (P1 x) (hTpos x) (hP0pos x) (hP1pos x)
  obtain ⟨g, hg⟩ := hDifferent
  have hFpos : 0 < F g :=
    p4Q2HV_real_weighted_sqrt_density_contrast_pos
      (T g) (P0 g) (P1 g) (hTpos g) (hP0pos g) (hP1pos g) hg
  have hSupportOpen : IsOpen (Function.support F) := by
    change IsOpen (F ⁻¹' ({0} : Set ℝ)ᶜ)
    exact isClosed_singleton.isOpen_compl.preimage hFcont
  have hSupportNonempty : (Function.support F).Nonempty :=
    ⟨g, hFpos.ne'⟩
  have hSupportPositive : 0 < μ (Function.support F) :=
    hFull _ hSupportOpen hSupportNonempty
  change 0 < ∫ x, F x ∂μ
  rw [integral_pos_iff_support_of_nonneg]
  · exact hSupportPositive
  · exact hFnonneg
  · exact hFint

/-- Positive physical-style source transfer cannot be simultaneously
orthogonal to the same true density contrast after BOTH alternative
positive half-density normalizations. This is stronger than a single
positive L² receiver difference and does not assume a source frame. -/
theorem p4Q2HV_two_sqrt_density_weighted_projections_cannot_both_vanish
    (μ : Measure X) [IsFiniteMeasure μ]
    (hFull : ∀ U : Set X, IsOpen U → U.Nonempty → 0 < μ U)
    (T P0 P1 : X → ℝ)
    (hT : Continuous T) (hP0 : Continuous P0) (hP1 : Continuous P1)
    (hTpos : ∀ x, 0 < T x)
    (hP0pos : ∀ x, 0 < P0 x)
    (hP1pos : ∀ x, 0 < P1 x)
    (hDifferent : ∃ x, P0 x ≠ P1 x) :
    (∫ x, T x * (P0 x - P1 x) / Real.sqrt (P0 x) ∂μ) ≠ 0 ∨
    (∫ x, T x * (P0 x - P1 x) / Real.sqrt (P1 x) ∂μ) ≠ 0 := by
  have hInv0 :
      Continuous (fun x : X => (1 : ℝ) / Real.sqrt (P0 x)) :=
    continuous_const.div (Real.continuous_sqrt.comp hP0)
      (fun x => (Real.sqrt_pos.mpr (hP0pos x)).ne')
  have hInv1 :
      Continuous (fun x : X => (1 : ℝ) / Real.sqrt (P1 x)) :=
    continuous_const.div (Real.continuous_sqrt.comp hP1)
      (fun x => (Real.sqrt_pos.mpr (hP1pos x)).ne')
  have hC0 : Continuous (fun x => T x * (P0 x - P1 x) /
      Real.sqrt (P0 x)) :=
    (hT.mul (hP0.sub hP1)).div
      (Real.continuous_sqrt.comp hP0)
      (fun x => (Real.sqrt_pos.mpr (hP0pos x)).ne')
  have hC1 : Continuous (fun x => T x * (P0 x - P1 x) /
      Real.sqrt (P1 x)) :=
    (hT.mul (hP0.sub hP1)).div
      (Real.continuous_sqrt.comp hP1)
      (fun x => (Real.sqrt_pos.mpr (hP1pos x)).ne')
  have hInt0 : Integrable (fun x => T x * (P0 x - P1 x) /
      Real.sqrt (P0 x)) μ :=
    hC0.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hInt1 : Integrable (fun x => T x * (P0 x - P1 x) /
      Real.sqrt (P1 x)) μ :=
    hC1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPositive :=
    p4Q2HV_positive_weight_sqrt_density_contrast_integral μ
      hFull T P0 P1 hT hP0 hP1 hTpos hP0pos hP1pos hDifferent
  have hDiff :
      (∫ x, T x * (P0 x - P1 x) / Real.sqrt (P1 x) ∂μ) -
      (∫ x, T x * (P0 x - P1 x) / Real.sqrt (P0 x) ∂μ) =
      ∫ x, T x * ((P0 x - P1 x) *
        (1 / Real.sqrt (P1 x) - 1 / Real.sqrt (P0 x))) ∂μ := by
    rw [← integral_sub hInt1 hInt0]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hStrict :
      (∫ x, T x * (P0 x - P1 x) / Real.sqrt (P0 x) ∂μ) <
      (∫ x, T x * (P0 x - P1 x) / Real.sqrt (P1 x) ∂μ) := by
    linarith [hPositive, hDiff]
  by_contra hZero
  push Not at hZero
  rcases hZero with ⟨h0, h1⟩
  rw [h0, h1] at hStrict
  exact (lt_irrefl (0 : ℝ)) hStrict

end AbstractHellinger
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HV_real_sqrt_density_contrast_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HV_real_weighted_sqrt_density_contrast_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HV_real_weighted_sqrt_density_contrast_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HV_positive_weight_sqrt_density_contrast_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HV_two_sqrt_density_weighted_projections_cannot_both_vanish
