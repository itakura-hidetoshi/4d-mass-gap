import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedWilsonSharpRawGapCriterionV5_PZ37ALO
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPoincareDefect
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALP: sharp original Wilson positive quadratic criterion

ALO proved the exact original physical fixed-beta0 raw norm criterion for the
full top-orthogonal sector. ALP replaces a norm-on-each-vector hypothesis
with the genuine Wilson positive quadratic form.

For the UNCHANGED positive, symmetric, compact physical Wilson one-slab P_H,
its normalized transfer S_H=P_H/||P_H|| and the full top-orthogonal K_H,
  ||R_H|| <= q IFF
  forall x in K_H,
    inner_R (P_H x) x <= q * ||P_H|| * ||x||^2
for q>=0. The same equivalence holds with one q before every finite H.
Positivity, not merely self-adjointness, makes the reverse implication
valid by the existing verified Rayleigh/Poincare norm theorem; compactness
is not required for this equivalence.

The exact physical feature-analysis factorization gives the alternate
criterion ||A_H x||^2 <= q*||P_H||*||x||^2. The ALJ floor ratio can also
be used as a more demanding *conditional* sufficient hypothesis.

No unconditional H-independent q<1, independent AJA witness, continuum
carrier, or Yang-Mills mass gap is asserted. The physical model, Haar,
full-top and fixed beta0=log(3/2)/64 have not been altered.
One new append-only Lean leaf. All axioms audited.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000

namespace GroundStatePosteriorJoint

/-- Sharp Rayleigh characterization for a positive bounded real operator.
This uses the existing Poincare/Rayleigh theorem for the nontrivial converse;
self-adjointness alone would not exclude negative spectral directions. -/
theorem p4Q2PZ37ALP_genericPositiveNorm_le_iff_quadratic
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hPositive : (T : E →ₗ[ℝ] E).IsPositive)
    (q : ℝ) (hq : 0 ≤ q) :
    (‖T‖ ≤ q) ↔ ∀ x : E, inner ℝ (T x) x ≤ q * ‖x‖ ^ 2 := by
  constructor
  · intro hNorm x
    have hCS : inner ℝ (T x) x ≤ ‖T x‖ * ‖x‖ := by
      have habs : |inner ℝ (T x) x| ≤ ‖T x‖ * ‖x‖ := by
        simpa [Real.norm_eq_abs] using
          (norm_inner_le_norm (𝕜 := ℝ) (T x) x)
      exact (le_abs_self _).trans habs
    calc
      inner ℝ (T x) x ≤ ‖T x‖ * ‖x‖ := hCS
      _ ≤ (‖T‖ * ‖x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm T x) (norm_nonneg x)
      _ = ‖T‖ * ‖x‖ ^ 2 := by ring
      _ ≤ q * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hNorm (sq_nonneg _)
  · intro hQuad
    have hSymm : ∀ x y : E, inner ℝ (T x) y = inner ℝ x (T y) := by
      intro x y
      exact hPositive.isSymmetric x y
    have hNN : ∀ x : E, 0 ≤ inner ℝ (T x) x := by
      intro x
      exact hPositive.inner_nonneg_left x
    have hDefect : ∀ x : E,
        (1 - q) * ‖x‖ ^ 2 ≤ realHilbertQuadraticDefect T x := by
      intro x
      dsimp [realHilbertQuadraticDefect]
      nlinarith only [hQuad x]
    have hR :=
      realHilbertSymmetric_opNorm_le_one_sub_of_quadraticDefect
        T hSymm hNN (show (1 - q : ℝ) ≤ 1 by linarith) hDefect
    linarith

/-- The same sharp quadratic criterion on the genuine full top-orthogonal
restriction. Its positivity is inherited from the ORIGINAL positive T. -/
theorem p4Q2PZ37ALP_genericPositiveOrthogonalNorm_le_iff_quadratic
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hPositive : (T : E →ₗ[ℝ] E).IsPositive)
    (q : ℝ) (hq : 0 ≤ q) :
    (‖realHilbertTopEigenspaceOrthogonalRestriction
        T hPositive.isSymmetric‖ ≤ q) ↔
      ∀ x : (realHilbertTopEigenspace T)ᗮ,
        inner ℝ (T (x : E)) (x : E) ≤ q * ‖(x : E)‖ ^ 2 := by
  have hRestrictedPos :=
    realHilbertTopEigenspaceOrthogonalRestriction_isPositive T hPositive
  have hIff :=
    p4Q2PZ37ALP_genericPositiveNorm_le_iff_quadratic
      (realHilbertTopEigenspaceOrthogonalRestriction T hPositive.isSymmetric)
      hRestrictedPos q hq
  constructor
  · intro hNorm x
    have h := hIff.mp hNorm x
    change inner ℝ (T (x : E)) (x : E) ≤ q * ‖(x : E)‖ ^ 2 at h
    exact h
  · intro hQuad
    apply hIff.mpr
    intro x
    change inner ℝ (T (x : E)) (x : E) ≤ q * ‖(x : E)‖ ^ 2
    exact hQuad x

variable (H : ℕ)

local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "P" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "A" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "Fphys" => p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor H
local notation "rhoH" => p4Q2PZ37ALO_originalFixedMomentFloorNormRatio H

/-- Exact unmodified Wilson raw-to-normalized quadratic scaling, relying
on the existing proven positive physical norm and normalization formula. -/
theorem p4Q2PZ37ALP_originalFixedRawQuadratic_eq_norm_mul_normalized
    (x : K) :
    inner ℝ (P (x : G)) (x : G) =
      ‖P‖ * inner ℝ (S (x : G)) (x : G) := by
  have hPpos : 0 < ‖P‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
  have hS : inner ℝ (S (x : G)) (x : G) =
      ‖P‖⁻¹ * inner ℝ (P (x : G)) (x : G) := by
    simp [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply,
      inner_smul_left]
  calc
    inner ℝ (P (x : G)) (x : G) =
        ‖P‖ * (‖P‖⁻¹ * inner ℝ (P (x : G)) (x : G)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hPpos.ne', one_mul]
    _ = ‖P‖ * inner ℝ (S (x : G)) (x : G) := by rw [hS]

/-- Sharp original fixed-beta0 positive quadratic criterion for the
ACTUAL physical full-top-orthogonal Wilson transfer, not a surrogate. -/
theorem p4Q2PZ37ALP_originalFixedNorm_le_iff_rawQuadratic
    (q : ℝ) (hq : 0 ≤ q) :
    (‖R‖ ≤ q) ↔
      ∀ x : K, inner ℝ (P (x : G)) (x : G) ≤
        q * ‖P‖ * ‖(x : G)‖ ^ 2 := by
  have hPositive : (S : G →ₗ[ℝ] G).IsPositive :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isPositive
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
  have hIff :=
    p4Q2PZ37ALP_genericPositiveOrthogonalNorm_le_iff_quadratic
      S hPositive q hq
  constructor
  · intro hNorm x
    have hQuad := hIff.mp hNorm x
    rw [p4Q2PZ37ALP_originalFixedRawQuadratic_eq_norm_mul_normalized H x]
    calc
      ‖P‖ * inner ℝ (S (x : G)) (x : G) ≤
          ‖P‖ * (q * ‖(x : G)‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hQuad (norm_nonneg P)
      _ = q * ‖P‖ * ‖(x : G)‖ ^ 2 := by ring
  · intro hRaw
    apply hIff.mpr
    intro x
    have hPpos : 0 < ‖P‖ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
    apply (mul_le_mul_iff_of_pos_left hPpos).mp
    calc
      ‖P‖ * inner ℝ (S (x : G)) (x : G) =
          inner ℝ (P (x : G)) (x : G) :=
            (p4Q2PZ37ALP_originalFixedRawQuadratic_eq_norm_mul_normalized H x).symm
      _ ≤ q * ‖P‖ * ‖(x : G)‖ ^ 2 := hRaw x
      _ = ‖P‖ * (q * ‖(x : G)‖ ^ 2) := by ring

/-- An exact fixed-H Poincare/gap equivalence in ORIGINAL raw quadratic
coordinates. No gap coefficient is asserted without a genuine estimate. -/
theorem p4Q2PZ37ALP_originalFixedGap_ge_iff_rawQuadratic
    (q : ℝ) (hq : 0 ≤ q) :
    ((1 - q : ℝ) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ↔
      ∀ x : K, inner ℝ (P (x : G)) (x : G) ≤
        q * ‖P‖ * ‖(x : G)‖ ^ 2 := by
  have hIff := p4Q2PZ37ALP_originalFixedNorm_le_iff_rawQuadratic H q hq
  constructor
  · intro hGap
    apply hIff.mp
    have hNorm : ‖R‖ ≤ q := by
      change 1 - q ≤ 1 - ‖R‖ at hGap
      linarith
    exact hNorm
  · intro hRaw
    have hNorm := hIff.mpr hRaw
    change 1 - q ≤ 1 - ‖R‖
    linarith

/-- The SAME actual physical feature-analysis map A, with P=A* A,
identifies the Wilson positive quadratic form exactly. -/
theorem p4Q2PZ37ALP_originalFixedRawQuadratic_eq_featureNormSq
    (x : K) :
    inner ℝ (P (x : G)) (x : G) = ‖A (x : G)‖ ^ 2 := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_quadratic_eq_analysis_norm_sq
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le (x : G)

/-- A positive feature-analysis energy criterion is EXACTLY equivalent
to the original full-top-orthogonal normalized operator norm ceiling. -/
theorem p4Q2PZ37ALP_originalFixedNorm_le_iff_featureEnergy
    (q : ℝ) (hq : 0 ≤ q) :
    (‖R‖ ≤ q) ↔
      ∀ x : K, ‖A (x : G)‖ ^ 2 ≤
        q * ‖P‖ * ‖(x : G)‖ ^ 2 := by
  constructor
  · intro hNorm x
    rw [← p4Q2PZ37ALP_originalFixedRawQuadratic_eq_featureNormSq H x]
    exact (p4Q2PZ37ALP_originalFixedNorm_le_iff_rawQuadratic H q hq).mp hNorm x
  · intro hEnergy
    apply (p4Q2PZ37ALP_originalFixedNorm_le_iff_rawQuadratic H q hq).mpr
    intro x
    rw [p4Q2PZ37ALP_originalFixedRawQuadratic_eq_featureNormSq H x]
    exact hEnergy x

/-- The raw quadratic property is explicitly tied to the original H-indexed
Wilson physical carrier, not to a replacement Hilbert model. -/
def p4Q2PZ37ALP_originalFixedRawQuadraticBound (q : ℝ) : Prop :=
  ∀ x : K, inner ℝ (P (x : G)) (x : G) ≤
    q * ‖P‖ * ‖(x : G)‖ ^ 2

/-- A single coefficient q chosen before every finite volume H: exact
equivalence of normalized physical contraction and physical quadratic form. -/
theorem p4Q2PZ37ALP_allH_normBound_iff_rawQuadratic
    (q : ℝ) (hq : 0 ≤ q) :
    (∀ H : ℕ,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le‖ ≤ q) ↔
      ∀ H : ℕ, p4Q2PZ37ALP_originalFixedRawQuadraticBound H q := by
  constructor
  · intro hNorm H
    exact (p4Q2PZ37ALP_originalFixedNorm_le_iff_rawQuadratic H q hq).mp (hNorm H)
  · intro hQuad H
    exact (p4Q2PZ37ALP_originalFixedNorm_le_iff_rawQuadratic H q hq).mpr (hQuad H)

/-- The still-open all-H uniform original Wilson gap question is
equivalent to existence of ONE q<1 satisfying the raw quadratic test.
This equivalence does NOT construct q. -/
theorem p4Q2PZ37ALP_allH_uniformGapFactor_iff_rawQuadratic :
    (∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
      ∀ H : ℕ,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le‖ ≤ q) ↔
      ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
        ∀ H : ℕ, p4Q2PZ37ALP_originalFixedRawQuadraticBound H q := by
  constructor
  · rintro ⟨q, hq, hqLt, hNorm⟩
    exact ⟨q, hq, hqLt,
      (p4Q2PZ37ALP_allH_normBound_iff_rawQuadratic q hq).mp hNorm⟩
  · rintro ⟨q, hq, hqLt, hQuad⟩
    exact ⟨q, hq, hqLt,
      (p4Q2PZ37ALP_allH_normBound_iff_rawQuadratic q hq).mpr hQuad⟩

/-- The stronger ALJ floor-scaled physical quadratic assumption is only
SUFFICIENT and entails a q*rhoH bound. The floor alone does not entail it. -/
theorem p4Q2PZ37ALP_originalFixedNorm_le_floorCorrectedQuadratic
    (q : ℝ) (hq : 0 ≤ q)
    (hRaw : ∀ x : K, inner ℝ (P (x : G)) (x : G) ≤
      q * Fphys * ‖(x : G)‖ ^ 2) :
    ‖R‖ ≤ q * rhoH := by
  have hRhoNonneg : 0 ≤ rhoH :=
    (p4Q2PZ37ALO_originalFixedMomentFloorNormRatio_pos H).le
  have hPpos : 0 < ‖P‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
  apply (p4Q2PZ37ALP_originalFixedNorm_le_iff_rawQuadratic
    H (q * rhoH) (mul_nonneg hq hRhoNonneg)).mpr
  intro x
  have hFactor : (q * rhoH) * ‖P‖ = q * Fphys := by
    unfold p4Q2PZ37ALO_originalFixedMomentFloorNormRatio
    calc
      (q * (Fphys / ‖P‖)) * ‖P‖ =
          q * ((Fphys / ‖P‖) * ‖P‖) := by ring
      _ = q * Fphys := by rw [div_mul_cancel₀ _ hPpos.ne']
  calc
    inner ℝ (P (x : G)) (x : G) ≤
        q * Fphys * ‖(x : G)‖ ^ 2 := hRaw x
    _ = (q * rhoH) * ‖P‖ * ‖(x : G)‖ ^ 2 := by rw [hFactor]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALP_genericPositiveNorm_le_iff_quadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALP_genericPositiveOrthogonalNorm_le_iff_quadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALP_originalFixedRawQuadratic_eq_norm_mul_normalized
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALP_originalFixedNorm_le_iff_rawQuadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALP_originalFixedGap_ge_iff_rawQuadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALP_originalFixedRawQuadratic_eq_featureNormSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALP_originalFixedNorm_le_iff_featureEnergy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALP_originalFixedRawQuadraticBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALP_allH_normBound_iff_rawQuadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALP_allH_uniformGapFactor_iff_rawQuadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALP_originalFixedNorm_le_floorCorrectedQuadratic
