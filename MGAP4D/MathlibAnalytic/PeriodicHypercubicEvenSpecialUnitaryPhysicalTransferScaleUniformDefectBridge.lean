import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 1000000

/-- For the restriction of a bounded real Hilbert-space operator to the
orthogonal complement of its full eigenvalue-one space, the squared norm defect
is bounded below by the exact operator-norm coefficient `1 - ‖R‖²`.

This is purely variational and does not use compactness. Compactness is needed
upstream only to know that the coefficient is positive at each fixed finite
volume. -/
theorem realHilbertTopEigenspaceOrthogonalRestriction_sq_defect_lower_bound
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (y : (realHilbertTopEigenspace S)ᗮ) :
    (1 - ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ ^ 2) *
        ‖(y : E)‖ ^ 2 ≤
      ‖(y : E)‖ ^ 2 - ‖S (y : E)‖ ^ 2 := by
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hSymm
  have hR := ContinuousLinearMap.le_opNorm R y
  change ‖S (y : E)‖ ≤ ‖R‖ * ‖(y : E)‖ at hR
  have hsq :
      ‖S (y : E)‖ * ‖S (y : E)‖ ≤
        (‖R‖ * ‖(y : E)‖) * (‖R‖ * ‖(y : E)‖) :=
    mul_self_le_mul_self (norm_nonneg _) hR
  change (1 - ‖R‖ ^ 2) * ‖(y : E)‖ ^ 2 ≤
    ‖(y : E)‖ ^ 2 - ‖S (y : E)‖ ^ 2
  simp only [pow_two]
  nlinarith

/-- Elementary square-root comparison used to turn a squared-defect coefficient
into a linear transfer-gap coefficient. -/
theorem real_sqrt_one_sub_le_one_sub_half
    {δ : ℝ} (_hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Real.sqrt (1 - δ) ≤ 1 - δ / 2 := by
  have hsub : 0 ≤ 1 - δ := sub_nonneg.mpr hδ1
  have hright : 0 ≤ 1 - δ / 2 := by linarith
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) hright).mp
  rw [Real.sq_sqrt hsub]
  nlinarith [sq_nonneg δ]

/-- A uniform lower bound on the squared norm defect on the full top-orthogonal
sector bounds the restricted operator norm by `sqrt (1 - δ)`.

This is the quantitative replacement for the qualitative compactness argument
that proves only `‖R‖ < 1` at each fixed finite volume. -/
theorem realHilbertTopEigenspaceOrthogonalRestriction_norm_le_sqrt_of_sq_defect
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (δ : ℝ) (_hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hdefect : ∀ y : (realHilbertTopEigenspace S)ᗮ,
      δ * ‖(y : E)‖ ^ 2 ≤
        ‖(y : E)‖ ^ 2 - ‖S (y : E)‖ ^ 2) :
    ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ ≤
      Real.sqrt (1 - δ) := by
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hSymm
  apply ContinuousLinearMap.opNorm_le_bound R (Real.sqrt_nonneg _)
  intro y
  have hd := hdefect y
  change ‖S (y : E)‖ ≤ Real.sqrt (1 - δ) * ‖(y : E)‖
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  have hsqrt : (Real.sqrt (1 - δ)) ^ 2 = 1 - δ :=
    Real.sq_sqrt (sub_nonneg.mpr hδ1)
  simp only [pow_two] at hd ⊢
  have hsqrt' : Real.sqrt (1 - δ) * Real.sqrt (1 - δ) = 1 - δ := by
    simpa [pow_two] using hsqrt
  nlinarith

/-- A squared-defect coefficient `δ ∈ [0,1]` yields the explicit linear gap
`δ/2 ≤ 1 - ‖R‖`. This deliberately avoids hiding a scale-dependent square
root in downstream finite-volume estimates. -/
theorem realHilbertTopEigenspaceOrthogonalRestriction_gap_lower_bound_of_sq_defect
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hdefect : ∀ y : (realHilbertTopEigenspace S)ᗮ,
      δ * ‖(y : E)‖ ^ 2 ≤
        ‖(y : E)‖ ^ 2 - ‖S (y : E)‖ ^ 2) :
    δ / 2 ≤
      1 - ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ := by
  have hnorm :=
    realHilbertTopEigenspaceOrthogonalRestriction_norm_le_sqrt_of_sq_defect
      S hSymm δ hδ0 hδ1 hdefect
  have hsqrt := real_sqrt_one_sub_le_one_sub_half hδ0 hδ1
  linarith

/-- Conversely, a linear lower bound `ε ≤ 1 - ‖R‖` forces the squared norm
defect coefficient `2 ε - ε²`. Thus uniform transfer separation and uniform
squared-defect coercivity are quantitatively equivalent up to explicit
constants. -/
theorem realHilbertTopEigenspaceOrthogonalRestriction_sq_defect_lower_bound_of_gap
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (ε : ℝ)
    (hgap : ε ≤ 1 - ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖)
    (y : (realHilbertTopEigenspace S)ᗮ) :
    (2 * ε - ε ^ 2) * ‖(y : E)‖ ^ 2 ≤
      ‖(y : E)‖ ^ 2 - ‖S (y : E)‖ ^ 2 := by
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hSymm
  have hq : ‖R‖ ≤ 1 - ε := by
    change ε ≤ 1 - ‖R‖ at hgap
    linarith
  have hsq : ‖R‖ * ‖R‖ ≤ (1 - ε) * (1 - ε) :=
    mul_self_le_mul_self (norm_nonneg R) hq
  have hcoeff : 2 * ε - ε ^ 2 ≤ 1 - ‖R‖ ^ 2 := by
    simp only [pow_two]
    nlinarith
  have hbase :=
    realHilbertTopEigenspaceOrthogonalRestriction_sq_defect_lower_bound
      S hSymm y
  change
    (2 * ε - ε ^ 2) * ‖(y : E)‖ ^ 2 ≤
      ‖(y : E)‖ ^ 2 - ‖S (y : E)‖ ^ 2
  exact le_trans
    (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg ‖(y : E)‖)) hbase

section PhysicalOneSlab

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
local notation "T" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H N hN beta hbeta
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta

/-- The raw one-slab squared norm defect on the full normalized-transfer
top-orthogonal physical sector.

The normalization is intentionally not divided out: this is stated directly in
terms of the actual finite physical one-slab transfer `T`, which itself is the
Gauss-law restriction of the literal Wilson Hilbert--Schmidt kernel operator. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
    (x : K) : ℝ :=
  ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 - ‖T (x : G)‖ ^ 2

/-- Exact norm scaling between the raw physical one-slab transfer and its
normalized version. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_raw_normalized_norm_scale
    (x : K) :
    ‖T‖ * ‖S (x : G)‖ = ‖T (x : G)‖ := by
  have hTpos : 0 < ‖T‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta
  change ‖T‖ * ‖‖T‖⁻¹ • T (x : G)‖ = ‖T (x : G)‖
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hTpos]
  rw [mul_inv_cancel_left₀ hTpos.ne']

/-- A raw squared-defect lower bound becomes the corresponding normalized
squared-defect lower bound with exactly the same dimensionless coefficient. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_raw_sq_defect_to_normalized
    (δ : ℝ) (x : K)
    (hraw :
      δ * ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
          H N hN beta hbeta x) :
    δ * ‖(x : G)‖ ^ 2 ≤
      ‖(x : G)‖ ^ 2 - ‖S (x : G)‖ ^ 2 := by
  have hTpos : 0 < ‖T‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta
  have hscale :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_raw_normalized_norm_scale
      H N hN beta hbeta x
  have hscaleSq :
      ‖T‖ ^ 2 * ‖S (x : G)‖ ^ 2 = ‖T (x : G)‖ ^ 2 := by
    calc
      ‖T‖ ^ 2 * ‖S (x : G)‖ ^ 2 =
          (‖T‖ * ‖S (x : G)‖) ^ 2 := by ring
      _ = ‖T (x : G)‖ ^ 2 := by rw [hscale]
  change
    δ * ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 ≤
      ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 - ‖T (x : G)‖ ^ 2 at hraw
  have hT2pos : 0 < ‖T‖ ^ 2 := sq_pos_of_pos hTpos
  have hmul :
      ‖T‖ ^ 2 * (δ * ‖(x : G)‖ ^ 2) ≤
        ‖T‖ ^ 2 * (‖(x : G)‖ ^ 2 - ‖S (x : G)‖ ^ 2) := by
    calc
      ‖T‖ ^ 2 * (δ * ‖(x : G)‖ ^ 2) =
          δ * ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 := by ring
      _ ≤ ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 - ‖T (x : G)‖ ^ 2 := hraw
      _ = ‖T‖ ^ 2 * (‖(x : G)‖ ^ 2 - ‖S (x : G)‖ ^ 2) := by
        rw [← hscaleSq]
        ring
  exact (mul_le_mul_iff_of_pos_left hT2pos).mp hmul

/-- The reverse normalization transport: a normalized squared-defect estimate
can be stated as a raw Wilson one-slab estimate after multiplication by the
squared top transfer scale. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_normalized_sq_defect_to_raw
    (δ : ℝ) (x : K)
    (hnorm :
      δ * ‖(x : G)‖ ^ 2 ≤
        ‖(x : G)‖ ^ 2 - ‖S (x : G)‖ ^ 2) :
    δ * ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
        H N hN beta hbeta x := by
  have hscale :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_raw_normalized_norm_scale
      H N hN beta hbeta x
  have hscaleSq :
      ‖T‖ ^ 2 * ‖S (x : G)‖ ^ 2 = ‖T (x : G)‖ ^ 2 := by
    calc
      ‖T‖ ^ 2 * ‖S (x : G)‖ ^ 2 =
          (‖T‖ * ‖S (x : G)‖) ^ 2 := by ring
      _ = ‖T (x : G)‖ ^ 2 := by rw [hscale]
  change
    δ * ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 ≤
      ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 - ‖T (x : G)‖ ^ 2
  calc
    δ * ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 =
        ‖T‖ ^ 2 * (δ * ‖(x : G)‖ ^ 2) := by ring
    _ ≤ ‖T‖ ^ 2 * (‖(x : G)‖ ^ 2 - ‖S (x : G)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hnorm (sq_nonneg ‖T‖)
    _ = ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 - ‖T (x : G)‖ ^ 2 := by
      rw [← hscaleSq]
      ring

/-- A model-facing raw one-slab squared-defect coefficient gives an explicit
lower bound for the already-canonical finite-volume transfer gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_rawDefect_lower_bound_implies_transferGap
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hraw : ∀ x : K,
      δ * ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
          H N hN beta hbeta x) :
    δ / 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  have hsymm :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H N hN beta hbeta
  have hdefect : ∀ y : (realHilbertTopEigenspace S)ᗮ,
      δ * ‖(y : G)‖ ^ 2 ≤
        ‖(y : G)‖ ^ 2 - ‖S (y : G)‖ ^ 2 := by
    intro y
    have yK : K := y
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_raw_sq_defect_to_normalized
      H N hN beta hbeta δ yK (hraw yK)
  have hgeneric :=
    realHilbertTopEigenspaceOrthogonalRestriction_gap_lower_bound_of_sq_defect
      S hsymm δ hδ0 hδ1 hdefect
  change δ / 2 ≤ 1 - ‖R‖
  exact hgeneric

/-- Conversely, a lower bound on the finite-volume transfer gap produces a raw
one-slab squared-defect lower bound with coefficient `2 ε - ε²`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_transferGap_lower_bound_implies_rawDefect
    (ε : ℝ)
    (hgap : ε ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta)
    (x : K) :
    (2 * ε - ε ^ 2) * ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
        H N hN beta hbeta x := by
  have hsymm :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H N hN beta hbeta
  have hgap' :
      ε ≤ 1 - ‖realHilbertTopEigenspaceOrthogonalRestriction S hsymm‖ := by
    change ε ≤ 1 - ‖R‖ at hgap
    exact hgap
  have xGeneric : (realHilbertTopEigenspace S)ᗮ := x
  have hnorm :=
    realHilbertTopEigenspaceOrthogonalRestriction_sq_defect_lower_bound_of_gap
      S hsymm ε hgap' xGeneric
  apply periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_normalized_sq_defect_to_raw
    H N hN beta hbeta (2 * ε - ε ^ 2) x
  exact hnorm

end PhysicalOneSlab

section ScalingFamily

variable
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)

/-- The exact model-facing uniformity target for the current one-slab mechanism:
there is a positive scale-independent dimensionless coefficient in the raw
physical one-slab squared norm defect on the full top-orthogonal sector. -/
def PeriodicHypercubicEvenSpecialUnitaryHasUniformRawTopOrthogonalSquaredDefect : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
    ∀ (n : ℕ)
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)),
      δ *
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n)‖ ^ 2 *
          ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent n) N)‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
          (halfExtent n) N hN (beta n) (hbeta n) x

/-- The current scale-uniform global-gap target expressed directly as a
positive lower bound for `1 - ‖R_n‖`. -/
def PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ n : ℕ,
      ε ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        (halfExtent n) N hN (beta n) (hbeta n)

/-- Raw uniform squared-defect coercivity implies a uniform positive transfer
gap, with the explicit conversion `ε = δ/2`. -/
theorem periodicHypercubicEvenSpecialUnitary_uniformRawDefect_implies_uniformTransferGap
    (hraw : PeriodicHypercubicEvenSpecialUnitaryHasUniformRawTopOrthogonalSquaredDefect
      halfExtent N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
      halfExtent N hN beta hbeta := by
  rcases hraw with ⟨δ, hδpos, hδ1, hraw⟩
  refine ⟨δ / 2, by positivity, ?_⟩
  intro n
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_rawDefect_lower_bound_implies_transferGap
    (halfExtent n) N hN (beta n) (hbeta n)
    δ hδpos.le hδ1 (fun x => hraw n x)

/-- Uniform positive transfer separation implies a uniform raw squared-defect
coercivity estimate. The coefficient is `δ = 2 ε - ε²`; positivity and the
normalization `δ ≤ 1` follow automatically because every transfer gap is at
most one. -/
theorem periodicHypercubicEvenSpecialUnitary_uniformTransferGap_implies_uniformRawDefect
    (hgap : PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
      halfExtent N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformRawTopOrthogonalSquaredDefect
      halfExtent N hN beta hbeta := by
  rcases hgap with ⟨ε, hεpos, hgap⟩
  have hε1 : ε ≤ 1 := by
    have h0 := hgap 0
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap] at h0
    have hnorm := norm_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        (halfExtent 0) N hN (beta 0) (hbeta 0))
    linarith
  let δ : ℝ := 2 * ε - ε ^ 2
  have hδpos : 0 < δ := by
    have hfactor : 0 < ε * (2 - ε) :=
      mul_pos hεpos (by linarith)
    dsimp [δ]
    nlinarith
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    nlinarith [sq_nonneg (1 - ε)]
  refine ⟨δ, hδpos, hδ1, ?_⟩
  intro n x
  dsimp [δ]
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_transferGap_lower_bound_implies_rawDefect
    (halfExtent n) N hN (beta n) (hbeta n) ε (hgap n) x

/-- Main scale-uniform diagnostic theorem for the current finite physical
one-slab mechanism.

A positive scale-uniform lower bound for `1 - ‖R_n‖` exists if and only if the
actual raw finite physical one-slab transfers satisfy a positive
scale-independent squared norm defect on their full top-orthogonal sectors.

Therefore the remaining global-gap problem is now exactly a raw-model
inequality. Compactness alone proves only pointwise positivity and cannot
supply either side of this equivalence uniformly. -/
theorem periodicHypercubicEvenSpecialUnitary_uniformRawDefect_iff_uniformTransferGap :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformRawTopOrthogonalSquaredDefect
        halfExtent N hN beta hbeta ↔
      PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
        halfExtent N hN beta hbeta := by
  constructor
  · exact periodicHypercubicEvenSpecialUnitary_uniformRawDefect_implies_uniformTransferGap
      halfExtent N hN beta hbeta
  · exact periodicHypercubicEvenSpecialUnitary_uniformTransferGap_implies_uniformRawDefect
      halfExtent N hN beta hbeta

/-- Audit-visible receipt for the scale-uniform reduction. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabScaleUniformDefectBridgePackage : Prop where
  rawToGap :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformRawTopOrthogonalSquaredDefect
        halfExtent N hN beta hbeta →
      PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
        halfExtent N hN beta hbeta
  gapToRaw :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
        halfExtent N hN beta hbeta →
      PeriodicHypercubicEvenSpecialUnitaryHasUniformRawTopOrthogonalSquaredDefect
        halfExtent N hN beta hbeta
  equivalence :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformRawTopOrthogonalSquaredDefect
        halfExtent N hN beta hbeta ↔
      PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
        halfExtent N hN beta hbeta

/-- Construct the scale-uniform defect/gap bridge package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabScaleUniformDefectBridgePackage :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabScaleUniformDefectBridgePackage
      halfExtent N hN beta hbeta :=
  { rawToGap := periodicHypercubicEvenSpecialUnitary_uniformRawDefect_implies_uniformTransferGap
      halfExtent N hN beta hbeta
    gapToRaw := periodicHypercubicEvenSpecialUnitary_uniformTransferGap_implies_uniformRawDefect
      halfExtent N hN beta hbeta
    equivalence := periodicHypercubicEvenSpecialUnitary_uniformRawDefect_iff_uniformTransferGap
      halfExtent N hN beta hbeta }

end ScalingFamily

end

end MathlibAnalytic
end MGAP4D
