import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGramTopDepthLinear
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-AA4: genuine Wilson normalized Rayleigh grows linearly in Krylov depth

AA3 proves the ORIGINAL frozen Wilson posterior Gram all-one quadratic
lower bound at large depth, provided the true projected full-link signed
innovation U is nonzero:
  onesᵀ G_r ones >= (r+1)^2 ‖U‖^2/4.

The coefficient-l2 norm squared of the all-one test vector is EXACTLY
r+1. Thus the ORIGINAL normalized Rayleigh has the sharp certified slope
  (r+1) ‖U‖^2/4 <= onesᵀ G_r ones/(r+1).

At fixed finite volume and strictly positive frozen beta, Z2 and AA3
certify ‖U‖>0 on an actual (one-sided) small-positive fine-coupling
window. For a physical profile in that sector, there is therefore NO
Krylov-depth independent upper coefficient-l2 Rayleigh/frame constant
for the UNCENTERED original posterior Gram (not merely at fine beta=0).

This is an upper-frame obstruction for one specific Krylov coefficient
direction. It does NOT disprove finite-volume Gram positivity, uniform
coercive LOWER bounds for a centered operator, or a continuum mass gap.
No proxy, Dobrushin, new axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 850000

/-- A positive top-signal coefficient eventually beats ANY finite
upper-frame constant along integer Krylov depths, even beyond a given
threshold. This is Archimedean and does not assume a uniform H bound. -/
theorem p4Q2AA_positive_top_slope_exceeds_any_frame_constant
    (a K : ℝ) (ha : 0 < a) (N : ℕ) :
    ∃ r : ℕ, N ≤ r ∧
      K < (((r + 1 : ℕ) : ℝ) * a ^ 2) / 4 := by
  have hk : 0 < a ^ 2 / 4 := by positivity
  obtain ⟨k, hkLarge⟩ := exists_nat_gt (K / (a ^ 2 / 4))
  let r : ℕ := N + k
  refine ⟨r, ?_, ?_⟩
  · dsimp [r]
    omega
  · have hK : K < (k : ℝ) * (a ^ 2 / 4) :=
      (div_lt_iff₀ hk).mp hkLarge
    have hkNat : k ≤ r + 1 := by
      dsimp [r]
      omega
    have hkReal : (k : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
      exact_mod_cast hkNat
    have hMul :
        (k : ℝ) * (a ^ 2 / 4) ≤
        ((r + 1 : ℕ) : ℝ) * (a ^ 2 / 4) :=
      mul_le_mul_of_nonneg_right hkReal (le_of_lt hk)
    calc
      K < (k : ℝ) * (a ^ 2 / 4) := hK
      _ ≤ ((r + 1 : ℕ) : ℝ) * (a ^ 2 / 4) := hMul
      _ = (((r + 1 : ℕ) : ℝ) * a ^ 2) / 4 := by ring

local instance p4AA4Group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4AA4Compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4AA4SecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4AA4Measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4AA4Borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4AA4LinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4AA4Complete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- Exact all-one coefficient-l2 normalization converts AA3 quadratic
ORIGINAL posterior Gram growth into a positive-slope LINEAR normalized
Rayleigh lower bound for every sufficiently large Krylov depth. -/
theorem fineRightKrylovPairHaarResidualGram_ones_eventually_normalizedRayleigh_ge_linearTop
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n : ℕ)
    (hTop :
      let H := halfExtent (n + 1)
      let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
      let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
      let I := physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
      0 < ‖WithLp.toLp 2
        (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (P u))‖) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r →
      let H := halfExtent (n + 1)
      let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
      let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
      let I := physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
      let U := WithLp.toLp 2
        (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (P u))
      ((((r + 1 : ℕ) : ℝ) * ‖U‖ ^ 2) / 4) ≤
        (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
          (Matrix.mulVec
            (fineRightKrylovPairHaarResidualGram
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
            (fun _ : Fin (r + 1) => (1 : ℝ)))) /
          (∑ j : Fin (r + 1), ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) := by
  let H := halfExtent (n + 1)
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let U := WithLp.toLp 2
    (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (P u))
  obtain ⟨N, hRaw⟩ :=
    fineRightKrylovPairHaarResidualGram_ones_eventually_ge_quarter_topDepth
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n hTop
  refine ⟨N, ?_⟩
  intro r hr
  have hGram := hRaw r hr
  change (((((r + 1 : ℕ) : ℝ) ^ 2) * ‖U‖ ^ 2) / 4) ≤
    star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
      (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
        (fun _ : Fin (r + 1) => (1 : ℝ))) at hGram
  have hCount : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
  change ((((r + 1 : ℕ) : ℝ) * ‖U‖ ^ 2) / 4) ≤
    (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
      (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
        (fun _ : Fin (r + 1) => (1 : ℝ)))) /
      (∑ j : Fin (r + 1), ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2)
  rw [fineRightKrylov_ones_coeff_sq_norm_eq, le_div_iff₀ hCount]
  calc
    (((r + 1 : ℕ) : ℝ) * ‖U‖ ^ 2) / 4 * ((r + 1 : ℕ) : ℝ) =
        (((((r + 1 : ℕ) : ℝ) ^ 2) * ‖U‖ ^ 2) / 4) := by ring
    _ ≤ _ := hGram

/-- When a genuinely positive ORIGINAL full-link top innovation persists,
there is NO coefficient-l2 upper Rayleigh bound independent of Krylov
depth for the uncentered original Wilson frozen posterior Gram.
This uses real all-one coefficients only and does not assert a
coercive lower bound in every coefficient direction. -/
theorem fineRightKrylovPairHaarResidualGram_no_uniformUpperRayleigh_of_top_nonzero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n : ℕ)
    (hTop :
      let H := halfExtent (n + 1)
      let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
      let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
      let I := physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
      0 < ‖WithLp.toLp 2
        (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (P u))‖) :
    ¬ ∃ K : ℝ, ∀ (r : ℕ) (a : Fin (r + 1) → ℝ),
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r) a) ≤
        K * (∑ j : Fin (r + 1), (a j) ^ 2) := by
  let H := halfExtent (n + 1)
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let U := WithLp.toLp 2
    (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (P u))
  have hU : 0 < ‖U‖ := hTop
  intro hFrame
  obtain ⟨K, hFrame⟩ := hFrame
  obtain ⟨N, hLinear⟩ :=
    fineRightKrylovPairHaarResidualGram_ones_eventually_normalizedRayleigh_ge_linearTop
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n hTop
  obtain ⟨r, hr, hStrict⟩ :=
    p4Q2AA_positive_top_slope_exceeds_any_frame_constant ‖U‖ K hU N
  have hLower := hLinear r hr
  have hUpperRaw := hFrame r (fun _ : Fin (r + 1) => (1 : ℝ))
  have hDenom :
      0 < (∑ j : Fin (r + 1), ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) := by
    rw [fineRightKrylov_ones_coeff_sq_norm_eq]
    positivity
  have hUpper :
      (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
          (fun _ : Fin (r + 1) => (1 : ℝ)))) /
        (∑ j : Fin (r + 1), ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) ≤
        K := by
    apply (div_le_iff₀ hDenom).mpr
    exact hUpperRaw
  have hLow : ((((r + 1 : ℕ) : ℝ) * ‖U‖ ^ 2) / 4) ≤
      (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
          (fun _ : Fin (r + 1) => (1 : ℝ)))) /
        (∑ j : Fin (r + 1), ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) := hLower
  exact (not_lt_of_ge (hLow.trans hUpper)) hStrict

/-- For any actual physical nonnegative coupling profile with positive
frozen Wilson beta, there is an open one-sided interval of SMALL POSITIVE
fine Wilson couplings on which the ORIGINAL uncentered posterior Gram
admits no depth-uniform coefficient-l2 upper Rayleigh bound.
The radius is finite-H/frozen-beta dependent, not universal. -/
theorem fineRightKrylovPairHaarResidualGram_exists_positiveFineWindow_no_uniformUpperRayleigh
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n : ℕ) (hFrozen : 0 < beta n) :
    ∃ delta : ℝ, 0 < delta ∧
      (beta (n + 1) < delta →
        ¬ ∃ K : ℝ, ∀ (r : ℕ) (a : Fin (r + 1) → ℝ),
          star a ⬝ᵥ (Matrix.mulVec
            (fineRightKrylovPairHaarResidualGram
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r) a) ≤
            K * (∑ j : Fin (r + 1), (a j) ^ 2)) := by
  let H := halfExtent (n + 1)
  obtain ⟨delta, hd, hWindow⟩ :=
    physicalOriginalFineTopProjection_fullLink_exists_positiveFineWindow
      H (beta n) hFrozen
  refine ⟨delta, hd, ?_⟩
  intro hFine
  have hTop :=
    hWindow (beta (n + 1)) (hbeta (n + 1)) hFine
  exact fineRightKrylovPairHaarResidualGram_no_uniformUpperRayleigh_of_top_nonzero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n hTop

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
