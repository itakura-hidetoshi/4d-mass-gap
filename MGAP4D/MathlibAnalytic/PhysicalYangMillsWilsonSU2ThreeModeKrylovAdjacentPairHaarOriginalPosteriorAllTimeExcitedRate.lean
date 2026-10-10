import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalExcitedTransferBridge
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-AI: all-time physical Wilson excited transfer and ORIGINAL posterior

AF4 proved that the real centered Krylov source F_a belongs to the
excited sector for the ACTUAL normalized positive-fine Wilson transfer S:
  P_fine F_a = 0, ||S F_a|| <= q ||F_a||, q = ||S-P_fine|| < 1.

Here we prove for EVERY natural iteration k:
  ||S^k F_a|| <= q^k ||F_a||.
The original frozen-beta signed Wilson innovation at EACH actual link,
and hence its ORIGINAL all-link PiLp 2 receiver, has squared energy
bounded by the true frozen signed Hilbert coefficient times
the number of spatial links times (q^k ||F_a||)^2.

For positive q and physical lattice spacing a, the exact rate condition
  m <= -log(q)/a
is equivalent to
  q <= exp(-m*a).
The latter yields spacing-scaled decay even if q = 0; the theorem NEVER
assumes or claims any positive H-uniform / a-uniform mass m.

Crucial carrier separation: the Wilson transfer acts on the physical
source Haar L2; the ORIGINAL frozen posterior innovation maps that source
to the pair-Haar all-link receiver. We do NOT define or apply a surrogate
transfer on the receiver space. No Dobrushin, proxy posterior/Gram,
sorry/admit/new axioms, or continuum Yang--Mills gap assertion.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 850000

/-- Every iterate of a symmetric real Hilbert transfer contracts vectors
in its ACTUAL full-top-orthogonal excitation carrier by q^k. -/
theorem p4Q2AI_realHilbert_excited_transferPow_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    (hSym : (S : E →ₗ[ℝ] E).IsSymmetric)
    (x : E)
    (hZero : realHilbertTopEigenspaceProjection S x = 0)
    (k : ℕ) :
    ‖(S ^ k) x‖ ≤
      ‖S - realHilbertTopEigenspaceProjection S‖ ^ k * ‖x‖ := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hZeroK : realHilbertTopEigenspaceProjection S ((S ^ k) x) = 0 :=
        (p4Q2AH_realHilbert_topProjection_transferPower S hSym k x).trans hZero
      have hOne :=
        p4Q2AH_realHilbert_excited_transfer_norm_le S ((S ^ k) x) hZeroK
      have hPower : (S ^ (k + 1)) x = S ((S ^ k) x) := by
        rw [pow_succ']
        rfl
      calc
        ‖(S ^ (k + 1)) x‖ = ‖S ((S ^ k) x)‖ :=
          congrArg norm hPower
        _ ≤ ‖S - realHilbertTopEigenspaceProjection S‖ * ‖(S ^ k) x‖ := hOne
        _ ≤ ‖S - realHilbertTopEigenspaceProjection S‖ *
            (‖S - realHilbertTopEigenspaceProjection S‖ ^ k * ‖x‖) :=
          mul_le_mul_of_nonneg_left ih (norm_nonneg _)
        _ = ‖S - realHilbertTopEigenspaceProjection S‖ ^ (k + 1) * ‖x‖ := by
          rw [pow_succ']
          ring

/-- For positive q and lattice spacing a, exactly the spacing-scaled
negative logarithmic rate appears; no rate limit is presupposed. -/
theorem p4Q2AI_positiveFactor_spacingRate_iff_exp
    (q spacing mass : ℝ)
    (hq : 0 < q) (hspacing : 0 < spacing) :
    mass ≤ -Real.log q / spacing ↔
      q ≤ Real.exp (-mass * spacing) := by
  constructor
  · intro hrate
    have hmul : mass * spacing ≤ -Real.log q :=
      (le_div_iff₀ hspacing).mp hrate
    apply (Real.log_le_iff_le_exp hq).mp
    nlinarith
  · intro hstep
    have hlog : Real.log q ≤ -mass * spacing :=
      (Real.log_le_iff_le_exp hq).mpr hstep
    apply (le_div_iff₀ hspacing).mpr
    nlinarith

/-- A certified physical one-step spacing-scaled bound propagates to
all integer lattice times. It is a conditional statement about the
ACTUAL transfer norm (not an assumed continuum mass gap). -/
theorem p4Q2AI_realHilbert_excited_transferPow_spacingRate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    (hSym : (S : E →ₗ[ℝ] E).IsSymmetric)
    (x : E)
    (hZero : realHilbertTopEigenspaceProjection S x = 0)
    (spacing mass : ℝ)
    (hStep :
      ‖S - realHilbertTopEigenspaceProjection S‖ ≤
        Real.exp (-mass * spacing))
    (k : ℕ) :
    ‖(S ^ k) x‖ ≤
      Real.exp ((k : ℝ) * (-mass * spacing)) * ‖x‖ := by
  have hp :
      ‖S - realHilbertTopEigenspaceProjection S‖ ^ k ≤
        (Real.exp (-mass * spacing)) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) hStep k
  calc
    ‖(S ^ k) x‖ ≤
        ‖S - realHilbertTopEigenspaceProjection S‖ ^ k * ‖x‖ :=
      p4Q2AI_realHilbert_excited_transferPow_norm_le S hSym x hZero k
    _ ≤ (Real.exp (-mass * spacing)) ^ k * ‖x‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg x)
    _ = Real.exp ((k : ℝ) * (-mass * spacing)) * ‖x‖ := by
      rw [← Real.exp_nat_mul]

local instance p4AIGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4AICompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4AISecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4AIMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4AIBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4AILinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4AIComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- The original fine Wilson excited physical source contracts at ALL
integer powers, not only for a single transfer step. -/
theorem fineRightKrylov_originalWilson_centeredSource_transferPow_norm_le
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (hCenter : (∑ j : Fin (r + 1), a j) = 0)
    (k : ℕ) :
    let H := halfExtent (n + 1)
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let F := fineRightKrylovOriginalSignedPhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
    ‖(S ^ k) F‖ ≤ ‖S - P‖ ^ k * ‖F‖ ∧ ‖S - P‖ < 1 := by
  let H := halfExtent (n + 1)
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let F := fineRightKrylovOriginalSignedPhysicalSource
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hExc := fineRightKrylov_originalWilson_centeredPhysicalSource_excitedTransfer
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a hCenter
  have hSym :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  have hBound : ‖(S ^ k) F‖ ≤ ‖S - P‖ ^ k * ‖F‖ :=
    p4Q2AI_realHilbert_excited_transferPow_norm_le S hSym F hExc.1 k
  exact ⟨hBound, hExc.2.2⟩

/-- Genuine frozen signed Wilson posterior all-spatial-link innovation
of a centered physical source evolved by k REAL fine-Wilson steps.
The receiver is not treated as the domain of S. -/
theorem fineRightKrylov_originalWilson_excitedTransferPow_posteriorFullLink_norm_sq_le
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (hCenter : (∑ j : Fin (r + 1), a j) = 0)
    (k : ℕ) :
    let H := halfExtent (n + 1)
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let F := fineRightKrylovOriginalSignedPhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
    let I := physicalOriginalReceiverPosteriorInnovation
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    ‖WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
        I e ((S ^ k) F))‖ ^ 2 ≤
      ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * gamma) *
        (‖S - P‖ ^ k * ‖F‖) ^ 2 := by
  classical
  let H := halfExtent (n + 1)
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let F := fineRightKrylovOriginalSignedPhysicalSource
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  have hGamma : 0 ≤ gamma :=
    originalWilsonPhysicalSignedInnovationHilbertCoefficient_nonneg
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  have hCoefNonneg :
      0 ≤ (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * gamma :=
    mul_nonneg (Nat.cast_nonneg _) hGamma
  have hPower : ‖(S ^ k) F‖ ≤ ‖S - P‖ ^ k * ‖F‖ :=
    (fineRightKrylov_originalWilson_centeredSource_transferPow_norm_le
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a hCenter k).1
  have hLeftNonneg : 0 ≤ ‖(S ^ k) F‖ :=
    norm_nonneg ((S ^ k) F)
  have hRightNonneg : 0 ≤ ‖S - P‖ ^ k * ‖F‖ :=
    mul_nonneg (pow_nonneg (norm_nonneg (S - P)) k) (norm_nonneg F)
  have hPowerSq :
      ‖(S ^ k) F‖ ^ 2 ≤ (‖S - P‖ ^ k * ‖F‖) ^ 2 :=
    (sq_le_sq₀ hLeftNonneg hRightNonneg).mpr hPower
  have hOne (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      ‖I e ((S ^ k) F)‖ ^ 2 ≤ gamma * ‖(S ^ k) F‖ ^ 2 := by
    exact physicalOriginalReceiverPosteriorInnovation_norm_sq_le_signedHilbert
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e ((S ^ k) F)
  change ‖WithLp.toLp 2
      (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e ((S ^ k) F))‖ ^ 2 ≤
    ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * gamma) *
      (‖S - P‖ ^ k * ‖F‖) ^ 2
  calc
    ‖WithLp.toLp 2
        (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e ((S ^ k) F))‖ ^ 2 =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖I e ((S ^ k) F)‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        rfl
    _ ≤ ∑ _e : PeriodicHypercubicEvenSpatialSliceLink H,
        gamma * ‖(S ^ k) F‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro e _he
        exact hOne e
    _ = ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * gamma) *
        ‖(S ^ k) F‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ ≤ ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * gamma) *
        (‖S - P‖ ^ k * ‖F‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hPowerSq hCoefNonneg

/-- Physical Wilson all-time source decay with explicit spacing-scaled
rate as a verifiable one-step assumption; this does not assert that any
mass/spacing bound has been established uniformly in volume. -/
theorem fineRightKrylov_originalWilson_centeredSource_spacingRate_of_certifiedStep
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (hCenter : (∑ j : Fin (r + 1), a j) = 0)
    (spacing mass : ℝ)
    (hStep :
      let H := halfExtent (n + 1)
      let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
      let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
      ‖S - P‖ ≤ Real.exp (-mass * spacing))
    (k : ℕ) :
    let H := halfExtent (n + 1)
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let F := fineRightKrylovOriginalSignedPhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
    ‖(S ^ k) F‖ ≤ Real.exp ((k : ℝ) * (-mass * spacing)) * ‖F‖ := by
  let H := halfExtent (n + 1)
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let F := fineRightKrylovOriginalSignedPhysicalSource
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hExc :=
    fineRightKrylov_originalWilson_centeredPhysicalSource_excitedTransfer
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a hCenter
  have hSym :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  exact p4Q2AI_realHilbert_excited_transferPow_spacingRate
    S hSym F hExc.1 spacing mass hStep k

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
