import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGramTopGeometricRayleigh
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-AA3: actual Wilson positive-fine top innovation gives depth growth

The true ORIGINAL frozen posterior all-link receiver U is known nonzero
on a one-sided positive fine Wilson interval (Z2). The AA2 Gram margin
then becomes a quadratic all-one lower bound for all large Krylov depths:
  onesᵀ G_original(r) ones >= (r+1)² ‖U‖²/4,
provided (r+1) ‖U‖ >= 2C/(1-q).
The depth threshold exists for every fixed finite H and physical
profile with ‖U‖>0. No volume-independent threshold and no continuum
mass gap or false full-coefficient coercivity are claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 850000

/-- Scalar quarter-margin bound: under a concrete depth condition,
the geometric receiver error leaves at least half the top signal. -/
theorem p4Q2AA_quarter_square_le_margin_sq
    (N a E : ℝ) (hN : 0 ≤ N) (ha : 0 ≤ a)
    (hDepth : 2 * E ≤ N * a) :
    (N ^ 2 * a ^ 2) / 4 ≤ (N*a-E) ^ 2 := by
  have hHalf : 0 ≤ N*a/2 := by positivity
  have hHalfLe : N*a/2 ≤ N*a-E := by linarith
  have hProd : 0 ≤ ((N*a-E) - N*a/2) * ((N*a-E) + N*a/2) :=
    mul_nonneg (sub_nonneg.mpr hHalfLe)
      (add_nonneg (by linarith) hHalf)
  nlinarith [hProd]

/-- Any strictly positive top signal eventually dominates twice a
fixed nonnegative geometric error budget. No uniformity over volume. -/
theorem p4Q2AA_exists_depth_linear_signal_dominates_error
    (a E : ℝ) (ha : 0 < a) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r →
      2 * E ≤ (((r+1:ℕ):ℝ) * a) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * E / a)
  refine ⟨N, ?_⟩
  intro r hr
  have hNreal : 2 * E < (N : ℝ) * a :=
    (div_lt_iff₀ ha).mp hN
  have hCast : (N : ℝ) ≤ ((r+1:ℕ):ℝ) := by
    exact_mod_cast (Nat.le_succ_of_le hr)
  have hDiffNonneg : 0 ≤ (((r+1:ℕ):ℝ) - (N : ℝ)) :=
    sub_nonneg.mpr hCast
  have hMulNonneg : 0 ≤ ((((r+1:ℕ):ℝ) - (N : ℝ)) * a) :=
    mul_nonneg hDiffNonneg (le_of_lt ha)
  nlinarith

local instance p4AA3Group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4AA3Compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4AA3SecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4AA3Measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4AA3Borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4AA3LinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4AA3HilbertComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- A single nonzero genuine frozen signed posterior link at P_fine u_H
forces strictly positive norm of the ORIGINAL full spatial-link PiLp 2
top innovation. No substitute receiver or link averaging. -/
theorem physicalOriginalFineTopProjection_fullLink_norm_pos_of_nonzero_link
    (H : ℕ) (frozen fine : ℝ)
    (hFrozen : 0 < frozen) (hFine : 0 ≤ fine)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (he :
      physicalOriginalReceiverPosteriorInnovation H 2
        specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen) e
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
          H 2 specialUnitaryTwoWilsonRankPositive fine hFine
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)) ≠ 0) :
    0 < ‖WithLp.toLp 2 (fun link : PeriodicHypercubicEvenSpatialSliceLink H =>
      physicalOriginalReceiverPosteriorInnovation H 2
        specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen) link
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
          H 2 specialUnitaryTwoWilsonRankPositive fine hFine
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)))‖ := by
  let U := WithLp.toLp 2 (fun link : PeriodicHypercubicEvenSpatialSliceLink H =>
      physicalOriginalReceiverPosteriorInnovation H 2
        specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen) link
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
          H 2 specialUnitaryTwoWilsonRankPositive fine hFine
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)))
  change 0 < ‖U‖
  have hUne : U ≠ 0 := by
    intro hz
    have hCoord : U e = 0 := by rw [hz]; simp
    exact he hCoord
  exact norm_pos_iff.mpr hUne

/-- The positive-fine OPEN interval of Z2 has a strictly positive
ORIGINAL all-link top innovation norm, not merely a one-link statement. -/
theorem physicalOriginalFineTopProjection_fullLink_exists_positiveFineWindow
    (H : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (fine : ℝ) (hFine : 0 ≤ fine), fine < delta →
        0 < ‖WithLp.toLp 2
          (fun link : PeriodicHypercubicEvenSpatialSliceLink H =>
            physicalOriginalReceiverPosteriorInnovation H 2
              specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen) link
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
                H 2 specialUnitaryTwoWilsonRankPositive fine hFine
                (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)))‖ := by
  obtain ⟨e, delta, hd, hWindow⟩ :=
    physicalOriginalFineTopProjection_exists_positiveFineWindow H frozen hFrozen
  refine ⟨delta, hd, ?_⟩
  intro fine hFine hLt
  exact physicalOriginalFineTopProjection_fullLink_norm_pos_of_nonzero_link
    H frozen fine hFrozen hFine e (hWindow fine hFine hLt)

/-- For the ACTUAL frozen Wilson all-link original posterior Gram,
the all-one Rayleigh numerator grows quadratically with Krylov depth
whenever the depth has overcome twice the geometric error C/(1-q).
Its coefficient is the SQUARED true physical top innovation norm. -/
theorem fineRightKrylovPairHaarResidualGram_ones_ge_quarter_topDepth
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ)
    (hDepth :
      let H := halfExtent (n+1)
      let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
      let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
      let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
      let I := physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
      let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
      let B := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n+1))
      let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
      let C := (Real.sqrt gamma * B) * Real.sqrt L + Real.sqrt gamma * Real.sqrt L
      let U := WithLp.toLp 2
        (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (P u))
      2 * (C/(1-‖S-P‖)) ≤ (((r+1:ℕ):ℝ) * ‖U‖)) :
    let H := halfExtent (n+1)
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
    let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
    let I := physicalOriginalReceiverPosteriorInnovation
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let U := WithLp.toLp 2
      (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (P u))
    ((((r+1:ℕ):ℝ)^2) * ‖U‖^2) / 4 ≤
      star (fun _ : Fin (r+1) => (1:ℝ)) ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
          (fun _ : Fin (r+1) => (1:ℝ))) := by
  let H := halfExtent (n+1)
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let B := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n+1))
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  let C := (Real.sqrt gamma * B) * Real.sqrt L + Real.sqrt gamma * Real.sqrt L
  let U := WithLp.toLp 2
    (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (P u))
  let N : ℝ := ((r+1:ℕ):ℝ)
  let E : ℝ := C / (1-‖S-P‖)
  change 2*E ≤ N*‖U‖ at hDepth
  have hMargin : 0 ≤ N*‖U‖ - E := by linarith
  have hGram :=
    fineRightKrylovPairHaarResidualGram_ones_rayleigh_ge_topGeometricMargin
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hMargin
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hScalar :=
    p4Q2AA_quarter_square_le_margin_sq N ‖U‖ E hN (norm_nonneg U) hDepth
  change (N^2*‖U‖^2)/4 ≤ _
  exact le_trans hScalar hGram

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
