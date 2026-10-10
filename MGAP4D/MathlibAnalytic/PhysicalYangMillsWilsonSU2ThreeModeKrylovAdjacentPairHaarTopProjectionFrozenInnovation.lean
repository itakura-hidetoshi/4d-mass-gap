import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSpectralKrylovDecay
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroRankOne
import Mathlib.Tactic

/-!
# P4-Q2-Z: genuine Wilson top-projection innovation, first nonvanishing bridge

P4-Q2-Y proved spectral contraction of the ORIGINAL normalized Wilson
fine-right orbit to its *entire* top-eigenspace projection. This file
isolates the previously missing noncancellation issue.

1. For a real Hilbert operator S and its actual fixed-space projection P,
   the overlap error obeys (1-‖S-P‖)‖u-Pu‖ ≤ ‖u-Su‖.
2. At actual fine coupling beta=0, P_0 u_H = u_H exactly.
3. For frozen Wilson beta>0, there exists an ORIGINAL spatial link e with
   I_frozen,e(P_0 u_H) nonzero, without a new nonvanishing assumption.
4. For arbitrary physical fine beta≥0, a checkable spectral-gap-weighted
   physical one-step margin suffices for nonvanishing of I_frozen,e(P u_H).

The last point is a *conditional certificate*, not a claim that the margin
is satisfied at all positive fine couplings. No proxy posterior, changed
transfer, Dobrushin hypothesis, new axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 750000

/-- An overlap estimate for the genuine eigenvalue-one projection of an
arbitrary bounded real Hilbert operator. No rank-one top-space assumption:
the only input is the exact fixed-space projection identity S P = P. -/
theorem p4Q2Z_realHilbert_topProjection_overlap_gap_control
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E) (u : E) :
    (1 - ‖S - realHilbertTopEigenspaceProjection S‖) *
        ‖u - realHilbertTopEigenspaceProjection S u‖ ≤
      ‖u - S u‖ := by
  let P : E →L[ℝ] E := realHilbertTopEigenspaceProjection S
  let Z : E →L[ℝ] E := S - P
  have hSP : S * P = P := by
    change S.comp (realHilbertTopEigenspaceProjection S) =
      realHilbertTopEigenspaceProjection S
    exact realHilbertTopEigenspace_comp_projection S
  have hFix : S (P u) = P u := by
    have hApply := congrArg (fun T : E →L[ℝ] E => T u) hSP
    change S (P u) = P u at hApply
    exact hApply
  have hPP : P (P u) = P u :=
    (realHilbertTopEigenspaceProjection_apply_eq_self_iff S (P u)).mpr hFix
  have hPSub : P (u - P u) = 0 := by
    rw [map_sub, hPP, sub_self]
  have hZSub : Z (u - P u) = S u - P u := by
    dsimp [Z]
    rw [ContinuousLinearMap.sub_apply, map_sub, hFix, hPSub, sub_zero]
  have hDecomp : u - P u = (u - S u) + Z (u - P u) := by
    rw [hZSub]
    abel
  have hTri :
      ‖u - P u‖ ≤ ‖u - S u‖ + ‖Z (u - P u)‖ := by
    calc
      ‖u - P u‖ = ‖(u - S u) + Z (u - P u)‖ :=
        congrArg norm hDecomp
      _ ≤ ‖u - S u‖ + ‖Z (u - P u)‖ := norm_add_le _ _
  have hOperator : ‖Z (u - P u)‖ ≤ ‖Z‖ * ‖u - P u‖ :=
    ContinuousLinearMap.le_opNorm Z (u - P u)
  have hBound :
      ‖u - P u‖ ≤ ‖u - S u‖ + ‖Z‖ * ‖u - P u‖ :=
    le_trans hTri (add_le_add_left hOperator _)
  have hGap : (1 - ‖Z‖) * ‖u - P u‖ ≤ ‖u - S u‖ := by
    nlinarith
  simpa only [P, Z] using hGap

local instance p4ZTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4ZCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4ZSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4ZMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4ZBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4ZSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4ZRealHilbertComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- At fine Wilson beta zero the FULL physical top projection, not an
auxiliary rank-one substitute, fixes the actual Haar constant unit. -/
theorem physicalOriginalFineZeroTopSpectralProjection_constantUnit (H : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
        H 2 specialUnitaryTwoWilsonRankPositive 0 (by norm_num)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) =
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 := by
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive 0 (by norm_num)
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  have hFix : S u = u := by
    simpa [S, u] using
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_zero_constantUnit
        H 2 specialUnitaryTwoWilsonRankPositive)
  change realHilbertTopEigenspaceProjection S u = u
  exact (realHilbertTopEigenspaceProjection_apply_eq_self_iff S u).mpr hFix

/-- Unconditional nonvanishing of the ORIGINAL frozen Wilson signed
posterior innovation on the true fine-zero physical top component.
The frozen beta is strictly positive and distinct from fine beta zero. -/
theorem physicalOriginalFineZeroTopProjection_exists_nonzero_frozenLink
    (H : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen) :
    ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
      physicalOriginalReceiverPosteriorInnovation
          H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen) e
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
            H 2 specialUnitaryTwoWilsonRankPositive 0 (by norm_num)
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)) ≠ 0 := by
  obtain ⟨e, he⟩ :=
    physicalOriginalUnitReceiver_exists_positive_link_norm_SU2 H frozen hFrozen
  refine ⟨e, ?_⟩
  rw [physicalOriginalFineZeroTopSpectralProjection_constantUnit]
  exact norm_pos_iff.mp he

/-- For a genuine positive/zero fine beta, nonvanishing follows from
a quantitative one-step spectral-overlap certificate. Its coefficient
uses the ORIGINAL frozen posterior signed-Hilbert bound, not a proxy. -/
theorem physicalOriginalFineTopProjection_link_ne_zero_of_stepMargin
    (H : ℕ) (frozen fine : ℝ)
    (hFrozen : 0 < frozen) (hFine : 0 ≤ fine)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive fine hFine
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive fine hFine
    let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
    let I := physicalOriginalReceiverPosteriorInnovation
      H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)
    let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)
    Real.sqrt gamma * ‖S u - u‖ <
        (1 - ‖S - P‖) * ‖I e u‖ →
      I e (P u) ≠ 0 := by
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive fine hFine
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive fine hFine
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)
  intro hMargin
  have hq : ‖S - P‖ < 1 := by
    exact physicalOriginalNormalizedFineTransfer_sub_topSpectralProjection_norm_lt_one
      H fine hFine
  have hdelta : 0 < 1 - ‖S - P‖ := sub_pos.mpr hq
  have hOverlap :
      (1 - ‖S - P‖) * ‖P u - u‖ ≤ ‖S u - u‖ := by
    simpa only [S, P, norm_sub_rev] using
      (p4Q2Z_realHilbert_topProjection_overlap_gap_control S u)
  have hCoefficient : 0 ≤ Real.sqrt gamma := Real.sqrt_nonneg _
  have hStrict :
      Real.sqrt gamma * ‖P u - u‖ < ‖I e u‖ := by
    apply (mul_lt_mul_left hdelta).mp
    calc
      (1 - ‖S - P‖) * (Real.sqrt gamma * ‖P u - u‖) =
          Real.sqrt gamma * ((1 - ‖S - P‖) * ‖P u - u‖) := by ring
      _ ≤ Real.sqrt gamma * ‖S u - u‖ :=
        mul_le_mul_of_nonneg_left hOverlap hCoefficient
      _ < (1 - ‖S - P‖) * ‖I e u‖ := hMargin
  have hSub :=
    physicalOriginalReceiverPosteriorInnovation_sub
      H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)
      e (P u) u
  change I e (P u) - I e u = I e (P u - u) at hSub
  have hLip :=
    physicalOriginalReceiverPosteriorInnovation_norm_le_sqrt_signedHilbert
      H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)
      e (P u - u)
  change ‖I e (P u - u)‖ ≤ Real.sqrt gamma * ‖P u - u‖ at hLip
  have hBound :
      ‖I e (P u) - I e u‖ ≤ Real.sqrt gamma * ‖P u - u‖ := by
    calc
      ‖I e (P u) - I e u‖ = ‖I e (P u - u)‖ := congrArg norm hSub
      _ ≤ Real.sqrt gamma * ‖P u - u‖ := hLip
  intro hZero
  have hUnit :
      ‖I e u‖ = ‖I e (P u) - I e u‖ := by
    rw [hZero]
    simp
  have hFalse :
      ‖I e u‖ ≤ Real.sqrt gamma * ‖P u - u‖ :=
    hUnit.trans_le hBound
  exact (not_lt_of_ge hFalse) hStrict

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
