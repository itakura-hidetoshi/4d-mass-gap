import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFineRadiusDepthVolumeSeparation
import Mathlib.Tactic

/-!
# P4-Q2-W: strictly positive original Wilson physical depth-loss coefficient

The P4-Q2-U/V sufficient fine-coupling radius is

    delta(H,r,b) = min(1, R(H,b)/(1+r*Q(H,b))),

where R(H,b) = sqrt(E_unit(b,H)) > 0 and the PHYSICAL coefficient is
    Q(H,b) = sqrt(L_H) * sqrt(gamma(b,H)) * C_H,
    C_H = 2*exp(A_H)*A_H.

Here L_H is the original number of spatial links, A_H is the genuine
finite-volume Wilson one-slab action budget, and gamma is the original
signed posterior innovation Hilbert coefficient.

At all finite H and strictly positive frozen b we prove:
1. A_H>0 using actual Wilson spatial links and canonical slab lists.
2. gamma(b,H)>0 using the true transfer-operator norm positivity and
   the already-proved exact signed Hilbert factorization.
3. Therefore Q(H,b)>0, and the true R/Q ratio is positive.
4. The P4-Q2-U *sufficient certificate* radius shrinks below every
   positive epsilon at sufficiently large Krylov depth, without an
   additional Q>0 assumption.
5. Any positive depth-uniform candidate epsilon below this sufficient
   radius obeys r*epsilon <= R(H,b)/Q(H,b).

This is NOT a no-go theorem for the genuine Wilson posterior Gram or
Yang--Mills mass gap: it isolates a limitation of a particular
telescoping O(r)-error certificate, not of the actual operator spectrum.
Neither volume-uniform bounds for R/Q nor continuum statements follow.
No Dobrushin, proxy posterior/transfer, new axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4WGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4WCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4WSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4WMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4WBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4WLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The canonical Wilson spatial-link list is nonempty at every
finite H: we extract an actual spatial link from the strictly positive
original frozen Wilson unit receiver. In particular the genuine slab
action budget A_H is strictly positive. -/
theorem physicalOriginalOneSlabGlobalActionBudget_pos_SU2
    (H : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H := by
  classical
  obtain ⟨e, _he⟩ :=
    physicalOriginalUnitReceiver_exists_positive_link_norm_SU2 H frozen hFrozen
  have hMem : e ∈ periodicHypercubicEvenSpatialSliceLinkList H :=
    periodicHypercubicEvenSpatialSliceLink_mem_list H e
  have hLinkList :
      0 < (periodicHypercubicEvenSpatialSliceLinkList H).length := by
    cases hList : periodicHypercubicEvenSpatialSliceLinkList H with
    | nil => simp [hList] at hMem
    | cons a as => simp
  have hVolume :
      0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume H := by
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume
    omega
  change 0 < (2 : ℝ) *
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume H : ℝ)
  exact mul_pos (by norm_num) (Nat.cast_pos.mpr hVolume)

/-- The original signed Wilson posterior Hilbert coefficient is
STRICTLY positive at positive frozen coupling, without assuming a
proxy transfer or forcing pointwise signs for signed innovations. -/
theorem originalWilsonPhysicalSignedInnovationHilbertCoefficient_pos_SU2
    (H : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen) :
    0 < originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen) := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)
  have hNorm : 0 < ‖T‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)
  have hInv : 0 < ‖T‖⁻¹ := inv_pos.mpr hNorm
  have hExp : 1 < Real.exp (8 * frozen) := by
    have hb8 : (0 : ℝ) < 8 * frozen := by positivity
    have h := Real.exp_lt_exp.mpr hb8
    simpa only [Real.exp_zero] using h
  have hDiff : 0 < Real.exp (8 * frozen) - 1 := by linarith
  have hFactor :=
    originalWilsonPhysicalSignedInnovationHilbertCoefficient_factor
      H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)
  change originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen) =
      (Real.exp (8 * frozen) - 1) ^ 2 * (‖T‖⁻¹) ^ 2 *
        (1 + Real.exp (8 * frozen) ^ 2 *
          (Real.exp (8 * frozen) + 1) ^ 2 * (‖T‖⁻¹) ^ 2) at hFactor
  rw [hFactor]
  have hFirst :
      0 < (Real.exp (8 * frozen) - 1) ^ 2 * (‖T‖⁻¹) ^ 2 :=
    mul_pos (sq_pos_of_pos hDiff) (sq_pos_of_pos hInv)
  have hSecond :
      0 < 1 + Real.exp (8 * frozen) ^ 2 *
        (Real.exp (8 * frozen) + 1) ^ 2 * (‖T‖⁻¹) ^ 2 := by
    positivity
  exact mul_pos hFirst hSecond

/-- Q_{H,b}, the certified full-link transfer-error coefficient, is
the actual physical expression and not a free abstract parameter. -/
noncomputable def physicalOriginalGlobalQuarterEnergyPhysicalDepthLoss
    (H : ℕ) (frozen : ℝ) (hFrozen : 0 ≤ frozen) : ℝ :=
  (Real.sqrt (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
    Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H 2 specialUnitaryTwoWilsonRankPositive frozen hFrozen)) *
    physicalOriginalNormalizedTransferExpActionLinearConstant H

/-- At every finite physical Wilson volume H and positive frozen b,
Q_{H,b} is STRICTLY POSITIVE: the conditional Q>0 used in P4-Q2-V
is automatically fulfilled for the genuine original Wilson model. -/
theorem physicalOriginalGlobalQuarterEnergyPhysicalDepthLoss_pos
    (H : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen) :
    0 < physicalOriginalGlobalQuarterEnergyPhysicalDepthLoss
      H frozen (le_of_lt hFrozen) := by
  classical
  obtain ⟨e, _he⟩ :=
    physicalOriginalUnitReceiver_exists_positive_link_norm_SU2 H frozen hFrozen
  have hCard :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) := by
    apply Finset.card_pos.mpr
    exact ⟨e, Finset.mem_univ e⟩
  have hL : (0 : ℝ) <
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) :=
    Nat.cast_pos.mpr hCard
  have hGamma :=
    originalWilsonPhysicalSignedInnovationHilbertCoefficient_pos_SU2
      H frozen hFrozen
  have hA := physicalOriginalOneSlabGlobalActionBudget_pos_SU2
    H frozen hFrozen
  have hC : 0 < physicalOriginalNormalizedTransferExpActionLinearConstant H := by
    unfold physicalOriginalNormalizedTransferExpActionLinearConstant
    exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) hA
  unfold physicalOriginalGlobalQuarterEnergyPhysicalDepthLoss
  exact mul_pos
    (mul_pos (Real.sqrt_pos.mpr hL) (Real.sqrt_pos.mpr hGamma)) hC

/-- The ratio of the true full-link positive-energy radius to its
positive physical depth-loss coefficient. No volume-uniform estimate
of this ratio is presumed. -/
noncomputable def physicalOriginalGlobalQuarterEnergyDepthHorizonRatio
    (H : ℕ) (frozen : ℝ) (hFrozen : 0 ≤ frozen) : ℝ :=
  Real.sqrt (physicalOriginalUnitReceiverFullLinkEnergy
    H 2 specialUnitaryTwoWilsonRankPositive frozen hFrozen) /
    physicalOriginalGlobalQuarterEnergyPhysicalDepthLoss H frozen hFrozen

theorem physicalOriginalGlobalQuarterEnergyDepthHorizonRatio_pos
    (H : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen) :
    0 < physicalOriginalGlobalQuarterEnergyDepthHorizonRatio
      H frozen (le_of_lt hFrozen) := by
  unfold physicalOriginalGlobalQuarterEnergyDepthHorizonRatio
  apply div_pos
  · exact Real.sqrt_pos.mpr
      (physicalOriginalUnitReceiverFullLinkEnergy_pos_of_beta_pos_SU2
        H frozen hFrozen)
  · exact physicalOriginalGlobalQuarterEnergyPhysicalDepthLoss_pos
      H frozen hFrozen

/-- A genuine physical Q>0 unconditional version of P4-Q2-V's
eventual-smallness result at positive frozen beta. The conclusion
concerns the particular P4-Q2-U sufficient radius only. -/
theorem physicalOriginalGlobalQuarterEnergyExplicitFineRadius_eventually_below_of_positiveFrozen
    (H : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r →
      physicalOriginalGlobalQuarterEnergyExplicitFineRadius
        H r frozen (le_of_lt hFrozen) < epsilon := by
  exact physicalOriginalGlobalQuarterEnergyExplicitFineRadius_eventually_below
    H frozen hFrozen
    (physicalOriginalGlobalQuarterEnergyPhysicalDepthLoss_pos H frozen hFrozen)
    epsilon hEpsilon

/-- The maximum depth certified by any fixed positive radius floor
is bounded in terms of the true physical ratio R(H,b)/Q(H,b):
epsilon*r ≤ R/Q. This does NOT bound true Gram positivity at depth r. -/
theorem physicalOriginalGlobalQuarterEnergyExplicitFineRadius_floor_depth_le_horizonRatio
    (H r : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon)
    (hFloor :
      epsilon ≤ physicalOriginalGlobalQuarterEnergyExplicitFineRadius
        H r frozen (le_of_lt hFrozen)) :
    (r : ℝ) * epsilon ≤
      physicalOriginalGlobalQuarterEnergyDepthHorizonRatio
        H frozen (le_of_lt hFrozen) := by
  let Q := physicalOriginalGlobalQuarterEnergyPhysicalDepthLoss
    H frozen (le_of_lt hFrozen)
  let R := Real.sqrt (physicalOriginalUnitReceiverFullLinkEnergy
    H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen))
  have hQ : 0 < Q :=
    physicalOriginalGlobalQuarterEnergyPhysicalDepthLoss_pos H frozen hFrozen
  have hBudget :=
    physicalOriginalGlobalQuarterEnergyExplicitFineRadius_floor_forces_budget
      H r frozen hFrozen epsilon (le_of_lt hEpsilon) hFloor
  have hBudget' : epsilon * ((r : ℝ) * Q) ≤ R := hBudget
  have hCross : ((r : ℝ) * epsilon) * Q ≤ R := by
    calc
      ((r : ℝ) * epsilon) * Q = epsilon * ((r : ℝ) * Q) := by ring
      _ ≤ R := hBudget'
  change ((r : ℝ) * epsilon) ≤ R / Q
  exact (le_div_iff₀ hQ).mpr hCross

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
