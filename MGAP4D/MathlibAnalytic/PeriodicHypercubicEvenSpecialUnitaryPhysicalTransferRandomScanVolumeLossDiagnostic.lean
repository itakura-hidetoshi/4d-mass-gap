import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBoundedColorCoercivity
import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinRandomScanScale
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

set_option maxHeartbeats 1000000

/-!
# Random-scan volume loss versus bounded-color physical coercivity

The current repository contains two mathematically different finite-volume
mechanisms:

* the exact Wilson single-link/Dobrushin heat-bath lane, whose canonical
discrete random-scan operator averages over every lattice edge; and
* the bounded-color physical-transfer bridge, whose purpose is precisely to
avoid dividing a coercive estimate by the number of lattice sites/edges.

This file records the normalization distinction theoremically.  It does not
identify the heat-bath operator with the physical one-slab transfer and it does
not promote the Dobrushin lane to a physical gap theorem.

The important output is that the canonical random-scan separation is exactly
`(1 - α) / |E|`, while a bounded-color normalized residual estimate with a
volume-independent coefficient requires the *unnormalized* residual sum to be
of order `|C|` times the squared norm.  Thus a sitewise random scan cannot by
normalization alone discharge the model-facing bounded-color comparison from
`PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBoundedColorCoercivity`.
-/

/-- The discrete Dobrushin random-scan separation is exactly the heat-bath
coercivity divided by the number of edges.  This is the pointwise form of the
normalization identity and makes the volume factor explicit. -/
theorem finite_lattice_one_sub_dobrushinRandomScanRate_eq
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L) :
    1 - finiteLatticeWilsonDobrushinRandomScanRate L D =
      finiteLatticeWilsonDobrushinHeatBathGap D /
        (Fintype.card L.Edge : ℝ) := by
  unfold finiteLatticeWilsonDobrushinRandomScanRate
  ring

/-- The Dobrushin heat-bath coercivity lies in `(0,1]`. -/
theorem finite_lattice_dobrushinHeatBathGap_le_one
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonDobrushinMatrixData L) :
    finiteLatticeWilsonDobrushinHeatBathGap D ≤ 1 := by
  unfold finiteLatticeWilsonDobrushinHeatBathGap
  linarith [D.dobrushinCoefficient_nonneg]

/-- Consequently, for a nonempty finite edge set, the discrete random-scan gap
is bounded above by `1 / |E|`, independently of how favorable the strict
Dobrushin coefficient is. -/
theorem finite_lattice_one_sub_dobrushinRandomScanRate_le_edgeCard_inv
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    1 - finiteLatticeWilsonDobrushinRandomScanRate L D ≤
      1 / (Fintype.card L.Edge : ℝ) := by
  have hCardPos : (0 : ℝ) < (Fintype.card L.Edge : ℝ) :=
    Nat.cast_pos.mpr hEdge
  rw [finite_lattice_one_sub_dobrushinRandomScanRate_eq L D]
  exact (div_le_div_iff_of_pos_right hCardPos).2
    (finite_lattice_dobrushinHeatBathGap_le_one D)

/-- The random-scan separation can be made smaller than any prescribed
positive threshold as soon as the reciprocal edge count is below that
threshold.  This is a finite, assumption-transparent diagnostic; no asymptotic
claim about the actual physical transfer is made. -/
theorem finite_lattice_one_sub_dobrushinRandomScanRate_lt_of_edgeCard_inv_lt
    (L : FiniteLatticeWilsonSystem)
    (D : FiniteLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (ε : ℝ)
    (hInv : 1 / (Fintype.card L.Edge : ℝ) < ε) :
    1 - finiteLatticeWilsonDobrushinRandomScanRate L D < ε :=
  lt_of_le_of_lt
    (finite_lattice_one_sub_dobrushinRandomScanRate_le_edgeCard_inv
      L D hEdge)
    hInv

/-- An unnormalized residual-sum lower bound loses exactly one factor of the
color cardinality when converted to the normalized bounded-color energy.

This theorem is generic because the normalization issue is independent of the
Wilson model. -/
theorem boundedColorNormalizedResidualEnergy_lower_bound_of_sum
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    [Nonempty C]
    (P : C → E →L[ℝ] E)
    (κ : ℝ)
    (x : E)
    (hsum :
      κ * ‖x‖ ^ 2 ≤ ∑ c : C, ‖x - P c x‖ ^ 2) :
    (κ / (Fintype.card C : ℝ)) * ‖x‖ ^ 2 ≤
      boundedColorNormalizedResidualEnergy P x := by
  have hCardNat : 0 < Fintype.card C := Fintype.card_pos_iff.mpr inferInstance
  have hCardPos : (0 : ℝ) < (Fintype.card C : ℝ) := Nat.cast_pos.mpr hCardNat
  have hInvNonneg :
      0 ≤ ((Fintype.card C : ℝ)⁻¹) := le_of_lt (inv_pos.mpr hCardPos)
  have hscaled := mul_le_mul_of_nonneg_left hsum hInvNonneg
  unfold boundedColorNormalizedResidualEnergy
  calc
    (κ / (Fintype.card C : ℝ)) * ‖x‖ ^ 2 =
        ((Fintype.card C : ℝ)⁻¹) * (κ * ‖x‖ ^ 2) := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ ((Fintype.card C : ℝ)⁻¹) *
        (∑ c : C, ‖x - P c x‖ ^ 2) := hscaled

/-- Conversely, a normalized bounded-color frame estimate of strength `κ`
forces the unnormalized residual sum to carry the linearly scaled strength
`|C| * κ`.

This is the exact algebraic target that a parallel block/color construction
must satisfy if `κ` is to remain uniform while the underlying lattice volume
grows. -/
theorem boundedColor_sum_lower_bound_of_normalizedResidualEnergy
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    [Nonempty C]
    (P : C → E →L[ℝ] E)
    (κ : ℝ)
    (x : E)
    (hframe :
      κ * ‖x‖ ^ 2 ≤ boundedColorNormalizedResidualEnergy P x) :
    ((Fintype.card C : ℝ) * κ) * ‖x‖ ^ 2 ≤
      ∑ c : C, ‖x - P c x‖ ^ 2 := by
  have hCardNat : 0 < Fintype.card C := Fintype.card_pos_iff.mpr inferInstance
  have hCardPos : (0 : ℝ) < (Fintype.card C : ℝ) := Nat.cast_pos.mpr hCardNat
  have hscaled := mul_le_mul_of_nonneg_left hframe (le_of_lt hCardPos)
  unfold boundedColorNormalizedResidualEnergy at hscaled
  calc
    ((Fintype.card C : ℝ) * κ) * ‖x‖ ^ 2 =
        (Fintype.card C : ℝ) * (κ * ‖x‖ ^ 2) := by ring
    _ ≤ (Fintype.card C : ℝ) *
        (((Fintype.card C : ℝ)⁻¹) *
          ∑ c : C, ‖x - P c x‖ ^ 2) := hscaled
    _ = ∑ c : C, ‖x - P c x‖ ^ 2 := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hCardPos), one_mul]

/-- A card-scaled unnormalized residual estimate is sufficient for a normalized
bounded-color frame estimate with no cardinality loss.

This is the forward form intended for a genuine fixed-color or parallel-block
construction: prove that the sum of block residuals grows like the number of
blocks, rather than merely proving an `O(1)` lower bound for that sum. -/
theorem boundedColorNormalizedResidualEnergy_frame_of_card_mul_sum_lower_bound
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    [Nonempty C]
    (P : C → E →L[ℝ] E)
    (κ : ℝ)
    (x : E)
    (hsum :
      ((Fintype.card C : ℝ) * κ) * ‖x‖ ^ 2 ≤
        ∑ c : C, ‖x - P c x‖ ^ 2) :
    κ * ‖x‖ ^ 2 ≤ boundedColorNormalizedResidualEnergy P x := by
  have hCardNat : 0 < Fintype.card C := Fintype.card_pos_iff.mpr inferInstance
  have hCardPos : (0 : ℝ) < (Fintype.card C : ℝ) := Nat.cast_pos.mpr hCardNat
  have hInvNonneg :
      0 ≤ ((Fintype.card C : ℝ)⁻¹) := le_of_lt (inv_pos.mpr hCardPos)
  have hscaled := mul_le_mul_of_nonneg_left hsum hInvNonneg
  unfold boundedColorNormalizedResidualEnergy
  calc
    κ * ‖x‖ ^ 2 =
        ((Fintype.card C : ℝ)⁻¹) *
          (((Fintype.card C : ℝ) * κ) * ‖x‖ ^ 2) := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hCardPos), one_mul]
    _ ≤ ((Fintype.card C : ℝ)⁻¹) *
        (∑ c : C, ‖x - P c x‖ ^ 2) := hscaled

/-- The normalized frame estimate is therefore exactly equivalent to the
cardinality-scaled unnormalized residual estimate.  This equivalence is the
right normalization checkpoint before attempting to instantiate the physical
bounded-color bridge. -/
theorem boundedColorNormalizedResidualEnergy_frame_iff_card_mul_sum
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    [Nonempty C]
    (P : C → E →L[ℝ] E)
    (κ : ℝ)
    (x : E) :
    (κ * ‖x‖ ^ 2 ≤ boundedColorNormalizedResidualEnergy P x) ↔
      (((Fintype.card C : ℝ) * κ) * ‖x‖ ^ 2 ≤
        ∑ c : C, ‖x - P c x‖ ^ 2) := by
  constructor
  · exact boundedColor_sum_lower_bound_of_normalizedResidualEnergy P κ x
  · exact boundedColorNormalizedResidualEnergy_frame_of_card_mul_sum_lower_bound P κ x

end

end MathlibAnalytic
end MGAP4D
