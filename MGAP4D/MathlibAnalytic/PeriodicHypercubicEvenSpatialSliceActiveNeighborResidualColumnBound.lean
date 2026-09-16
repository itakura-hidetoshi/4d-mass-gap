import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSliceActiveNeighborBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance spatialSliceActiveNeighborResidualColumnBoundFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- If a spatial influence column is pointwise dominated by a uniform local
coefficient on the direct Wilson active-neighbor set plus an arbitrary
nonnegative residual, then the whole column is bounded by `18 * eta` plus the
residual column sum.

This is the exact algebraic form needed after remote raw-kernel cancellation:
the finite-volume dependence of the bare Wilson part is replaced by the
volume-independent active-neighbor degree `18`; every remaining nonlocal effect
is isolated in `residual`. -/
theorem periodicHypercubicEvenSpatialSlice_influenceColumnSum_le_eighteen_mul_add_residual
    (H : ℕ)
    (influence residual :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (eta : ℝ)
    (hEtaNonneg : 0 ≤ eta)
    (hResidualNonneg : ∀ target source, 0 ≤ residual target source)
    (hPointwise : ∀ target source,
      influence target source ≤
        (if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
          eta else 0) + residual target source)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        influence target source) ≤
      18 * eta +
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          residual target source := by
  classical
  let s := periodicHypercubicEvenSpatialSliceActiveNeighbors H source
  have hCardNat : s.card ≤ 18 := by
    simpa [s] using
      periodicHypercubicEvenSpatialSliceActiveNeighbors_card_le_eighteen H source
  have hCard : (s.card : ℝ) ≤ 18 := by
    exact_mod_cast hCardNat
  calc
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        influence target source) ≤
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        ((if target ∈ s then eta else 0) + residual target source) := by
          apply Finset.sum_le_sum
          intro target _hTarget
          simpa [s] using hPointwise target source
    _ =
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        if target ∈ s then eta else 0) +
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        residual target source := by
          rw [Finset.sum_add_distrib]
    _ = (s.card : ℝ) * eta +
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        residual target source := by
          congr 1
          rw [← Finset.sum_filter]
          simp [nsmul_eq_mul]
    _ ≤ 18 * eta +
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        residual target source := by
          simpa [add_comm] using
            add_le_add_right
              (mul_le_mul_of_nonneg_right hCard hEtaNonneg)
              (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
                residual target source)

/-- A uniform bound on the residual column sum turns the local-plus-residual
split into a volume-independent column bound. -/
theorem periodicHypercubicEvenSpatialSlice_influenceColumnSum_le_eighteen_mul_add_residualBound
    (H : ℕ)
    (influence residual :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (eta rho : ℝ)
    (hEtaNonneg : 0 ≤ eta)
    (hResidualNonneg : ∀ target source, 0 ≤ residual target source)
    (hPointwise : ∀ target source,
      influence target source ≤
        (if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
          eta else 0) + residual target source)
    (hResidualColumn : ∀ source,
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        residual target source) ≤ rho)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        influence target source) ≤
      18 * eta + rho := by
  exact
    (periodicHypercubicEvenSpatialSlice_influenceColumnSum_le_eighteen_mul_add_residual
      H influence residual eta hEtaNonneg hResidualNonneg hPointwise source).trans
      (by
        simpa [add_comm] using
          add_le_add_left (hResidualColumn source) (18 * eta))

/-- Consequently, the scalar gate `18 * eta + rho < 1` is sufficient for every
spatial influence column to be strictly contractive once the pointwise
local-plus-vacuum-residual decomposition and the uniform residual-column bound
have been proved. -/
theorem periodicHypercubicEvenSpatialSlice_influenceColumnSum_lt_one_of_local_residual
    (H : ℕ)
    (influence residual :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (eta rho : ℝ)
    (hEtaNonneg : 0 ≤ eta)
    (hResidualNonneg : ∀ target source, 0 ≤ residual target source)
    (hPointwise : ∀ target source,
      influence target source ≤
        (if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
          eta else 0) + residual target source)
    (hResidualColumn : ∀ source,
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        residual target source) ≤ rho)
    (hStrict : 18 * eta + rho < 1)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        influence target source) < 1 :=
  lt_of_le_of_lt
    (periodicHypercubicEvenSpatialSlice_influenceColumnSum_le_eighteen_mul_add_residualBound
      H influence residual eta rho hEtaNonneg hResidualNonneg hPointwise
      hResidualColumn source)
    hStrict

end

end MathlibAnalytic
end MGAP4D