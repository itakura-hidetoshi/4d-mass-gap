import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceC5ExceptionalSupport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance spatialSliceC5ExceptionalResidualColumnBoundFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- If a C5 spatial influence column is pointwise dominated by a uniform
coefficient on the volume-independent exceptional set plus an arbitrary
residual, then the whole column is bounded by `20 * eta` plus the residual
column sum.

This is the finite-sum interface matching the geometric C5 decomposition: all
bare/local exceptional contributions occupy at most twenty spatial links, and
every contribution outside that set may be placed in the vacuum residual. -/
theorem periodicHypercubicEvenSpatialSlice_C5_influenceColumnSum_le_twenty_mul_add_residual
    (H : ℕ)
    (distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (influence residual :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (eta : ℝ)
    (hEtaNonneg : 0 ≤ eta)
    (hPointwise : ∀ target source,
      influence target source ≤
        (if target ∈
            periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
              H source distinguishedTarget then eta else 0) +
          residual target source)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        influence target source) ≤
      20 * eta +
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          residual target source := by
  classical
  let s :=
    periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
      H source distinguishedTarget
  have hCardNat : s.card ≤ 20 := by
    simpa [s] using
      periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers_card_le_twenty
        H source distinguishedTarget
  have hCard : (s.card : ℝ) ≤ 20 := by
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
    _ ≤ 20 * eta +
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        residual target source := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_right hCard hEtaNonneg)
            (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              residual target source)

/-- A uniform bound on the C5 vacuum-residual column sum yields a
volume-independent complete column bound. -/
theorem periodicHypercubicEvenSpatialSlice_C5_influenceColumnSum_le_twenty_mul_add_residualBound
    (H : ℕ)
    (distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (influence residual :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (eta rho : ℝ)
    (hEtaNonneg : 0 ≤ eta)
    (hPointwise : ∀ target source,
      influence target source ≤
        (if target ∈
            periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
              H source distinguishedTarget then eta else 0) +
          residual target source)
    (hResidualColumn : ∀ source,
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        residual target source) ≤ rho)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        influence target source) ≤
      20 * eta + rho := by
  exact
    (periodicHypercubicEvenSpatialSlice_C5_influenceColumnSum_le_twenty_mul_add_residual
      H distinguishedTarget influence residual eta hEtaNonneg hPointwise source).trans
      (add_le_add_left (hResidualColumn source) (20 * eta))

/-- Hence `20 * eta + rho < 1` is a sufficient scalar C5 contraction gate
once the pointwise exceptional-plus-vacuum decomposition and a uniform vacuum
residual-column bound are supplied. -/
theorem periodicHypercubicEvenSpatialSlice_C5_influenceColumnSum_lt_one_of_exceptional_residual
    (H : ℕ)
    (distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (influence residual :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (eta rho : ℝ)
    (hEtaNonneg : 0 ≤ eta)
    (hPointwise : ∀ target source,
      influence target source ≤
        (if target ∈
            periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
              H source distinguishedTarget then eta else 0) +
          residual target source)
    (hResidualColumn : ∀ source,
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        residual target source) ≤ rho)
    (hStrict : 20 * eta + rho < 1)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        influence target source) < 1 :=
  lt_of_le_of_lt
    (periodicHypercubicEvenSpatialSlice_C5_influenceColumnSum_le_twenty_mul_add_residualBound
      H distinguishedTarget influence residual eta rho hEtaNonneg hPointwise
      hResidualColumn source)
    hStrict

end

end MathlibAnalytic
end MGAP4D