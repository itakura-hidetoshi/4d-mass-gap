import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedDenseTemporalApproximation
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- The canonical integer step selecting the lattice time immediately below a
target physical time `t`.  It is an approximation selector, not an additive map
from real time to integer time. -/
noncomputable def physicalTemporalFloorStep
    (latticeSpacing : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℤ :=
  ⌊t / latticeSpacing n⌋

/-- The physical time selected by the floor step never exceeds the target time. -/
theorem physicalTemporalFloorStep_mul_le
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (t : ℝ) (n : ℕ) :
    ((physicalTemporalFloorStep latticeSpacing t n : ℤ) : ℝ) *
        latticeSpacing n ≤ t := by
  have hfloor :
      ((⌊t / latticeSpacing n⌋ : ℤ) : ℝ) ≤
        t / latticeSpacing n :=
    Int.floor_le _
  have hmul := mul_le_mul_of_nonneg_right hfloor (latticeSpacing_pos n).le
  calc
    ((physicalTemporalFloorStep latticeSpacing t n : ℤ) : ℝ) *
        latticeSpacing n =
      ((⌊t / latticeSpacing n⌋ : ℤ) : ℝ) * latticeSpacing n := rfl
    _ ≤ (t / latticeSpacing n) * latticeSpacing n := hmul
    _ = t := by
      field_simp [ne_of_gt (latticeSpacing_pos n)]

/-- The target time lies less than one lattice spacing above the selected floor
time. -/
theorem physicalTemporalFloorStep_lt_add_spacing
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (t : ℝ) (n : ℕ) :
    t < ((physicalTemporalFloorStep latticeSpacing t n : ℤ) : ℝ) *
        latticeSpacing n + latticeSpacing n := by
  have hfloor :
      t / latticeSpacing n <
        ((⌊t / latticeSpacing n⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hmul := mul_lt_mul_of_pos_right hfloor (latticeSpacing_pos n)
  calc
    t = (t / latticeSpacing n) * latticeSpacing n := by
      field_simp [ne_of_gt (latticeSpacing_pos n)]
    _ < (((⌊t / latticeSpacing n⌋ : ℤ) : ℝ) + 1) *
        latticeSpacing n := hmul
    _ = ((physicalTemporalFloorStep latticeSpacing t n : ℤ) : ℝ) *
        latticeSpacing n + latticeSpacing n := by
      rw [add_mul, one_mul]
      rfl

/-- The nonnegative floor-approximation error is bounded by one lattice spacing. -/
theorem physicalTemporalFloorStep_error_bounds
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (t : ℝ) (n : ℕ) :
    0 ≤ t - ((physicalTemporalFloorStep latticeSpacing t n : ℤ) : ℝ) *
        latticeSpacing n ∧
      t - ((physicalTemporalFloorStep latticeSpacing t n : ℤ) : ℝ) *
          latticeSpacing n ≤ latticeSpacing n := by
  constructor
  · exact sub_nonneg.mpr
      (physicalTemporalFloorStep_mul_le latticeSpacing latticeSpacing_pos t n)
  · have hlt :=
      physicalTemporalFloorStep_lt_add_spacing
        latticeSpacing latticeSpacing_pos t n
    linarith

/-- Positive lattice spacings tending to zero make the canonical floor-selected
physical times converge to every prescribed real time. -/
theorem physicalTemporalFloorStep_tendsto
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (t : ℝ) :
    Tendsto
      (fun n =>
        ((physicalTemporalFloorStep latticeSpacing t n : ℤ) : ℝ) *
          latticeSpacing n)
      atTop (nhds t) := by
  have herror :
      Tendsto
        (fun n =>
          t - ((physicalTemporalFloorStep latticeSpacing t n : ℤ) : ℝ) *
            latticeSpacing n)
        atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact
        (physicalTemporalFloorStep_error_bounds
          latticeSpacing latticeSpacing_pos t n).1
    · intro n
      exact
        (physicalTemporalFloorStep_error_bounds
          latticeSpacing latticeSpacing_pos t n).2
    · exact latticeSpacing_tendsto_zero
  have hsub := tendsto_const_nhds.sub herror
  simpa only [sub_sub_cancel, sub_zero] using hsub

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.DenseTemporalApproximation

variable {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
variable {A : E.PhysicalDiscreteTemporalAction}

/-- Construct dense realizable temporal approximations automatically whenever
the finite-scale physical-time homomorphism is multiplication by the lattice
spacing. -/
noncomputable def ofFloor
    (latticeTime_eq : ∀ n k,
      A.latticeTime n k = (k : ℝ) * E.latticeSpacing n) :
    A.DenseTemporalApproximation where
  approximateStep t n := physicalTemporalFloorStep E.latticeSpacing t n
  approximateTime_tendsto t := by
    have h := physicalTemporalFloorStep_tendsto
      E.latticeSpacing E.latticeSpacing_pos E.latticeSpacing_tendsto_zero t
    simpa only [latticeTime_eq] using h

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.DenseTemporalApproximation

end

end MathlibAnalytic
end MGAP4D
