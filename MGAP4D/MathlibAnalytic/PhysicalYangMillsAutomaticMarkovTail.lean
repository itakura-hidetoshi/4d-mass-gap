import MGAP4D.MathlibAnalytic.PhysicalYangMillsLatticeMomentCertificate
import Mathlib.Analysis.SpecificLimits.Basic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

/-- A finite extended-nonnegative constant divided by the canonical radii
`n + 1` tends to zero. -/
theorem ENNReal.tendsto_const_div_natCast_add_one
    (C : ENNReal) (hC : C ≠ ∞) :
    Tendsto (fun n : ℕ => C / ((n + 1 : ℕ) : ENNReal)) atTop (nhds 0) := by
  have hNN :
      Tendsto (fun n : ℕ => C.toNNReal / (n : NNReal)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C.toNNReal
  have hShift :
      Tendsto (fun n : ℕ => C.toNNReal / ((n + 1 : ℕ) : NNReal))
        atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).2 hNN
  have hCoe :
      Tendsto
        (fun n : ℕ =>
          ((C.toNNReal / ((n + 1 : ℕ) : NNReal) : NNReal) : ENNReal))
        atTop (nhds 0) :=
    _root_.ENNReal.continuous_coe.continuousAt.tendsto.comp hShift
  refine hCoe.congr' ?_
  filter_upwards with n
  rw [← _root_.ENNReal.coe_toNNReal hC]
  exact (_root_.ENNReal.coe_div (by positivity)).symm

/-- Coercive-moment data using the canonical compact sublevels
`functional ≤ n + 1`. The Markov-tail convergence is derived automatically. -/
structure UniformNaturalRadiusCoerciveMomentCertificate
    (X : Type*) [MeasurableSpace X] [TopologicalSpace X]
    (S : Set (Measure X)) where
  functional : X → ENNReal
  functional_measurable : Measurable functional
  compact_sublevel :
    ∀ n, IsCompact {x | functional x ≤ ((n + 1 : ℕ) : ENNReal)}
  momentBound : ENNReal
  momentBound_ne_top : momentBound ≠ ∞
  uniform_lintegral_le :
    ∀ μ ∈ S, ∫⁻ x, functional x ∂μ ≤ momentBound

namespace UniformNaturalRadiusCoerciveMomentCertificate

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable {S : Set (Measure X)}

/-- Forget the canonical-radius presentation and obtain the general certificate. -/
def toCoerciveMomentCertificate
    (C : UniformNaturalRadiusCoerciveMomentCertificate X S) :
    UniformCoerciveMomentCertificate X S :=
  { functional := C.functional
    functional_measurable := C.functional_measurable
    radius := fun n => ((n + 1 : ℕ) : ENNReal)
    radius_ne_zero := fun n => by simp
    radius_ne_top := fun n => by simp
    compact_sublevel := C.compact_sublevel
    momentBound := C.momentBound
    uniform_lintegral_le := C.uniform_lintegral_le
    markovTail_tendsto_zero :=
      ENNReal.tendsto_const_div_natCast_add_one
        C.momentBound C.momentBound_ne_top }

/-- Canonical-radius coercive moments imply tightness. -/
theorem isTight
    (C : UniformNaturalRadiusCoerciveMomentCertificate X S) :
    IsTightMeasureSet S :=
  C.toCoerciveMomentCertificate.isTight

end UniformNaturalRadiusCoerciveMomentCertificate

end

end MathlibAnalytic
end MGAP4D
