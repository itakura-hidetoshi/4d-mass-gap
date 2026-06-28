import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalOrbitContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The physical semigroup orbit extended from nonnegative to real time by
clamping negative real times to zero.  Only its restriction to nonnegative
intervals is used in the time-average construction. -/
def realPhysicalOrbit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (s : ℝ) : P.PhysicalHilbert :=
  T.toPhysicalSemigroup.operator s.toNNReal psi

/-- The real-time extension of every physical orbit is continuous. -/
theorem realPhysicalOrbit_continuous
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    Continuous (T.realPhysicalOrbit psi) := by
  exact (T.physicalOrbit_continuous psi).comp continuous_real_toNNReal

/-- Real physical orbits are Bochner integrable on every compact interval. -/
theorem realPhysicalOrbit_intervalIntegrable
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (a b : ℝ) :
    IntervalIntegrable (T.realPhysicalOrbit psi) MeasureTheory.volume a b :=
  (T.realPhysicalOrbit_continuous psi).intervalIntegrable a b

@[simp] theorem realPhysicalOrbit_zero_time
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    T.realPhysicalOrbit psi 0 = psi := by
  simp [realPhysicalOrbit, T.toPhysicalSemigroup.operator_zero]

@[simp] theorem realPhysicalOrbit_add
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi phi : P.PhysicalHilbert) (s : ℝ) :
    T.realPhysicalOrbit (psi + phi) s =
      T.realPhysicalOrbit psi s + T.realPhysicalOrbit phi s := by
  simp [realPhysicalOrbit]

@[simp] theorem realPhysicalOrbit_smul
    (T : P.StronglyContinuousPhysicalSemigroup)
    (r : ℝ) (psi : P.PhysicalHilbert) (s : ℝ) :
    T.realPhysicalOrbit (r • psi) s = r • T.realPhysicalOrbit psi s := by
  simp [realPhysicalOrbit]

/-- The unnormalized Bochner time integral of a physical semigroup orbit. -/
def timeIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) : P.PhysicalHilbert :=
  ∫ s in (0 : ℝ)..(h : ℝ), T.realPhysicalOrbit psi s

/-- The normalized Cesàro time average of a physical semigroup orbit. -/
def timeAverage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) : P.PhysicalHilbert :=
  (h : ℝ)⁻¹ • T.timeIntegral h psi

@[simp] theorem timeIntegral_zero_width
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    T.timeIntegral 0 psi = 0 := by
  simp [timeIntegral]

@[simp] theorem timeAverage_zero_width
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    T.timeAverage 0 psi = 0 := by
  simp [timeAverage]

@[simp] theorem timeIntegral_zero
    (T : P.StronglyContinuousPhysicalSemigroup) (h : NNReal) :
    T.timeIntegral h 0 = 0 := by
  simp [timeIntegral, realPhysicalOrbit]

@[simp] theorem timeAverage_zero
    (T : P.StronglyContinuousPhysicalSemigroup) (h : NNReal) :
    T.timeAverage h 0 = 0 := by
  simp [timeAverage]

@[simp] theorem timeIntegral_add
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi phi : P.PhysicalHilbert) :
    T.timeIntegral h (psi + phi) =
      T.timeIntegral h psi + T.timeIntegral h phi := by
  simpa only [timeIntegral, realPhysicalOrbit_add] using
    intervalIntegral.integral_add
      (T.realPhysicalOrbit_intervalIntegrable psi 0 (h : ℝ))
      (T.realPhysicalOrbit_intervalIntegrable phi 0 (h : ℝ))

@[simp] theorem timeIntegral_smul
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (r : ℝ) (psi : P.PhysicalHilbert) :
    T.timeIntegral h (r • psi) = r • T.timeIntegral h psi := by
  simp [timeIntegral, realPhysicalOrbit]

@[simp] theorem timeAverage_add
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi phi : P.PhysicalHilbert) :
    T.timeAverage h (psi + phi) =
      T.timeAverage h psi + T.timeAverage h phi := by
  simp [timeAverage, smul_add]

@[simp] theorem timeAverage_smul
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (r : ℝ) (psi : P.PhysicalHilbert) :
    T.timeAverage h (r • psi) = r • T.timeAverage h psi := by
  simp [timeAverage, smul_smul, mul_comm]

/-- Time averaging is a real-linear endomorphism of the physical Hilbert
space. -/
noncomputable def timeAverageLinearMap
    (T : P.StronglyContinuousPhysicalSemigroup) (h : NNReal) :
    P.PhysicalHilbert →ₗ[ℝ] P.PhysicalHilbert where
  toFun := T.timeAverage h
  map_add' := T.timeAverage_add h
  map_smul' := T.timeAverage_smul h

@[simp] theorem timeAverageLinearMap_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    T.timeAverageLinearMap h psi = T.timeAverage h psi :=
  rfl

/-- Physical time evolution commutes pointwise with the real orbit used in the
Bochner integral. -/
theorem physicalOperator_realPhysicalOrbit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (t : NNReal) (psi : P.PhysicalHilbert) (s : ℝ) :
    T.toPhysicalSemigroup.operator t (T.realPhysicalOrbit psi s) =
      T.realPhysicalOrbit (T.toPhysicalSemigroup.operator t psi) s := by
  exact T.physicalOperator_commute_apply t s.toNNReal psi

/-- Physical time evolution commutes with the unnormalized time integral. -/
theorem physicalOperator_timeIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (t h : NNReal) (psi : P.PhysicalHilbert) :
    T.toPhysicalSemigroup.operator t (T.timeIntegral h psi) =
      T.timeIntegral h (T.toPhysicalSemigroup.operator t psi) := by
  unfold timeIntegral
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm
    (T.toPhysicalSemigroup.operator t)
    (T.realPhysicalOrbit_intervalIntegrable psi 0 (h : ℝ))]
  apply intervalIntegral.integral_congr
  intro s hs
  exact T.physicalOperator_realPhysicalOrbit t psi s

/-- Physical time evolution commutes with the normalized time average. -/
theorem physicalOperator_timeAverage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (t h : NNReal) (psi : P.PhysicalHilbert) :
    T.toPhysicalSemigroup.operator t (T.timeAverage h psi) =
      T.timeAverage h (T.toPhysicalSemigroup.operator t psi) := by
  simp [timeAverage, map_smul, T.physicalOperator_timeIntegral]

@[simp] theorem realPhysicalOrbit_vacuum
    (T : P.StronglyContinuousPhysicalSemigroup) (s : ℝ) :
    T.realPhysicalOrbit P.vacuum s = P.vacuum := by
  simp [realPhysicalOrbit, T.toPhysicalSemigroup.fixes_vacuum]

@[simp] theorem timeIntegral_vacuum
    (T : P.StronglyContinuousPhysicalSemigroup) (h : NNReal) :
    T.timeIntegral h P.vacuum = (h : ℝ) • P.vacuum := by
  simp [timeIntegral]

@[simp] theorem timeAverage_vacuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    {h : NNReal} (hh : h ≠ 0) :
    T.timeAverage h P.vacuum = P.vacuum := by
  have hhreal : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  simp [timeAverage, hhreal, smul_smul]

/-- The real-time orbit inherits the pointwise contraction bound. -/
theorem realPhysicalOrbit_norm_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (s : ℝ) :
    ‖T.realPhysicalOrbit psi s‖ ≤ ‖psi‖ := by
  exact T.physicalOperator_norm_le s.toNNReal psi

/-- The norm of the unnormalized time integral is bounded by interval length
times the original vector norm. -/
theorem timeIntegral_norm_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    ‖T.timeIntegral h psi‖ ≤ (h : ℝ) * ‖psi‖ := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (h : ℝ)) (C := ‖psi‖)
    (f := T.realPhysicalOrbit psi)
    (fun s hs => T.realPhysicalOrbit_norm_le psi s)
  simpa [timeIntegral, abs_of_nonneg h.coe_nonneg, mul_comm] using hbound

/-- Every positive normalized time average is contractive. -/
theorem timeAverage_norm_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    {h : NNReal} (hh : 0 < h) (psi : P.PhysicalHilbert) :
    ‖T.timeAverage h psi‖ ≤ ‖psi‖ := by
  have hhreal : 0 < (h : ℝ) := by exact_mod_cast hh
  rw [timeAverage, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos hhreal]
  calc
    (h : ℝ)⁻¹ * ‖T.timeIntegral h psi‖ ≤
        (h : ℝ)⁻¹ * ((h : ℝ) * ‖psi‖) :=
      mul_le_mul_of_nonneg_left (T.timeIntegral_norm_le h psi)
        (inv_nonneg.mpr hhreal.le)
    _ = ‖psi‖ := by field_simp

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
