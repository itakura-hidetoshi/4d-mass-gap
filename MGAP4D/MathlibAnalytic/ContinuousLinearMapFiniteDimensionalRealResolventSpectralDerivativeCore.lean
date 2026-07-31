import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventStabilityCore
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff LinearPMap Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The difference of two real shifted operators is the scalar parameter difference. -/
theorem continuousLinearMapRealShift_sub_realShift
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] V) (z w : ℝ) :
    continuousLinearMapRealShift A w - continuousLinearMapRealShift A z =
      (w - z) • (1 : V →L[ℝ] V) := by
  simp [continuousLinearMapRealShift]
  module

/-- The two-parameter real resolvent identity for arbitrary finite-dimensional
continuous endomorphisms.  With the convention `R_A(z) = (z I - A)⁻¹`, the
spectral difference carries the sign `w - z`. -/
theorem continuousLinearMapRealResolvent_sub_eq_smul_mul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) {z w : ℝ}
    (hz : IsUnit (continuousLinearMapRealShift A z))
    (hw : IsUnit (continuousLinearMapRealShift A w)) :
    continuousLinearMapRealResolvent A z -
        continuousLinearMapRealResolvent A w =
      (w - z) •
        (continuousLinearMapRealResolvent A z *
          continuousLinearMapRealResolvent A w) := by
  have hRz :
      continuousLinearMapRealResolvent A z *
          continuousLinearMapRealShift A z = 1 :=
    ringInverse_mul_of_isUnit hz
  have hRw :
      continuousLinearMapRealShift A w *
          continuousLinearMapRealResolvent A w = 1 :=
    mul_ringInverse_of_isUnit hw
  have hshift := continuousLinearMapRealShift_sub_realShift A z w
  calc
    continuousLinearMapRealResolvent A z -
        continuousLinearMapRealResolvent A w =
      continuousLinearMapRealResolvent A z * 1 -
        1 * continuousLinearMapRealResolvent A w := by
          rw [mul_one, one_mul]
    _ = continuousLinearMapRealResolvent A z *
          (continuousLinearMapRealShift A w *
            continuousLinearMapRealResolvent A w) -
        (continuousLinearMapRealResolvent A z *
          continuousLinearMapRealShift A z) *
            continuousLinearMapRealResolvent A w := by
          rw [hRw, hRz]
    _ = continuousLinearMapRealResolvent A z *
          (continuousLinearMapRealShift A w -
            continuousLinearMapRealShift A z) *
          continuousLinearMapRealResolvent A w := by
          noncomm_ring
    _ = continuousLinearMapRealResolvent A z *
          ((w - z) • (1 : V →L[ℝ] V)) *
          continuousLinearMapRealResolvent A w := by
          rw [hshift]
    _ = (w - z) •
        (continuousLinearMapRealResolvent A z *
          continuousLinearMapRealResolvent A w) := by
          simp [mul_smul_comm, smul_mul_assoc]

/-- Determinant nonvanishing gives the two-parameter real resolvent identity. -/
theorem continuousLinearMapRealResolvent_sub_eq_smul_mul_of_det_ne_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) {z w : ℝ}
    (hz : continuousLinearMapCharacteristicDeterminant A z ≠ 0)
    (hw : continuousLinearMapCharacteristicDeterminant A w ≠ 0) :
    continuousLinearMapRealResolvent A z -
        continuousLinearMapRealResolvent A w =
      (w - z) •
        (continuousLinearMapRealResolvent A z *
          continuousLinearMapRealResolvent A w) :=
  continuousLinearMapRealResolvent_sub_eq_smul_mul A
    (continuousLinearMapRealShift_isUnit_of_characteristicDeterminant_ne_zero A z hz)
    (continuousLinearMapRealShift_isUnit_of_characteristicDeterminant_ne_zero A w hw)

/-- Exact two-parameter operator-norm control from the real resolvent identity. -/
theorem continuousLinearMapRealResolvent_sub_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) {z w M : ℝ}
    (hz : IsUnit (continuousLinearMapRealShift A z))
    (hw : IsUnit (continuousLinearMapRealShift A w))
    (hzNorm : continuousLinearMapRealResolventNorm A z ≤ M)
    (hwNorm : continuousLinearMapRealResolventNorm A w ≤ M)
    (hM : 0 ≤ M) :
    ‖continuousLinearMapRealResolvent A z -
        continuousLinearMapRealResolvent A w‖ ≤
      |z - w| * (M * M) := by
  rw [continuousLinearMapRealResolvent_sub_eq_smul_mul A hz hw,
    norm_smul, Real.norm_eq_abs]
  rw [abs_sub_comm]
  calc
    |z - w| *
        ‖continuousLinearMapRealResolvent A z *
          continuousLinearMapRealResolvent A w‖ ≤
      |z - w| *
        (‖continuousLinearMapRealResolvent A z‖ *
          ‖continuousLinearMapRealResolvent A w‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (abs_nonneg _)
    _ ≤ |z - w| * (M * M) := by
      gcongr

/-- Uniformly bounded real resolvents are Lipschitz on any common real
resolvent region. -/
theorem continuousLinearMapRealResolvent_lipschitzOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (U : Set ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M) :
    LipschitzOnWith (Real.toNNReal (M * M))
      (continuousLinearMapRealResolvent A) U := by
  apply LipschitzOnWith.of_dist_le'
  intro z hz w hw
  rw [dist_eq_norm]
  have hbound := continuousLinearMapRealResolvent_sub_norm_le
    A (hunit z hz) (hunit w hw) (hnorm z hz) (hnorm w hw) hM
  calc
    ‖continuousLinearMapRealResolvent A z -
        continuousLinearMapRealResolvent A w‖ ≤
      |z - w| * (M * M) := hbound
    _ = (M * M) * dist z w := by
      rw [Real.dist_eq]
      ring
    _ = (Real.toNNReal (M * M) : ℝ) * dist z w := by
      rw [Real.coe_toNNReal (mul_nonneg hM hM)]

/-- Uniformly bounded real resolvents depend continuously on the spectral
parameter throughout a common real resolvent region. -/
theorem continuousLinearMapRealResolvent_continuousOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (U : Set ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M) :
    ContinuousOn (continuousLinearMapRealResolvent A) U :=
  (continuousLinearMapRealResolvent_lipschitzOn
    A U M hM hunit hnorm).continuousOn

/-- On a common real resolvent region, the spectral derivative of
`(z I - A)⁻¹` is `-R(z)²`. -/
theorem continuousLinearMapRealResolvent_hasDerivWithinAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (U : Set ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M)
    {z : ℝ} (hz : z ∈ U) :
    HasDerivWithinAt
      (continuousLinearMapRealResolvent A)
      (-((continuousLinearMapRealResolvent A z) ^ 2)) U z := by
  refine (hasDerivWithinAt_iff_tendsto_slope
    (𝕜 := ℝ)
    (f := continuousLinearMapRealResolvent A)
    (f' := -((continuousLinearMapRealResolvent A z) ^ 2))
    (s := U) (x := z)).2 ?_
  let Rz := continuousLinearMapRealResolvent A z
  have hres0 :
      Tendsto (continuousLinearMapRealResolvent A)
        (𝓝[U] z) (𝓝 (continuousLinearMapRealResolvent A z)) :=
    continuousLinearMapRealResolvent_continuousOn
      A U M hM hunit hnorm z hz
  have hres :
      Tendsto (continuousLinearMapRealResolvent A)
        (𝓝[U] z) (𝓝 Rz) := by
    simpa [Rz] using hres0
  have hres' :
      Tendsto (continuousLinearMapRealResolvent A)
        (𝓝[U \ {z}] z) (𝓝 Rz) :=
    hres.mono_left <| nhdsWithin_mono _ <| by
      intro w hw
      exact hw.1
  have hmul :
      Tendsto
        (fun w => continuousLinearMapRealResolvent A w * Rz)
        (𝓝[U \ {z}] z) (𝓝 (Rz * Rz)) :=
    hres'.mul tendsto_const_nhds
  have hneg :
      Tendsto
        (fun w => -(continuousLinearMapRealResolvent A w * Rz))
        (𝓝[U \ {z}] z) (𝓝 (-(Rz * Rz))) :=
    hmul.neg
  have htarget : -(Rz * Rz) = -(Rz ^ 2) := by
    rw [pow_two]
  rw [htarget] at hneg
  apply hneg.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  rcases hw with ⟨hwU, hwNe⟩
  have hne : w - z ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa only [mem_singleton_iff] using hwNe
  rw [slope_def_module,
    continuousLinearMapRealResolvent_sub_eq_smul_mul
      A (hunit w hwU) (hunit z hz)]
  simp only [zsmul_eq_mul, one_mul]
  rw [show z - w = -(w - z) by ring, neg_smul]
  rw [inv_smul_smul₀ hne]

/-- On an open real resolvent region, the within derivative is the ordinary
operator-norm derivative. -/
theorem continuousLinearMapRealResolvent_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (U : Set ℝ) (M : ℝ)
    (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M)
    {z : ℝ} (hz : z ∈ U) :
    HasDerivAt
      (continuousLinearMapRealResolvent A)
      (-((continuousLinearMapRealResolvent A z) ^ 2)) z := by
  have hwithin := continuousLinearMapRealResolvent_hasDerivWithinAt
    A U M hM hunit hnorm hz
  exact hwithin.hasDerivAt (hU.mem_nhds hz)

/-- Explicit operator-norm spectral derivative formula for the true real
resolvent. -/
theorem continuousLinearMapRealResolvent_deriv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (U : Set ℝ) (M : ℝ)
    (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M)
    {z : ℝ} (hz : z ∈ U) :
    deriv (continuousLinearMapRealResolvent A) z =
      -((continuousLinearMapRealResolvent A z) ^ 2) :=
  (continuousLinearMapRealResolvent_hasDerivAt
    A U M hU hM hunit hnorm hz).deriv

/-- The true real resolvent is differentiable in operator norm throughout an
open common real resolvent region. -/
theorem continuousLinearMapRealResolvent_differentiableOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (U : Set ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M) :
    DifferentiableOn ℝ (continuousLinearMapRealResolvent A) U := by
  intro z hz
  exact (continuousLinearMapRealResolvent_hasDerivWithinAt
    A U M hM hunit hnorm hz).differentiableWithinAt

/-- The first spectral derivative has the explicit Cauchy-type norm bound. -/
theorem continuousLinearMapRealResolvent_deriv_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (U : Set ℝ) (M : ℝ)
    (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M)
    {z : ℝ} (hz : z ∈ U) :
    ‖deriv (continuousLinearMapRealResolvent A) z‖ ≤ M ^ 2 := by
  rw [continuousLinearMapRealResolvent_deriv
    A U M hU hM hunit hnorm hz, norm_neg]
  calc
    ‖continuousLinearMapRealResolvent A z ^ 2‖ ≤
        ‖continuousLinearMapRealResolvent A z‖ ^ 2 := norm_pow_le _ _
    _ ≤ M ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) (hnorm z hz) 2

end MathlibAnalytic
end MGAP4D
