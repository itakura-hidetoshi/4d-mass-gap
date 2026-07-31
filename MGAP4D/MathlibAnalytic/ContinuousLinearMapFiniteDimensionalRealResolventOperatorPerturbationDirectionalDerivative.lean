import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationDysonCore
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff LinearPMap Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The true real resolvent along the affine operator line `A + tH`. -/
def continuousLinearMapRealResolventOperatorLine
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z t : ℝ) : V →L[ℝ] V :=
  continuousLinearMapRealResolvent (A + t • H) z

/-- Exact two-parameter identity along an affine operator line. -/
theorem continuousLinearMapRealResolventOperatorLine_sub_eq_smul_mul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ) {s t : ℝ}
    (hs : IsUnit (continuousLinearMapRealShift (A + s • H) z))
    (ht : IsUnit (continuousLinearMapRealShift (A + t • H) z)) :
    continuousLinearMapRealResolventOperatorLine A H z t -
        continuousLinearMapRealResolventOperatorLine A H z s =
      (t - s) •
        (continuousLinearMapRealResolventOperatorLine A H z t * H *
          continuousLinearMapRealResolventOperatorLine A H z s) := by
  unfold continuousLinearMapRealResolventOperatorLine
  rw [continuousLinearMapRealResolvent_sub_eq_mul_operator_sub_mul
    (A + s • H) (A + t • H) z hs ht]
  have hdiff : (A + t • H) - (A + s • H) = (t - s) • H := by
    module
  rw [hdiff]
  simp [mul_assoc]

/-- Uniform inverse bounds give a quantitative Lipschitz estimate along the
operator line. -/
theorem continuousLinearMapRealResolventOperatorLine_sub_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ) {s t M : ℝ}
    (hs : IsUnit (continuousLinearMapRealShift (A + s • H) z))
    (ht : IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hsNorm : ‖continuousLinearMapRealResolventOperatorLine A H z s‖ ≤ M)
    (htNorm : ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M)
    (hM : 0 ≤ M) :
    ‖continuousLinearMapRealResolventOperatorLine A H z t -
        continuousLinearMapRealResolventOperatorLine A H z s‖ ≤
      |t - s| * (M * ‖H‖ * M) := by
  rw [continuousLinearMapRealResolventOperatorLine_sub_eq_smul_mul A H z hs ht,
    norm_smul, Real.norm_eq_abs]
  calc
    |t - s| *
        ‖continuousLinearMapRealResolventOperatorLine A H z t * H *
          continuousLinearMapRealResolventOperatorLine A H z s‖ ≤
      |t - s| *
        ((‖continuousLinearMapRealResolventOperatorLine A H z t‖ * ‖H‖) *
          ‖continuousLinearMapRealResolventOperatorLine A H z s‖) := by
      gcongr
      exact norm_mul_le _ _ |>.trans <|
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ |t - s| * (M * ‖H‖ * M) := by gcongr

/-- Uniformly bounded resolvents are Lipschitz along an affine operator line. -/
theorem continuousLinearMapRealResolventOperatorLine_lipschitzOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M) :
    LipschitzOnWith (Real.toNNReal (M * ‖H‖ * M))
      (continuousLinearMapRealResolventOperatorLine A H z) U := by
  apply LipschitzOnWith.of_dist_le'
  intro s hs t ht
  rw [dist_eq_norm]
  have hbound := continuousLinearMapRealResolventOperatorLine_sub_norm_le
    A H z (hunit s hs) (hunit t ht) (hnorm s hs) (hnorm t ht) hM
  calc
    ‖continuousLinearMapRealResolventOperatorLine A H z s -
        continuousLinearMapRealResolventOperatorLine A H z t‖ =
      ‖continuousLinearMapRealResolventOperatorLine A H z t -
        continuousLinearMapRealResolventOperatorLine A H z s‖ := by
      rw [norm_sub_rev]
    _ ≤ |t - s| * (M * ‖H‖ * M) := hbound
    _ = (M * ‖H‖ * M) * dist s t := by
      rw [Real.dist_eq, abs_sub_comm]
      ring

/-- Uniformly bounded resolvents depend continuously on the operator-line
parameter. -/
theorem continuousLinearMapRealResolventOperatorLine_continuousOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M) :
    ContinuousOn (continuousLinearMapRealResolventOperatorLine A H z) U :=
  (continuousLinearMapRealResolventOperatorLine_lipschitzOn
    A H z U M hM hunit hnorm).continuousOn

/-- The operator-direction derivative of a true real resolvent is `R H R`. -/
theorem continuousLinearMapRealResolventOperatorLine_hasDerivWithinAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M)
    {t : ℝ} (ht : t ∈ U) :
    HasDerivWithinAt
      (continuousLinearMapRealResolventOperatorLine A H z)
      (continuousLinearMapRealResolventOperatorLine A H z t * H *
        continuousLinearMapRealResolventOperatorLine A H z t) U t := by
  refine (hasDerivWithinAt_iff_tendsto_slope
    (𝕜 := ℝ)
    (f := continuousLinearMapRealResolventOperatorLine A H z)
    (f' := continuousLinearMapRealResolventOperatorLine A H z t * H *
      continuousLinearMapRealResolventOperatorLine A H z t)
    (s := U) (x := t)).2 ?_
  let Rt := continuousLinearMapRealResolventOperatorLine A H z t
  have hres0 : Tendsto (continuousLinearMapRealResolventOperatorLine A H z)
      (𝓝[U] t) (𝓝 (continuousLinearMapRealResolventOperatorLine A H z t)) :=
    continuousLinearMapRealResolventOperatorLine_continuousOn
      A H z U M hM hunit hnorm t ht
  have hres : Tendsto (continuousLinearMapRealResolventOperatorLine A H z)
      (𝓝[U] t) (𝓝 Rt) := by simpa [Rt] using hres0
  have hres' : Tendsto (continuousLinearMapRealResolventOperatorLine A H z)
      (𝓝[U \ {t}] t) (𝓝 Rt) :=
    hres.mono_left <| nhdsWithin_mono _ <| by
      intro w hw
      exact hw.1
  have hmul : Tendsto
      (fun w => continuousLinearMapRealResolventOperatorLine A H z w * H * Rt)
      (𝓝[U \ {t}] t) (𝓝 (Rt * H * Rt)) :=
    (hres'.mul tendsto_const_nhds).mul tendsto_const_nhds
  apply hmul.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  rcases hw with ⟨hwU, hwNe⟩
  have hne : w - t ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa only [mem_singleton_iff] using hwNe
  rw [slope_def_module,
    continuousLinearMapRealResolventOperatorLine_sub_eq_smul_mul
      A H z (hunit t ht) (hunit w hwU)]
  rw [inv_smul_smul₀ hne]

/-- On an open operator-line resolvent region the within derivative is the
ordinary derivative. -/
theorem continuousLinearMapRealResolventOperatorLine_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M)
    {t : ℝ} (ht : t ∈ U) :
    HasDerivAt
      (continuousLinearMapRealResolventOperatorLine A H z)
      (continuousLinearMapRealResolventOperatorLine A H z t * H *
        continuousLinearMapRealResolventOperatorLine A H z t) t :=
  (continuousLinearMapRealResolventOperatorLine_hasDerivWithinAt
    A H z U M hM hunit hnorm ht).hasDerivAt (hU.mem_nhds ht)

/-- Explicit ordinary operator-direction derivative formula. -/
theorem continuousLinearMapRealResolventOperatorLine_deriv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M)
    {t : ℝ} (ht : t ∈ U) :
    deriv (continuousLinearMapRealResolventOperatorLine A H z) t =
      continuousLinearMapRealResolventOperatorLine A H z t * H *
        continuousLinearMapRealResolventOperatorLine A H z t :=
  (continuousLinearMapRealResolventOperatorLine_hasDerivAt
    A H z U M hU hM hunit hnorm ht).deriv

/-- The finite Dyson coefficient jet along an affine operator line. -/
def continuousLinearMapRealResolventOperatorDirectionalDysonJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (N : ℕ) (A H : V →L[ℝ] V) (z t : ℝ) :
    Fin N → (V →L[ℝ] V) :=
  fun n => continuousLinearMapRealResolventOperatorDysonCoefficient n.1
    (A + t • H) H z

end MathlibAnalytic
end MGAP4D