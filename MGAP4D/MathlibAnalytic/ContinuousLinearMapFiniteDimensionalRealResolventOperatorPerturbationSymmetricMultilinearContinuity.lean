import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationSymmetricMultilinearResponse
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- For a fixed direction tuple, every ordered noncommutative resolvent word is
continuous in the resolvent variable. -/
theorem continuous_continuousLinearMapRealResolventOrderedDysonMultilinear
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (H : Fin n → (V →L[ℝ] V)) :
    Continuous (fun R : V →L[ℝ] V =>
      continuousLinearMapRealResolventOrderedDysonMultilinear n R H) := by
  simp only [continuousLinearMapRealResolventOrderedDysonMultilinear_apply]
  fun_prop

/-- For a fixed direction tuple, the fully symmetric multilinear derivative
word is continuous in the resolvent variable. -/
theorem continuous_continuousLinearMapRealResolventSymmetricDysonMultilinear
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (H : Fin n → (V →L[ℝ] V)) :
    Continuous (fun R : V →L[ℝ] V =>
      continuousLinearMapRealResolventSymmetricDysonMultilinear n R H) := by
  change Continuous (fun R : V →L[ℝ] V =>
    ∑ σ : Equiv.Perm (Fin n),
      continuousLinearMapRealResolventOrderedDysonMultilinear n R
        (fun i => H (σ i)))
  apply continuous_finset_sum
  intro σ _hσ
  exact continuous_continuousLinearMapRealResolventOrderedDysonMultilinear
    n (fun i => H (σ i))

/-- Resolvent convergence transfers to every fixed symmetric multilinear
mixed-direction coefficient. -/
theorem tendsto_continuousLinearMapRealResolventSymmetricDysonMultilinear
    {V α : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter α} (n : ℕ) (H : Fin n → (V →L[ℝ] V))
    (R : α → (V →L[ℝ] V)) (R0 : V →L[ℝ] V)
    (hR : Tendsto R l (𝓝 R0)) :
    Tendsto (fun a =>
      continuousLinearMapRealResolventSymmetricDysonMultilinear n (R a) H) l
      (𝓝 (continuousLinearMapRealResolventSymmetricDysonMultilinear n R0 H)) :=
  (continuous_continuousLinearMapRealResolventSymmetricDysonMultilinear
    n H).continuousAt.tendsto.comp hR

/-- Continuous-linear observations of fixed symmetric mixed-direction
coefficients are continuous in the resolvent variable. -/
theorem continuous_continuousLinearMapRealResolventSymmetricDysonLinearResponse
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n : ℕ)
    (H : Fin n → (V →L[ℝ] V)) :
    Continuous (fun R : V →L[ℝ] V =>
      φ (continuousLinearMapRealResolventSymmetricDysonMultilinear n R H)) :=
  φ.continuous.comp
    (continuous_continuousLinearMapRealResolventSymmetricDysonMultilinear n H)

end MathlibAnalytic
end MGAP4D
