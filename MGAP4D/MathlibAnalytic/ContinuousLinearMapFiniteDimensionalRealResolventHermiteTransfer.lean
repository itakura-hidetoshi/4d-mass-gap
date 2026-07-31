import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventHermiteCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalContinuousObservableCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Uniform convergence of finite tuples of finite-dimensional operators
transfers to any fixed normalized Hermite observable. -/
theorem finiteDimensional_realResolventHermiteObservable_tendsto_uniformOn
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (order : ℕ)
    (R : α → ι → Fin (order + 1) → (V →L[ℝ] V))
    (R0 : ι → Fin (order + 1) → (V →L[ℝ] V))
    (M : ℝ) (hM : 0 ≤ M)
    (hR0 : ∀ i ∈ s, ‖R0 i‖ ≤ M)
    (hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖R a i - R0 i‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s,
        ‖continuousLinearMapRealResolventHermiteObservable order (R a i) -
          continuousLinearMapRealResolventHermiteObservable order (R0 i)‖ < epsilon := by
  exact finiteDimensional_continuousObservable_tendsto_uniformOn
    R R0 (continuousLinearMapRealResolventHermiteObservable order)
    (continuous_continuousLinearMapRealResolventHermiteObservable order)
    M hM hR0 hR

/-- Uniform convergence of finite tuples transfers simultaneously to the
entire normalized Hermite jet through a fixed finite order. -/
theorem finiteDimensional_realResolventHermiteJet_tendsto_uniformOn
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (order : ℕ)
    (R : α → ι → Fin (order + 1) → (V →L[ℝ] V))
    (R0 : ι → Fin (order + 1) → (V →L[ℝ] V))
    (M : ℝ) (hM : 0 ≤ M)
    (hR0 : ∀ i ∈ s, ‖R0 i‖ ≤ M)
    (hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖R a i - R0 i‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s,
        ‖continuousLinearMapRealResolventHermiteJet order (R a i) -
          continuousLinearMapRealResolventHermiteJet order (R0 i)‖ < epsilon := by
  exact finiteDimensional_continuousObservable_tendsto_uniformOn
    R R0 (continuousLinearMapRealResolventHermiteJet order)
    (continuous_continuousLinearMapRealResolventHermiteJet order)
    M hM hR0 hR

end MathlibAnalytic
end MGAP4D
