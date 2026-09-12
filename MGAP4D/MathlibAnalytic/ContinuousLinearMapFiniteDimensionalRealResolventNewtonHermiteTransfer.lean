import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventNewtonHermiteExact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalContinuousObservableCore
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Generic exact-remainder observable on a tuple containing the interpolation
node resolvents followed by the evaluation-point resolvent. -/
def continuousLinearMapRealResolventNewtonHermiteRemainderObservable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (degree : ℕ) (nodes : Fin (degree + 1) → ℝ) (z : ℝ)
    (R : Fin (degree + 2) → (V →L[ℝ] V)) : V →L[ℝ] V :=
  continuousLinearMapRealResolventNewtonNodeProduct (degree + 1) nodes z •
    continuousLinearMapRealResolventHermiteObservable (degree + 1) R

/-- The generic exact-remainder observable is continuous in the complete
finite operator tuple. -/
theorem continuous_continuousLinearMapRealResolventNewtonHermiteRemainderObservable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (degree : ℕ) (nodes : Fin (degree + 1) → ℝ) (z : ℝ) :
    Continuous
      (continuousLinearMapRealResolventNewtonHermiteRemainderObservable
        (V := V) degree nodes z) := by
  exact
    (continuous_const_smul
      (continuousLinearMapRealResolventNewtonNodeProduct
        (degree + 1) nodes z)).comp
      (continuous_continuousLinearMapRealResolventHermiteObservable (degree + 1))

/-- Two-component observable consisting of the Newton-Hermite interpolant and
its exact closed remainder. -/
def continuousLinearMapRealResolventNewtonHermitePairObservable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (degree : ℕ) (nodes : Fin (degree + 1) → ℝ) (z : ℝ)
    (R : Fin (degree + 2) → (V →L[ℝ] V)) :
    Fin 2 → (V →L[ℝ] V) :=
  ![continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
      degree nodes z (Fin.init R),
    continuousLinearMapRealResolventNewtonHermiteRemainderObservable
      degree nodes z R]

/-- The complete interpolant/remainder pair is continuous in product supremum
norm. -/
theorem continuous_continuousLinearMapRealResolventNewtonHermitePairObservable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (degree : ℕ) (nodes : Fin (degree + 1) → ℝ) (z : ℝ) :
    Continuous
      (continuousLinearMapRealResolventNewtonHermitePairObservable
        (V := V) degree nodes z) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · have hinit : Continuous
        (fun R : Fin (degree + 2) → (V →L[ℝ] V) => Fin.init R) := by
      apply continuous_pi
      intro k
      exact continuous_apply k.castSucc
    simpa [continuousLinearMapRealResolventNewtonHermitePairObservable]
      using
        (continuous_continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
          (V := V) degree nodes z).comp hinit
  · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    simpa [continuousLinearMapRealResolventNewtonHermitePairObservable]
      using
        continuous_continuousLinearMapRealResolventNewtonHermiteRemainderObservable
          (V := V) degree nodes z

/-- Uniform convergence of finite operator tuples transfers to a fixed
Newton-Hermite interpolant observable. -/
theorem finiteDimensional_realResolventNewtonHermiteInterpolant_tendsto_uniformOn
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (degree : ℕ) (nodes : Fin (degree + 1) → ℝ) (z : ℝ)
    (R : α → ι → Fin (degree + 1) → (V →L[ℝ] V))
    (R0 : ι → Fin (degree + 1) → (V →L[ℝ] V))
    (M : ℝ) (hM : 0 ≤ M)
    (hR0 : ∀ i ∈ s, ‖R0 i‖ ≤ M)
    (hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖R a i - R0 i‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s,
        ‖continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
            degree nodes z (R a i) -
          continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
            degree nodes z (R0 i)‖ < epsilon := by
  exact finiteDimensional_continuousObservable_tendsto_uniformOn
    R R0
    (continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
      degree nodes z)
    (continuous_continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
      degree nodes z)
    M hM hR0 hR

/-- Componentwise tuple convergence is sufficient for uniform convergence of
Newton-Hermite interpolants. -/
theorem finiteDimensional_realResolventNewtonHermiteInterpolant_tendsto_uniformOn_of_componentwise
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (degree : ℕ) (nodes : Fin (degree + 1) → ℝ) (z : ℝ)
    (R : α → ι → Fin (degree + 1) → (V →L[ℝ] V))
    (R0 : ι → Fin (degree + 1) → (V →L[ℝ] V))
    (M : ℝ) (hM : 0 ≤ M)
    (hR0 : ∀ i ∈ s, ∀ j, ‖R0 i j‖ ≤ M)
    (hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ∀ j, ‖R a i j - R0 i j‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s,
        ‖continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
            degree nodes z (R a i) -
          continuousLinearMapRealResolventNewtonHermiteInterpolantObservable
            degree nodes z (R0 i)‖ < epsilon := by
  apply finiteDimensional_realResolventNewtonHermiteInterpolant_tendsto_uniformOn
    degree nodes z R R0 M hM
  · intro i hi
    rw [pi_norm_le_iff_of_nonneg hM]
    exact hR0 i hi
  · intro eta heta
    have h := hR eta heta
    filter_upwards [h] with a ha
    intro i hi
    rw [pi_norm_lt_iff heta]
    intro j
    simpa only [Pi.sub_apply] using ha i hi j

/-- Componentwise convergence of the full node-plus-evaluation tuple transfers
to the exact closed remainder. -/
theorem finiteDimensional_realResolventNewtonHermiteRemainder_tendsto_uniformOn_of_componentwise
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (degree : ℕ) (nodes : Fin (degree + 1) → ℝ) (z : ℝ)
    (R : α → ι → Fin (degree + 2) → (V →L[ℝ] V))
    (R0 : ι → Fin (degree + 2) → (V →L[ℝ] V))
    (M : ℝ) (hM : 0 ≤ M)
    (hR0 : ∀ i ∈ s, ∀ j, ‖R0 i j‖ ≤ M)
    (hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ∀ j, ‖R a i j - R0 i j‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s,
        ‖continuousLinearMapRealResolventNewtonHermiteRemainderObservable
            degree nodes z (R a i) -
          continuousLinearMapRealResolventNewtonHermiteRemainderObservable
            degree nodes z (R0 i)‖ < epsilon := by
  apply finiteDimensional_continuousObservable_tendsto_uniformOn
    R R0
    (continuousLinearMapRealResolventNewtonHermiteRemainderObservable
      degree nodes z)
    (continuous_continuousLinearMapRealResolventNewtonHermiteRemainderObservable
      degree nodes z)
    M hM
  · intro i hi
    rw [pi_norm_le_iff_of_nonneg hM]
    exact hR0 i hi
  · intro eta heta
    have h := hR eta heta
    filter_upwards [h] with a ha
    intro i hi
    rw [pi_norm_lt_iff heta]
    intro j
    simpa only [Pi.sub_apply] using ha i hi j

/-- Simultaneous uniform convergence of Newton-Hermite interpolants and their
exact closed remainders. -/
theorem finiteDimensional_realResolventNewtonHermitePair_tendsto_uniformOn_of_componentwise
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (degree : ℕ) (nodes : Fin (degree + 1) → ℝ) (z : ℝ)
    (R : α → ι → Fin (degree + 2) → (V →L[ℝ] V))
    (R0 : ι → Fin (degree + 2) → (V →L[ℝ] V))
    (M : ℝ) (hM : 0 ≤ M)
    (hR0 : ∀ i ∈ s, ∀ j, ‖R0 i j‖ ≤ M)
    (hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ∀ j, ‖R a i j - R0 i j‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s,
        ‖continuousLinearMapRealResolventNewtonHermitePairObservable
            degree nodes z (R a i) -
          continuousLinearMapRealResolventNewtonHermitePairObservable
            degree nodes z (R0 i)‖ < epsilon := by
  apply finiteDimensional_continuousObservable_tendsto_uniformOn
    R R0
    (continuousLinearMapRealResolventNewtonHermitePairObservable
      degree nodes z)
    (continuous_continuousLinearMapRealResolventNewtonHermitePairObservable
      degree nodes z)
    M hM
  · intro i hi
    rw [pi_norm_le_iff_of_nonneg hM]
    exact hR0 i hi
  · intro eta heta
    have h := hR eta heta
    filter_upwards [h] with a ha
    intro i hi
    rw [pi_norm_lt_iff heta]
    intro j
    simpa only [Pi.sub_apply] using ha i hi j

end MathlibAnalytic
end MGAP4D
