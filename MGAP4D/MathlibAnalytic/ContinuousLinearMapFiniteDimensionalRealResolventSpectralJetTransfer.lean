import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventFactorialSpectralDerivative
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalContinuousObservableCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The algebraic `n`th spectral jet observable of a real resolvent value. -/
def continuousLinearMapRealResolventSpectralJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : V →L[ℝ] V) : V →L[ℝ] V :=
  continuousLinearMapRealResolventSpectralCoefficient n • R ^ (n + 1)

/-- The finite vector of spectral jets through `order`, equipped with the
product supremum norm. -/
def continuousLinearMapRealResolventSpectralJetVector
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (order : ℕ) (R : V →L[ℝ] V) :
    Fin (order + 1) → (V →L[ℝ] V) :=
  fun n => continuousLinearMapRealResolventSpectralJet n.1 R

/-- Every fixed algebraic real-resolvent spectral jet is continuous. -/
theorem continuous_continuousLinearMapRealResolventSpectralJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) :
    Continuous (continuousLinearMapRealResolventSpectralJet (V := V) n) := by
  unfold continuousLinearMapRealResolventSpectralJet
  exact (continuous_const_smul _).comp (continuous_id.pow (n + 1))

/-- Every finite spectral jet vector is continuous in the product supremum
norm. -/
theorem continuous_continuousLinearMapRealResolventSpectralJetVector
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (order : ℕ) :
    Continuous
      (continuousLinearMapRealResolventSpectralJetVector (V := V) order) := by
  unfold continuousLinearMapRealResolventSpectralJetVector
  apply continuous_pi
  intro n
  exact continuous_continuousLinearMapRealResolventSpectralJet n.1

/-- The algebraic spectral jet agrees with the true operator-norm iterated
spectral derivative throughout an open common resolvent region. -/
theorem continuousLinearMapRealResolventSpectralJet_eq_iteratedDeriv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (U : Set ℝ) (M : ℝ)
    (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M)
    (n : ℕ) {z : ℝ} (hz : z ∈ U) :
    continuousLinearMapRealResolventSpectralJet n
        (continuousLinearMapRealResolvent A z) =
      iteratedDeriv n (continuousLinearMapRealResolvent A) z := by
  symm
  exact continuousLinearMapRealResolvent_iteratedDeriv
    A U M hU hM hunit hnorm n hz

/-- Uniform convergence of finite-dimensional resolvent values transfers to
any fixed algebraic spectral jet. -/
theorem finiteDimensional_realResolventSpectralJet_tendsto_uniformOn
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (R : α → ι → (V →L[ℝ] V)) (R0 : ι → (V →L[ℝ] V))
    (n : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hR0 : ∀ i ∈ s, ‖R0 i‖ ≤ M)
    (hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖R a i - R0 i‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s,
        ‖continuousLinearMapRealResolventSpectralJet n (R a i) -
          continuousLinearMapRealResolventSpectralJet n (R0 i)‖ < epsilon := by
  exact finiteDimensional_continuousObservable_tendsto_uniformOn
    R R0 (continuousLinearMapRealResolventSpectralJet n)
    (continuous_continuousLinearMapRealResolventSpectralJet n)
    M hM hR0 hR

/-- Uniform convergence of finite-dimensional resolvent values transfers
simultaneously to every spectral derivative through a fixed finite order. -/
theorem finiteDimensional_realResolventSpectralJetVector_tendsto_uniformOn
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (R : α → ι → (V →L[ℝ] V)) (R0 : ι → (V →L[ℝ] V))
    (order : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hR0 : ∀ i ∈ s, ‖R0 i‖ ≤ M)
    (hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖R a i - R0 i‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s,
        ‖continuousLinearMapRealResolventSpectralJetVector order (R a i) -
          continuousLinearMapRealResolventSpectralJetVector order (R0 i)‖ < epsilon := by
  exact finiteDimensional_continuousObservable_tendsto_uniformOn
    R R0 (continuousLinearMapRealResolventSpectralJetVector order)
    (continuous_continuousLinearMapRealResolventSpectralJetVector order)
    M hM hR0 hR

end MathlibAnalytic
end MGAP4D
