import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventLinearResponseCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventNewtonHermiteVariableTransfer
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Apply a finite family of continuous linear spectral observables to every
component of an operator-valued Newton-Hermite pair. -/
def continuousLinearMapRealResolventLinearResponseFamilyPair
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {observableOrder : ℕ}
    (Phi : Fin (observableOrder + 1) → ((V →L[ℝ] V) →L[ℝ] ℝ))
    (P : Fin 2 → (V →L[ℝ] V)) :
    Fin (observableOrder + 1) → Fin 2 → ℝ :=
  fun r i => Phi r (P i)

/-- The finite response-family map is continuous from the operator-pair
product supremum norm to the doubly finite scalar product supremum norm. -/
theorem continuous_continuousLinearMapRealResolventLinearResponseFamilyPair
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {observableOrder : ℕ}
    (Phi : Fin (observableOrder + 1) → ((V →L[ℝ] V) →L[ℝ] ℝ)) :
    Continuous
      (continuousLinearMapRealResolventLinearResponseFamilyPair Phi) := by
  unfold continuousLinearMapRealResolventLinearResponseFamilyPair
  apply continuous_pi
  intro r
  apply continuous_pi
  intro i
  exact (Phi r).continuous.comp (continuous_apply i)

/-- A finite uniformly bounded family of linear observables transfers uniform
operator-pair convergence to simultaneous scalar response convergence. -/
theorem finiteDimensional_linearResponseFamilyPair_tendsto_uniformOn
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter α} {s : Set ι} {observableOrder : ℕ}
    (Phi : Fin (observableOrder + 1) → ((V →L[ℝ] V) →L[ℝ] ℝ))
    (P : α → ι → Fin 2 → (V →L[ℝ] V))
    (P0 : ι → Fin 2 → (V →L[ℝ] V))
    (L : ℝ) (hL : 0 ≤ L) (hPhi : ∀ r, ‖Phi r‖ ≤ L)
    (hP : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ q ∈ s, ‖P a q - P0 q‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ q ∈ s,
        ‖continuousLinearMapRealResolventLinearResponseFamilyPair Phi (P a q) -
          continuousLinearMapRealResolventLinearResponseFamilyPair Phi (P0 q)‖ < epsilon := by
  intro epsilon hepsilon
  let eta : ℝ := epsilon / (L + 1)
  have hL1 : 0 < L + 1 := by linarith
  have heta : 0 < eta := div_pos hepsilon hL1
  have hpair := hP eta heta
  filter_upwards [hpair] with a ha
  intro q hq
  rw [pi_norm_lt_iff hepsilon]
  intro r
  rw [pi_norm_lt_iff hepsilon]
  intro i
  have hcomponent : ‖P a q i - P0 q i‖ < eta := by
    have hp := ha q hq
    rw [pi_norm_lt_iff heta] at hp
    simpa only [Pi.sub_apply] using hp i
  have hdual := (Phi r).le_opNorm (P a q i - P0 q i)
  rw [Real.norm_eq_abs] at hdual
  calc
    ‖(continuousLinearMapRealResolventLinearResponseFamilyPair Phi (P a q) -
        continuousLinearMapRealResolventLinearResponseFamilyPair Phi (P0 q)) r i‖ =
        |Phi r (P a q i - P0 q i)| := by
          simp [continuousLinearMapRealResolventLinearResponseFamilyPair,
            Real.norm_eq_abs]
    _ ≤ ‖Phi r‖ * ‖P a q i - P0 q i‖ := hdual
    _ ≤ L * ‖P a q i - P0 q i‖ :=
      mul_le_mul_of_nonneg_right (hPhi r) (norm_nonneg _)
    _ < (L + 1) * eta := by
      exact mul_lt_mul hcomponent (by linarith) (norm_nonneg _) hL1
    _ = epsilon := by
      dsimp [eta]
      field_simp [ne_of_gt hL1]

/-- Fixed-node Newton-Hermite operator-pair convergence transfers to an
arbitrary finite response family. -/
theorem finiteDimensional_realResolventNewtonHermiteLinearResponseFamilyPair_tendsto_uniformOn_of_componentwise
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι} {observableOrder : ℕ}
    (degree : ℕ) (nodes : Fin (degree + 1) → ℝ) (z : ℝ)
    (Phi : Fin (observableOrder + 1) → ((V →L[ℝ] V) →L[ℝ] ℝ))
    (R : α → ι → Fin (degree + 2) → (V →L[ℝ] V))
    (R0 : ι → Fin (degree + 2) → (V →L[ℝ] V))
    (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hPhi : ∀ r, ‖Phi r‖ ≤ L)
    (hR0 : ∀ q ∈ s, ∀ j, ‖R0 q j‖ ≤ M)
    (hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ q ∈ s, ∀ j, ‖R a q j - R0 q j‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ q ∈ s,
        ‖continuousLinearMapRealResolventLinearResponseFamilyPair Phi
            (continuousLinearMapRealResolventNewtonHermitePairObservable
              degree nodes z (R a q)) -
          continuousLinearMapRealResolventLinearResponseFamilyPair Phi
            (continuousLinearMapRealResolventNewtonHermitePairObservable
              degree nodes z (R0 q))‖ < epsilon := by
  apply finiteDimensional_linearResponseFamilyPair_tendsto_uniformOn
    Phi
    (fun a q => continuousLinearMapRealResolventNewtonHermitePairObservable
      degree nodes z (R a q))
    (fun q => continuousLinearMapRealResolventNewtonHermitePairObservable
      degree nodes z (R0 q))
    L hL hPhi
  exact finiteDimensional_realResolventNewtonHermitePair_tendsto_uniformOn_of_componentwise
    degree nodes z R R0 M hM hR0 hR

/-- Weighted variable-node Newton-Hermite pair convergence transfers to every
member of a finite response family without a node-separation hypothesis. -/
theorem finiteDimensional_weightedNewtonHermiteLinearResponseFamilyPair_tendsto_uniformOn
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι} {observableOrder : ℕ}
    (degree : ℕ)
    (Phi : Fin (observableOrder + 1) → ((V →L[ℝ] V) →L[ℝ] ℝ))
    (X : α → ι →
      (Fin (degree + 2) → ℝ) ×
        (Fin (degree + 2) → (V →L[ℝ] V)))
    (X0 : ι →
      (Fin (degree + 2) → ℝ) ×
        (Fin (degree + 2) → (V →L[ℝ] V)))
    (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hPhi : ∀ r, ‖Phi r‖ ≤ L)
    (hX0 : ∀ q ∈ s, ‖X0 q‖ ≤ M)
    (hX : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ q ∈ s, ‖X a q - X0 q‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ q ∈ s,
        ‖continuousLinearMapRealResolventLinearResponseFamilyPair Phi
            (continuousLinearMapRealResolventWeightedNewtonHermitePairObservable
              degree (X a q)) -
          continuousLinearMapRealResolventLinearResponseFamilyPair Phi
            (continuousLinearMapRealResolventWeightedNewtonHermitePairObservable
              degree (X0 q))‖ < epsilon := by
  apply finiteDimensional_linearResponseFamilyPair_tendsto_uniformOn
    Phi
    (fun a q => continuousLinearMapRealResolventWeightedNewtonHermitePairObservable
      degree (X a q))
    (fun q => continuousLinearMapRealResolventWeightedNewtonHermitePairObservable
      degree (X0 q))
    L hL hPhi
  exact finiteDimensional_continuousObservable_tendsto_uniformOn
    X X0
    (continuousLinearMapRealResolventWeightedNewtonHermitePairObservable degree)
    (continuous_continuousLinearMapRealResolventWeightedNewtonHermitePairObservable degree)
    M hM hX0 hX

end MathlibAnalytic
end MGAP4D
