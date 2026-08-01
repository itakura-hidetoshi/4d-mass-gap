import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterMultilinearJetDirectionFamilyCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalContinuousObservableCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Uniform convergence of a finite-dimensional family, together with an
independent convergent finite-dimensional parameter, passes through every
continuous observable on the product space.  This is the generic transfer
principle used for simultaneously moving resolvents and perturbation families. -/
theorem finiteDimensional_continuousObservable_tendsto_uniformOn_prod_const
    {α ι X Z Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {l : Filter α} {s : Set ι}
    (A : α → ι → X) (A0 : ι → X) (B : α → Z) (B0 : Z)
    (Phi : X × Z → Y) (hPhi : Continuous Phi)
    (R : ℝ) (hR : 0 ≤ R) (hA0 : ∀ i ∈ s, ‖A0 i‖ ≤ R)
    (hA : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖A a i - A0 i‖ < eta)
    (hB : Tendsto B l (𝓝 B0)) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s,
        ‖Phi (A a i, B a) - Phi (A0 i, B0)‖ < epsilon := by
  let C : α → ι → X × Z := fun a i => (A a i, B a)
  let C0 : ι → X × Z := fun i => (A0 i, B0)
  let R0 : ℝ := max R ‖B0‖
  have hR0 : 0 ≤ R0 := by
    exact le_max_of_le_left hR
  have hC0 : ∀ i ∈ s, ‖C0 i‖ ≤ R0 := by
    intro i hi
    simp only [C0, Prod.norm_def, max_le_iff, R0]
    exact ⟨hA0 i hi, le_rfl⟩
  have hBmetric : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ‖B a - B0‖ < eta := by
    rw [Metric.tendsto_nhds] at hB
    intro eta heta
    have hb := hB eta heta
    filter_upwards [hb] with a ha
    simpa [dist_eq_norm] using ha
  have hC : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖C a i - C0 i‖ < eta := by
    intro eta heta
    have ha := hA eta heta
    have hb := hBmetric eta heta
    filter_upwards [ha, hb] with a hAa hBa
    intro i hi
    simp only [C, C0, Prod.fst_sub, Prod.snd_sub, Prod.norm_def,
      max_lt_iff]
    exact ⟨hAa i hi, hBa⟩
  exact finiteDimensional_continuousObservable_tendsto_uniformOn
    C C0 Phi hPhi R0 hR0 hC0 hC

/-- Specialization of the generic product transfer principle to a compressed
resolvent and a complete finite family of operator perturbation directions. -/
theorem finiteDimensional_directionFamilyObservable_tendsto_uniformOn
    {α ι V Y : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {l : Filter α} {s : Set ι}
    (R : α → ι → (V →L[ℝ] V)) (R0 : ι → (V →L[ℝ] V))
    {m : ℕ} (H : α → Fin m → (V →L[ℝ] V))
    (H0 : Fin m → (V →L[ℝ] V))
    (Phi : (V →L[ℝ] V) × (Fin m → (V →L[ℝ] V)) → Y)
    (hPhi : Continuous Phi) (M : ℝ) (hM : 0 ≤ M)
    (hR0 : ∀ i ∈ s, ‖R0 i‖ ≤ M)
    (hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖R a i - R0 i‖ < eta)
    (hH : Tendsto H l (𝓝 H0)) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s,
        ‖Phi (R a i, H a) - Phi (R0 i, H0)‖ < epsilon :=
  finiteDimensional_continuousObservable_tendsto_uniformOn_prod_const
    R R0 H H0 Phi hPhi M hM hR0 hR hH

end MathlibAnalytic
end MGAP4D
