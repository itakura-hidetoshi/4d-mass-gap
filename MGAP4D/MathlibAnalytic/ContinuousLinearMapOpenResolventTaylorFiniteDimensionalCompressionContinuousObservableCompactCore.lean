import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalContinuousObservableCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E V W : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Every continuous observable of a compressed fixed Taylor derivative
converges uniformly on compact strict-subgap spectral sets. -/
theorem iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (Phi : (V →L[ℝ] V) → W) (hPhi : Continuous Phi)
    (k : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K,
        ‖Phi (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          Phi (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon := by
  let R : ℝ :=
    ‖Q‖ * ((k.factorial : ℝ) * (gap - u)⁻¹ ^ (k + 1)) * ‖J‖
  have hmargin : 0 < gap - u := sub_pos.mpr hu
  have hinv : 0 ≤ (gap - u)⁻¹ := inv_nonneg.mpr hmargin.le
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg
      (mul_nonneg (norm_nonneg Q)
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hinv _)))
      (norm_nonneg J)
  have hlimit :
      ∀ lambda ∈ K,
        ‖continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k S.limitResolvent lambda)‖ ≤ R := by
    intro lambda hlambda
    have h :=
      L.iteratedDeriv_finiteDimensionalCompression_norm_le_on_Iic
        J Q k (by simpa [hLgap] using hu) (hKu hlambda)
    simpa [R, hLgap, hLresolvent] using h
  have hoperator :=
    S.iteratedDeriv_tendsto_uniformOn_compact_finiteDimensionalCompression
      B L hLgap hLresolvent J Q k K hKcompact hKu hu
  exact
    finiteDimensional_continuousObservable_tendsto_uniformOn
      (l := l) (s := K)
      (fun a lambda => continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k (F a) lambda))
      (fun lambda => continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k S.limitResolvent lambda))
      Phi hPhi R hR hlimit hoperator

/-- A finite Taylor jet may carry a different continuous observable at each
jet level, with simultaneous compact-uniform convergence. -/
theorem iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact_jet
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (Phi : ℕ → (V →L[ℝ] V) → W) (hPhi : ∀ k, Continuous (Phi k))
    (order : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ k ≤ order, ∀ lambda ∈ K,
        ‖Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon := by
  intro epsilon hepsilon
  have hk : ∀ k ∈ Finset.range (order + 1),
      ∀ᶠ a in l, ∀ lambda ∈ K,
        ‖Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon := by
    intro k hk
    exact S.iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact
      B L hLgap hLresolvent J Q (Phi k) (hPhi k)
      k K hKcompact hKu hu epsilon hepsilon
  have hfinite : ∀ᶠ a in l, ∀ k ∈ Finset.range (order + 1), ∀ lambda ∈ K,
      ‖Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon := by
    change {a | ∀ k ∈ Finset.range (order + 1), ∀ lambda ∈ K,
      ‖Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon} ∈ l
    rw [show {a | ∀ k ∈ Finset.range (order + 1), ∀ lambda ∈ K,
      ‖Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon} =
      ⋂ k ∈ Finset.range (order + 1), {a | ∀ lambda ∈ K,
        ‖Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          Phi k (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon} by
      ext a
      simp]
    exact (Filter.biInter_finset_mem (Finset.range (order + 1))).2
      fun k hk' => hk k hk'
  filter_upwards [hfinite] with a ha
  intro k hkOrder
  exact ha k (Finset.mem_range.2 (Nat.lt_succ_iff.2 hkOrder))

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
