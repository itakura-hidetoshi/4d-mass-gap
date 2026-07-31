import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionContinuousObservableCompactCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/- This module is part of the unified continuous spectral-observable package. -/

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Determinants of compressed Taylor derivatives converge compact-uniformly. -/
theorem iteratedDeriv_det_finiteDimensionalCompression_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (k : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K,
        |(continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)).det -
          (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)).det| < epsilon := by
  simpa [Real.norm_eq_abs] using
    S.iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact
      B L hLgap hLresolvent J Q (fun A : V →L[ℝ] V => A.det)
      ContinuousLinearMap.continuous_det k K hKcompact hKu hu

/-- Whole finite Taylor jets have simultaneous determinant convergence. -/
theorem iteratedDeriv_det_finiteDimensionalCompression_tendsto_uniformOn_compact_jet
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (order : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ k ≤ order, ∀ lambda ∈ K,
        |(continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)).det -
          (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)).det| < epsilon := by
  simpa [Real.norm_eq_abs] using
    S.iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact_jet
      B L hLgap hLresolvent J Q
      (fun (_ : ℕ) (A : V →L[ℝ] V) => A.det)
      (fun _ => ContinuousLinearMap.continuous_det)
      order K hKcompact hKu hu

section AlgebraicConsequences

variable {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
variable (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
variable (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
variable (L : ContinuousLinearMapOpenResolventNormBoundData E)
variable (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
variable (J : V →L[ℝ] E) (Q : E →L[ℝ] V)

/-- Finite operator polynomials converge compact-uniformly in operator norm. -/
theorem iteratedDeriv_polynomial_finiteDimensionalCompression_tendsto_uniformOn_compact
    (coeff : ℕ → ℝ) (degree k : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ lambda ∈ K,
      ‖continuousLinearMapPolynomial coeff degree
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda)) -
        continuousLinearMapPolynomial coeff degree
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon :=
  S.iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact
    B L hLgap hLresolvent J Q (continuousLinearMapPolynomial coeff degree)
    (continuous_continuousLinearMapPolynomial coeff degree)
    k K hKcompact hKu hu

end AlgebraicConsequences

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
