import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set
open scoped InnerProductSpace Topology

noncomputable section

universe u

/-- A compact operator on a real Hilbert space can be approximated in operator
norm by an operator factoring through a finite-dimensional subspace.  The
construction is intrinsic: take a finite net of the compact closure of the
unit-ball image and orthogonally project onto its finite span. -/
theorem realHilbertCompact_exists_finiteDimensional_factor_approx
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →L[ℝ] E)
    (hA : IsCompactOperator A)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (V : Submodule ℝ E) (_ : FiniteDimensional ℝ V)
      (B : E →L[ℝ] V),
      ‖A - V.subtypeL ∘L B‖ < ε := by
  let K : Set E := closure (A '' Metric.closedBall 0 1)
  have hKcompact : IsCompact K := by
    simpa [K] using hA.isCompact_closure_image_closedBall (1 : ℝ)
  have hδ : 0 < ε / 2 := half_pos hε
  obtain ⟨t, htK, htfinite, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded hKcompact.totallyBounded (ε / 2) hδ
  let V : Submodule ℝ E := Submodule.span ℝ t
  letI : FiniteDimensional ℝ V :=
    FiniteDimensional.span_of_finite ℝ htfinite
  let B : E →L[ℝ] V := V.orthogonalProjection ∘L A
  have hunit : ∀ x : E, ‖x‖ ≤ 1 → ‖(A - V.subtypeL ∘L B) x‖ ≤ ε / 2 := by
    intro x hx
    have hxball : x ∈ Metric.closedBall (0 : E) 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hAxK : A x ∈ K := by
      exact subset_closure ⟨x, hxball, rfl⟩
    have hAxcover := hcover hAxK
    simp only [Set.mem_iUnion, Metric.mem_ball] at hAxcover
    rcases hAxcover with ⟨y, hy⟩
    rcases hy with ⟨hyt, hdist⟩
    have hyV : y ∈ V := by
      exact Submodule.subset_span hyt
    have hproj : ‖A x - V.starProjection (A x)‖ ≤ ‖A x - y‖ := by
      rw [V.starProjection_minimal]
      change (⨅ z : V, ‖A x - (z : E)‖) ≤ ‖A x - y‖
      have hnonneg : BddBelow (Set.range (fun z : V => ‖A x - (z : E)‖)) := by
        exact ⟨0, Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩
      exact ciInf_le hnonneg ⟨y, hyV⟩
    have hprojlt : ‖A x - V.starProjection (A x)‖ < ε / 2 :=
      lt_of_le_of_lt hproj (by simpa [dist_eq_norm] using hdist)
    change ‖A x - V.starProjection (A x)‖ ≤ ε / 2
    exact hprojlt.le
  have hop : ‖A - V.subtypeL ∘L B‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_bound
    · exact hδ.le
    · intro x
      by_cases hx0 : x = 0
      · simp [hx0]
      · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
        let u : E := ‖x‖⁻¹ • x
        have hu_norm : ‖u‖ = 1 := by
          dsimp [u]
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hxpos]
          exact inv_mul_cancel₀ hxpos.ne'
        have hu := hunit u (by rw [hu_norm])
        have hx_repr : x = ‖x‖ • u := by
          dsimp [u]
          rw [smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
        calc
          ‖(A - V.subtypeL ∘L B) x‖ =
              ‖(A - V.subtypeL ∘L B) (‖x‖ • u)‖ :=
            congrArg (fun z : E => ‖(A - V.subtypeL ∘L B) z‖) hx_repr
          _ = ‖x‖ * ‖(A - V.subtypeL ∘L B) u‖ := by
            rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
          _ ≤ ‖x‖ * (ε / 2) :=
            mul_le_mul_of_nonneg_left hu (norm_nonneg x)
          _ = (ε / 2) * ‖x‖ := by
            rw [mul_comm]
  refine ⟨V, inferInstance, B, lt_of_le_of_lt hop ?_⟩
  linarith

end

end MathlibAnalytic
end MGAP4D
