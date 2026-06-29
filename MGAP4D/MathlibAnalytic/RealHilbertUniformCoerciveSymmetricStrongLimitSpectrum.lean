import MGAP4D.MathlibAnalytic.RealHilbertUniformCoerciveSymmetricStrongLimitLaxMilgram
import Mathlib.Analysis.Normed.Algebra.Spectrum

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Real spectral shift of the strongly limiting operator. -/
noncomputable def
    RealHilbertUniformCoerciveSymmetricStrongLimitData.limitShiftOperator
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    (lambda : ℝ) :
    E →L[ℝ] E :=
  D.limitOperator - lambda • ContinuousLinearMap.id ℝ E

@[simp] theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limitShiftOperator_apply
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    (lambda : ℝ)
    (f : E) :
    D.limitShiftOperator lambda f = D.limitOperator f - lambda • f := by
  rfl

/-- The strong-limit quadratic gap persists after every real shift below it. -/
theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limitShiftOperator_gap
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    (lambda : ℝ)
    (f : E) :
    (D.gap - lambda) * ‖f‖ ^ 2 ≤
      inner ℝ (D.limitShiftOperator lambda f) f := by
  have hGap :=
    realHilbert_uniformCoerciveStrongLimit_limit_gap
      D.toRealHilbertUniformCoerciveStrongLimitData f
  rw [realHilbert_uniformCoerciveSymmetricStrongLimit_limitShiftOperator_apply]
  have hSmul :
      inner ℝ (lambda • f) f = lambda * inner ℝ f f :=
    real_inner_smul_left f f lambda
  have hSelf : inner ℝ f f = ‖f‖ ^ 2 :=
    real_inner_self_eq_norm_sq f
  have hInner :
      inner ℝ (D.limitOperator f - lambda • f) f =
        inner ℝ (D.limitOperator f) f - lambda * ‖f‖ ^ 2 := by
    calc
      inner ℝ (D.limitOperator f - lambda • f) f =
          inner ℝ (D.limitOperator f) f - inner ℝ (lambda • f) f :=
        inner_sub_left _ _ _
      _ = inner ℝ (D.limitOperator f) f - lambda * inner ℝ f f :=
        congrArg
          (fun t : ℝ => inner ℝ (D.limitOperator f) f - t)
          hSmul
      _ = inner ℝ (D.limitOperator f) f - lambda * ‖f‖ ^ 2 :=
        congrArg
          (fun t : ℝ => inner ℝ (D.limitOperator f) f - lambda * t)
          hSelf
  rw [hInner]
  nlinarith [sq_nonneg ‖f‖]

/-- Bounded bilinear form associated with the shifted strong-limit operator. -/
noncomputable def
    RealHilbertUniformCoerciveSymmetricStrongLimitData.limitShiftForm
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    (lambda : ℝ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ).comp (D.limitShiftOperator lambda)

@[simp] theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limitShiftForm_apply
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    (lambda : ℝ)
    (f g : E) :
    D.limitShiftForm lambda f g =
      inner ℝ (D.limitShiftOperator lambda f) g := by
  rfl

/-- Every shift below the limiting gap is coercive. -/
theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limitShiftForm_isCoercive
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    {lambda : ℝ}
    (hlambda : lambda < D.gap) :
    IsCoercive (D.limitShiftForm lambda) := by
  refine ⟨D.gap - lambda, sub_pos.mpr hlambda, ?_⟩
  intro f
  change
    (D.gap - lambda) * ‖f‖ * ‖f‖ ≤
      inner ℝ (D.limitShiftOperator lambda f) f
  simpa [pow_two, mul_assoc] using
    realHilbert_uniformCoerciveSymmetricStrongLimit_limitShiftOperator_gap
      D lambda f

/-- Lax--Milgram equivalence for every real shift below the limiting gap. -/
noncomputable def
    RealHilbertUniformCoerciveSymmetricStrongLimitData.limitShiftEquivalence
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    {lambda : ℝ}
    (hlambda : lambda < D.gap) :
    E ≃L[ℝ] E :=
  (realHilbert_uniformCoerciveSymmetricStrongLimit_limitShiftForm_isCoercive
    D hlambda).continuousLinearEquivOfBilin

/-- The shifted Lax--Milgram equivalence acts by `A - lambda I`. -/
theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limitShiftEquivalence_apply
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    {lambda : ℝ}
    (hlambda : lambda < D.gap)
    (f : E) :
    D.limitShiftEquivalence hlambda f = D.limitShiftOperator lambda f := by
  change
    InnerProductSpace.continuousLinearMapOfBilin
        (D.limitShiftForm lambda) f =
      D.limitShiftOperator lambda f
  symm
  apply InnerProductSpace.unique_continuousLinearMapOfBilin
  intro g
  rfl

/-- Continuous resolvent of the limiting operator below the inherited gap. -/
noncomputable def
    RealHilbertUniformCoerciveSymmetricStrongLimitData.limitResolvent
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    {lambda : ℝ}
    (hlambda : lambda < D.gap) :
    E →L[ℝ] E :=
  (D.limitShiftEquivalence hlambda).symm.toContinuousLinearMap

/-- The shifted limiting operator followed by its resolvent is the identity. -/
theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limitShift_apply_resolvent
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    {lambda : ℝ}
    (hlambda : lambda < D.gap)
    (y : E) :
    D.limitShiftOperator lambda (D.limitResolvent hlambda y) = y := by
  change
    D.limitShiftOperator lambda ((D.limitShiftEquivalence hlambda).symm y) = y
  rw [← realHilbert_uniformCoerciveSymmetricStrongLimit_limitShiftEquivalence_apply]
  exact (D.limitShiftEquivalence hlambda).apply_symm_apply y

/-- The limiting resolvent followed by the shifted operator is the identity. -/
theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_apply_shift
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    {lambda : ℝ}
    (hlambda : lambda < D.gap)
    (f : E) :
    D.limitResolvent hlambda (D.limitShiftOperator lambda f) = f := by
  change
    (D.limitShiftEquivalence hlambda).symm
        (D.limitShiftOperator lambda f) = f
  rw [← realHilbert_uniformCoerciveSymmetricStrongLimit_limitShiftEquivalence_apply]
  exact (D.limitShiftEquivalence hlambda).symm_apply_apply f

/-- Pointwise resolvent estimate inherited from the limiting quadratic gap. -/
theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_bound
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    {lambda : ℝ}
    (hlambda : lambda < D.gap)
    (y : E) :
    ‖D.limitResolvent hlambda y‖ ≤ (D.gap - lambda)⁻¹ * ‖y‖ := by
  let x : E := D.limitResolvent hlambda y
  change ‖x‖ ≤ (D.gap - lambda)⁻¹ * ‖y‖
  have hShiftPos : 0 < D.gap - lambda := sub_pos.mpr hlambda
  by_cases hx : x = 0
  · rw [hx, norm_zero]
    exact mul_nonneg (inv_nonneg.mpr hShiftPos.le) (norm_nonneg y)
  have hxNorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hGap :=
    realHilbert_uniformCoerciveSymmetricStrongLimit_limitShiftOperator_gap
      D lambda x
  have hInverse : D.limitShiftOperator lambda x = y := by
    dsimp [x]
    exact
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitShift_apply_resolvent
        D hlambda y
  rw [hInverse] at hGap
  have hCS : inner ℝ y x ≤ ‖y‖ * ‖x‖ := real_inner_le_norm y x
  have hMul : (D.gap - lambda) * ‖x‖ ^ 2 ≤ ‖y‖ * ‖x‖ :=
    hGap.trans hCS
  have hLinear : (D.gap - lambda) * ‖x‖ ≤ ‖y‖ := by
    nlinarith [sq_nonneg ‖x‖]
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hShiftPos).2
  simpa [mul_comm] using hLinear

/-- Operator-norm estimate for the limiting resolvent. -/
theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_le
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    {lambda : ℝ}
    (hlambda : lambda < D.gap) :
    ‖D.limitResolvent hlambda‖ ≤ (D.gap - lambda)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact inv_nonneg.mpr (sub_pos.mpr hlambda).le
  · exact
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_bound
        D hlambda

/-- Every real parameter below the inherited gap belongs to the resolvent set
of the strong-limit operator. -/
theorem realHilbert_uniformCoerciveSymmetricStrongLimit_mem_resolventSet
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    {lambda : ℝ}
    (hlambda : lambda < D.gap) :
    lambda ∈ resolventSet ℝ D.limitOperator := by
  let S : E →L[ℝ] E := D.limitShiftOperator lambda
  let R : E →L[ℝ] E := D.limitResolvent hlambda
  have hScalarShift :
      algebraMap ℝ (E →L[ℝ] E) lambda - D.limitOperator = -S := by
    apply ContinuousLinearMap.ext
    intro y
    change lambda • y - D.limitOperator y =
      -(D.limitOperator y - lambda • y)
    abel
  have hShiftResolvent : S * R = 1 := by
    apply ContinuousLinearMap.ext
    intro y
    change D.limitShiftOperator lambda (D.limitResolvent hlambda y) = y
    exact
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitShift_apply_resolvent
        D hlambda y
  have hResolventShift : R * S = 1 := by
    apply ContinuousLinearMap.ext
    intro y
    change D.limitResolvent hlambda (D.limitShiftOperator lambda y) = y
    exact
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_apply_shift
        D hlambda y
  refine spectrum.mem_resolventSet_of_left_right_inverse
    (b := -R) (c := -R) ?_ ?_
  · rw [hScalarShift]
    calc
      -S * -R = S * R := by
        apply ContinuousLinearMap.ext
        intro y
        simp
      _ = 1 := hShiftResolvent
  · rw [hScalarShift]
    calc
      -R * -S = R * S := by
        apply ContinuousLinearMap.ext
        intro y
        simp
      _ = 1 := hResolventShift

/-- No real spectral value of the strong-limit operator lies below the inherited
uniform gap. -/
theorem realHilbert_uniformCoerciveSymmetricStrongLimit_not_mem_spectrum
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    {lambda : ℝ}
    (hlambda : lambda < D.gap) :
    lambda ∉ spectrum ℝ D.limitOperator := by
  exact
    spectrum.notMem_iff.mpr
      (spectrum.mem_resolventSet_iff.mp
        (realHilbert_uniformCoerciveSymmetricStrongLimit_mem_resolventSet
          D hlambda))

/-- The real algebra spectrum of the strong-limit operator is bounded below by
the inherited positive uniform gap. -/
theorem realHilbert_uniformCoerciveSymmetricStrongLimit_spectrum_subset_Ici
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l) :
    spectrum ℝ D.limitOperator ⊆ Set.Ici D.gap := by
  intro lambda hlambdaSpectrum
  by_contra hlambdaLower
  have hlambda : lambda < D.gap := lt_of_not_ge hlambdaLower
  exact
    (realHilbert_uniformCoerciveSymmetricStrongLimit_not_mem_spectrum
      D hlambda) hlambdaSpectrum

end

end MathlibAnalytic
end MGAP4D
