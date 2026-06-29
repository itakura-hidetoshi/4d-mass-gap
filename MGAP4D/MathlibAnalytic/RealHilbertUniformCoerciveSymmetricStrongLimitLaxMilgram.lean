import MGAP4D.MathlibAnalytic.RealHilbertUniformCoerciveStrongLimit
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Symmetric

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology

noncomputable section

structure RealHilbertUniformCoerciveSymmetricStrongLimitData
    (ι E : Type*)
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (l : Filter ι)
    extends RealHilbertUniformCoerciveStrongLimitData ι E l where
  approximant_symmetric : ∀ i : ι,
    ((approximant i : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric

theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limit_symmetric
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l) :
    (D.limitOperator : E →ₗ[ℝ] E).IsSymmetric := by
  intro f g
  have hLeft :
      Tendsto (fun i => inner ℝ (D.approximant i f) g) l
        (𝓝 (inner ℝ (D.limitOperator f) g)) :=
    (D.strong_tendsto f).inner tendsto_const_nhds
  have hRight :
      Tendsto (fun i => inner ℝ f (D.approximant i g)) l
        (𝓝 (inner ℝ f (D.limitOperator g))) :=
    tendsto_const_nhds.inner (D.strong_tendsto g)
  have hFunctions :
      (fun i => inner ℝ (D.approximant i f) g) =
        (fun i => inner ℝ f (D.approximant i g)) := by
    funext i
    exact D.approximant_symmetric i f g
  rw [hFunctions] at hLeft
  exact tendsto_nhds_unique hLeft hRight

noncomputable def
    RealHilbertUniformCoerciveSymmetricStrongLimitData.limitEnergyForm
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ).comp D.limitOperator

@[simp] theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limitEnergyForm_apply
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    (f g : E) :
    D.limitEnergyForm f g = inner ℝ (D.limitOperator f) g :=
  rfl

theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limitEnergyForm_isCoercive
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l) :
    IsCoercive D.limitEnergyForm := by
  refine ⟨D.gap, D.gap_pos, ?_⟩
  intro f
  change D.gap * ‖f‖ * ‖f‖ ≤ inner ℝ (D.limitOperator f) f
  simpa [pow_two, mul_assoc] using
    (realHilbert_uniformCoerciveStrongLimit_limit_gap
      D.toRealHilbertUniformCoerciveStrongLimitData f)

noncomputable def
    RealHilbertUniformCoerciveSymmetricStrongLimitData.limitEquivalence
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l) :
    E ≃L[ℝ] E :=
  IsCoercive.continuousLinearEquivOfBilin
    (realHilbert_uniformCoerciveSymmetricStrongLimit_limitEnergyForm_isCoercive D)

theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limitEquivalence_apply
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    (f : E) :
    D.limitEquivalence f = D.limitOperator f := by
  let hCoercive :=
    realHilbert_uniformCoerciveSymmetricStrongLimit_limitEnergyForm_isCoercive D
  symm
  change D.limitOperator f =
    IsCoercive.continuousLinearEquivOfBilin hCoercive f
  exact
    IsCoercive.unique_continuousLinearEquivOfBilin
      hCoercive (v := f) (f := D.limitOperator f) (fun _ => rfl)

theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limit_surjective
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l) :
    Function.Surjective D.limitOperator := by
  intro y
  refine ⟨D.limitEquivalence.symm y, ?_⟩
  rw [← realHilbert_uniformCoerciveSymmetricStrongLimit_limitEquivalence_apply]
  exact D.limitEquivalence.apply_symm_apply y

end

end MathlibAnalytic
end MGAP4D
