import MGAP4D.MathlibAnalytic.RealHilbertUniformCoerciveSymmetricStrongLimitSpectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Topology

/-- Changing the real shift parameter changes the bounded strong-limit shift by
the corresponding scalar multiple of the input vector. -/
theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limitShiftOperator_change_parameter
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    (lambda mu : ℝ)
    (x : E) :
    D.limitShiftOperator lambda x =
      D.limitShiftOperator mu x + (mu - lambda) • x := by
  simp only [
    realHilbert_uniformCoerciveSymmetricStrongLimit_limitShiftOperator_apply]
  module

/-- Every shift below the inherited gap is injective. -/
theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limitShiftOperator_injective
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    {lambda : ℝ}
    (hlambda : lambda < D.gap) :
    Function.Injective (D.limitShiftOperator lambda) := by
  intro x z hxz
  have h := congrArg (fun y => D.limitResolvent hlambda y) hxz
  simpa only [
    realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_apply_shift]
    using h

/-- Pointwise resolvent identity for the bounded strong-limit operator. -/
theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_sub_apply
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    {lambda mu : ℝ}
    (hlambda : lambda < D.gap)
    (hmu : mu < D.gap)
    (y : E) :
    D.limitResolvent hlambda y - D.limitResolvent hmu y =
      (lambda - mu) •
        D.limitResolvent hlambda (D.limitResolvent hmu y) := by
  let xmu : E := D.limitResolvent hmu y
  have hShiftMu : D.limitShiftOperator mu xmu = y := by
    simpa [xmu] using
      realHilbert_uniformCoerciveSymmetricStrongLimit_limitShift_apply_resolvent
        D hmu y
  have hShiftAtLambda :
      D.limitShiftOperator lambda xmu = y + (mu - lambda) • xmu := by
    calc
      D.limitShiftOperator lambda xmu =
          D.limitShiftOperator mu xmu + (mu - lambda) • xmu :=
        realHilbert_uniformCoerciveSymmetricStrongLimit_limitShiftOperator_change_parameter
          D lambda mu xmu
      _ = y + (mu - lambda) • xmu := by rw [hShiftMu]
  have hApply := congrArg (fun z => D.limitResolvent hlambda z) hShiftAtLambda
  have hEq :
      xmu = D.limitResolvent hlambda y +
        (mu - lambda) • D.limitResolvent hlambda xmu := by
    simpa [map_add, map_smul] using hApply
  change
    D.limitResolvent hlambda y - xmu =
      (lambda - mu) • D.limitResolvent hlambda xmu
  rw [hEq]
  module

/-- Resolvent identity as an equality of bounded operators. -/
theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_identity
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    {lambda mu : ℝ}
    (hlambda : lambda < D.gap)
    (hmu : mu < D.gap) :
    D.limitResolvent hlambda - D.limitResolvent hmu =
      (lambda - mu) •
        ((D.limitResolvent hlambda).comp (D.limitResolvent hmu)) := by
  ext y
  exact
    realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_sub_apply
      D hlambda hmu y

/-- Resolvents of the same bounded strong-limit operator commute at all real
parameters below the inherited gap. -/
theorem realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_comp_comm
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveSymmetricStrongLimitData ι E l)
    {lambda mu : ℝ}
    (hlambda : lambda < D.gap)
    (hmu : mu < D.gap) :
    (D.limitResolvent hlambda).comp (D.limitResolvent hmu) =
      (D.limitResolvent hmu).comp (D.limitResolvent hlambda) := by
  apply ContinuousLinearMap.ext
  intro y
  apply
    realHilbert_uniformCoerciveSymmetricStrongLimit_limitShiftOperator_injective
      D hlambda
  calc
    D.limitShiftOperator lambda
        (((D.limitResolvent hlambda).comp (D.limitResolvent hmu)) y) =
      D.limitResolvent hmu y := by
        simpa only [ContinuousLinearMap.comp_apply] using
          realHilbert_uniformCoerciveSymmetricStrongLimit_limitShift_apply_resolvent
            D hlambda (D.limitResolvent hmu y)
    _ = D.limitResolvent hlambda y +
        (mu - lambda) •
          D.limitResolvent hmu (D.limitResolvent hlambda y) := by
      have hIdentity :=
        realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_sub_apply
          D hmu hlambda y
      rw [← hIdentity]
      abel
    _ = D.limitShiftOperator lambda
        (((D.limitResolvent hmu).comp (D.limitResolvent hlambda)) y) := by
      symm
      calc
        D.limitShiftOperator lambda
            (((D.limitResolvent hmu).comp (D.limitResolvent hlambda)) y) =
          D.limitShiftOperator mu
              (D.limitResolvent hmu (D.limitResolvent hlambda y)) +
            (mu - lambda) •
              D.limitResolvent hmu (D.limitResolvent hlambda y) := by
            simpa only [ContinuousLinearMap.comp_apply] using
              realHilbert_uniformCoerciveSymmetricStrongLimit_limitShiftOperator_change_parameter
                D lambda mu
                  (D.limitResolvent hmu (D.limitResolvent hlambda y))
        _ = D.limitResolvent hlambda y +
            (mu - lambda) •
              D.limitResolvent hmu (D.limitResolvent hlambda y) := by
          rw [
            realHilbert_uniformCoerciveSymmetricStrongLimit_limitShift_apply_resolvent]

end

end MathlibAnalytic
end MGAP4D
