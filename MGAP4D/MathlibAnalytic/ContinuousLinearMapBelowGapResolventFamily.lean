import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventFactorialDerivative
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap

namespace MGAP4D
namespace MathlibAnalytic

/-- Totalize a proof-indexed family of bounded resolvents by setting it equal to
zero outside its open below-gap domain.  On the domain, proof irrelevance makes
this definition independent of the supplied inequality witness. -/
noncomputable def belowGapContinuousLinearMapFamily
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (gap : ℝ) (R : ∀ lambda : ℝ, lambda < gap → E →L[ℝ] E) :
    ℝ → E →L[ℝ] E :=
  fun lambda => if h : lambda < gap then R lambda h else 0

@[simp]
theorem belowGapContinuousLinearMapFamily_of_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (gap : ℝ) (R : ∀ lambda : ℝ, lambda < gap → E →L[ℝ] E)
    {lambda : ℝ} (hlambda : lambda < gap) :
    belowGapContinuousLinearMapFamily gap R lambda = R lambda hlambda := by
  simp [belowGapContinuousLinearMapFamily, hlambda]

@[simp]
theorem belowGapContinuousLinearMapFamily_of_not_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (gap : ℝ) (R : ∀ lambda : ℝ, lambda < gap → E →L[ℝ] E)
    {lambda : ℝ} (hlambda : ¬ lambda < gap) :
    belowGapContinuousLinearMapFamily gap R lambda = 0 := by
  simp [belowGapContinuousLinearMapFamily, hlambda]

/-- The standard two-parameter reciprocal-gap estimate implies operator-norm
continuity of the totalized resolvent on the open below-gap half-line. -/
theorem belowGapContinuousLinearMapFamily_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (gap : ℝ) (R : ∀ lambda : ℝ, lambda < gap → E →L[ℝ] E)
    (hsub : ∀ {lambda mu : ℝ}
      (hlambda : lambda < gap) (hmu : mu < gap),
      ‖R lambda hlambda - R mu hmu‖ ≤
        |lambda - mu| * ((gap - lambda)⁻¹ * (gap - mu)⁻¹)) :
    ContinuousOn (belowGapContinuousLinearMapFamily gap R) (Set.Iio gap) := by
  intro lambda hlambda
  let F := belowGapContinuousLinearMapFamily gap R
  have hSubFull :
      Tendsto (fun mu : ℝ => mu - lambda) (𝓝 lambda) (𝓝 0) := by
    simpa using
      (tendsto_id.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => lambda) (𝓝 lambda) (𝓝 lambda)))
  have hAbsFull :
      Tendsto (fun mu : ℝ => |mu - lambda|) (𝓝 lambda) (𝓝 0) := by
    simpa [Real.norm_eq_abs] using hSubFull.norm
  have hAbs :
      Tendsto (fun mu : ℝ => |mu - lambda|)
        (𝓝[Set.Iio gap] lambda) (𝓝 0) :=
    hAbsFull.mono_left inf_le_left
  have hGapSubFull :
      Tendsto (fun mu : ℝ => gap - mu) (𝓝 lambda) (𝓝 (gap - lambda)) :=
    tendsto_const_nhds.sub tendsto_id
  have hGapNe : gap - lambda ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt hlambda)
  have hInvFull :
      Tendsto (fun mu : ℝ => (gap - mu)⁻¹)
        (𝓝 lambda) (𝓝 ((gap - lambda)⁻¹)) :=
    hGapSubFull.inv₀ hGapNe
  have hInv :
      Tendsto (fun mu : ℝ => (gap - mu)⁻¹)
        (𝓝[Set.Iio gap] lambda) (𝓝 ((gap - lambda)⁻¹)) :=
    hInvFull.mono_left inf_le_left
  have hConstInv :
      Tendsto (fun _ : ℝ => (gap - lambda)⁻¹)
        (𝓝[Set.Iio gap] lambda) (𝓝 ((gap - lambda)⁻¹)) :=
    tendsto_const_nhds
  have hMajor :
      Tendsto
        (fun mu : ℝ =>
          |mu - lambda| *
            ((gap - mu)⁻¹ * (gap - lambda)⁻¹))
        (𝓝[Set.Iio gap] lambda) (𝓝 0) := by
    simpa using hAbs.mul (hInv.mul hConstInv)
  have hDiff :
      Tendsto (fun mu : ℝ => F mu - F lambda)
        (𝓝[Set.Iio gap] lambda) (𝓝 0) := by
    refine squeeze_zero_norm'
      (a := fun mu : ℝ =>
        |mu - lambda| * ((gap - mu)⁻¹ * (gap - lambda)⁻¹))
      ?_ hMajor
    filter_upwards [self_mem_nhdsWithin] with mu hmu
    have hFmu : F mu = R mu hmu := by
      dsimp [F]
      exact belowGapContinuousLinearMapFamily_of_lt gap R hmu
    have hFlambda : F lambda = R lambda hlambda := by
      dsimp [F]
      exact belowGapContinuousLinearMapFamily_of_lt gap R hlambda
    rw [hFmu, hFlambda]
    exact hsub hmu hlambda
  have hAdd := hDiff.add
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => F lambda)
        (𝓝[Set.Iio gap] lambda) (𝓝 (F lambda)))
  simpa [sub_add_cancel] using hAdd

/-- A proof-indexed below-gap resolvent family together with its quantitative
continuity and exact resolvent identity canonically determines the abstract
open-resolvent calculus. -/
noncomputable def ContinuousLinearMapOpenResolventData.ofBelowGapFamily
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (gap : ℝ) (R : ∀ lambda : ℝ, lambda < gap → E →L[ℝ] E)
    (hsub : ∀ {lambda mu : ℝ}
      (hlambda : lambda < gap) (hmu : mu < gap),
      ‖R lambda hlambda - R mu hmu‖ ≤
        |lambda - mu| * ((gap - lambda)⁻¹ * (gap - mu)⁻¹))
    (hidentity : ∀ {lambda mu : ℝ}
      (hlambda : lambda < gap) (hmu : mu < gap),
      R lambda hlambda - R mu hmu =
        (lambda - mu) • ((R lambda hlambda).comp (R mu hmu))) :
    ContinuousLinearMapOpenResolventData E where
  gap := gap
  resolvent := belowGapContinuousLinearMapFamily gap R
  continuousOn := belowGapContinuousLinearMapFamily_continuousOn gap R hsub
  resolvent_identity := by
    intro lambda mu hlambda hmu
    have hLambda :
        belowGapContinuousLinearMapFamily gap R lambda = R lambda hlambda :=
      belowGapContinuousLinearMapFamily_of_lt gap R hlambda
    have hMu :
        belowGapContinuousLinearMapFamily gap R mu = R mu hmu :=
      belowGapContinuousLinearMapFamily_of_lt gap R hmu
    rw [hLambda, hMu]
    exact hidentity hlambda hmu

end MathlibAnalytic
end MGAP4D
