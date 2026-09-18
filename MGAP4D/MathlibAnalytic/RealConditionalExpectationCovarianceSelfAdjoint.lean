import MGAP4D.MathlibAnalytic.RealIntegralWeightedProbabilityNormalization
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Ordinary real covariance is invariant under almost-everywhere
replacement of its left observable. -/
theorem realIntegralCovariance_congr_left_ae
    {alpha : Type*}
    [MeasurableSpace alpha]
    (mu : Measure alpha)
    {f f' g : alpha -> Real}
    (hff' : f =ᵐ[mu] f') :
    realIntegralCovariance mu f g =
      realIntegralCovariance mu f' g := by
  have hPair :
      (fun x => f x * g x) =ᵐ[mu] fun x => f' x * g x := by
    filter_upwards [hff'] with x hx
    rw [hx]
  unfold realIntegralCovariance
  rw [integral_congr_ae hPair, integral_congr_ae hff']

/-- Ordinary real covariance is invariant under almost-everywhere
replacement of its right observable. -/
theorem realIntegralCovariance_congr_right_ae
    {alpha : Type*}
    [MeasurableSpace alpha]
    (mu : Measure alpha)
    {f g g' : alpha -> Real}
    (hgg' : g =ᵐ[mu] g') :
    realIntegralCovariance mu f g =
      realIntegralCovariance mu f g' := by
  have hPair :
      (fun x => f x * g x) =ᵐ[mu] fun x => f x * g' x := by
    filter_upwards [hgg'] with x hx
    rw [hx]
  unfold realIntegralCovariance
  rw [integral_congr_ae hPair, integral_congr_ae hgg']

/-- Conditional expectation is self-adjoint for the real integral pairing on
square-integrable functions over a probability measure.  The proof uses only
the pull-out law and preservation of the integral, not any Gibbs structure. -/
theorem realIntegral_condExp_pairing_symm_of_memLp_two
    {alpha : Type*}
    [m0 : MeasurableSpace alpha]
    (mu : Measure alpha)
    [IsProbabilityMeasure mu]
    (m : MeasurableSpace alpha)
    (hm : m <= m0)
    (f g : alpha -> Real)
    (hf : MemLp f 2 mu)
    (hg : MemLp g 2 mu) :
    (∫ x, MeasureTheory.condExp m mu f x * g x ∂mu) =
      ∫ x, f x * MeasureTheory.condExp m mu g x ∂mu := by
  let cf : alpha -> Real := MeasureTheory.condExp m mu f
  let cg : alpha -> Real := MeasureTheory.condExp m mu g
  have hfInt : Integrable f mu :=
    memLp_one_iff_integrable.1 (hf.mono_exponent one_le_two)
  have hgInt : Integrable g mu :=
    memLp_one_iff_integrable.1 (hg.mono_exponent one_le_two)
  have hcf2 : MemLp cf 2 mu := by
    simpa [cf] using (hf.condExp (m := m))
  have hcg2 : MemLp cg 2 mu := by
    simpa [cg] using (hg.condExp (m := m))
  have hcfgInt : Integrable (cf * g) mu :=
    hcf2.integrable_mul hg
  have hfcgInt : Integrable (f * cg) mu :=
    hf.integrable_mul hcg2
  have hPullLeft :
      MeasureTheory.condExp m mu (cf * g) =ᵐ[mu] cf * cg := by
    simpa [cf, cg] using
      (MeasureTheory.condExp_mul_of_aestronglyMeasurable_left
        (m := m) (μ := mu)
        (f := cf) (g := g)
        MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable
        hcfgInt hgInt)
  have hPullRight :
      MeasureTheory.condExp m mu (f * cg) =ᵐ[mu] cf * cg := by
    simpa [cf, cg] using
      (MeasureTheory.condExp_mul_of_aestronglyMeasurable_right
        (m := m) (μ := mu)
        (f := f) (g := cg)
        MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable
        hfcgInt hfInt)
  change (∫ x, cf x * g x ∂mu) = ∫ x, f x * cg x ∂mu
  calc
    (∫ x, cf x * g x ∂mu) =
        ∫ x, MeasureTheory.condExp m mu (cf * g) x ∂mu := by
      symm
      simpa only [Pi.mul_apply] using
        (MeasureTheory.integral_condExp (μ := mu) (f := cf * g) hm)
    _ = ∫ x, cf x * cg x ∂mu := by
      simpa only [Pi.mul_apply] using integral_congr_ae hPullLeft
    _ = ∫ x, MeasureTheory.condExp m mu (f * cg) x ∂mu := by
      symm
      simpa only [Pi.mul_apply] using integral_congr_ae hPullRight
    _ = ∫ x, f x * cg x ∂mu := by
      simpa only [Pi.mul_apply] using
        (MeasureTheory.integral_condExp (μ := mu) (f := f * cg) hm)

/-- The ordinary real covariance inherits the self-adjointness of conditional
expectation on L2.  This is measure-theoretic and does not assume a Gibbs law. -/
theorem realIntegralCovariance_condExp_symm_of_memLp_two
    {alpha : Type*}
    [m0 : MeasurableSpace alpha]
    (mu : Measure alpha)
    [IsProbabilityMeasure mu]
    (m : MeasurableSpace alpha)
    (hm : m <= m0)
    (f g : alpha -> Real)
    (hf : MemLp f 2 mu)
    (hg : MemLp g 2 mu) :
    @realIntegralCovariance alpha m0 mu
        (MeasureTheory.condExp m mu f) g =
      @realIntegralCovariance alpha m0 mu
        f (MeasureTheory.condExp m mu g) := by
  have hPair :=
    realIntegral_condExp_pairing_symm_of_memLp_two
      (m0 := m0) mu m hm f g hf hg
  have hMeanF :
      (∫ x, MeasureTheory.condExp m mu f x ∂mu) =
        ∫ x, f x ∂mu :=
    MeasureTheory.integral_condExp (μ := mu) (f := f) hm
  have hMeanG :
      (∫ x, MeasureTheory.condExp m mu g x ∂mu) =
        ∫ x, g x ∂mu :=
    MeasureTheory.integral_condExp (μ := mu) (f := g) hm
  unfold realIntegralCovariance
  rw [hPair, hMeanF, hMeanG]

end

end MathlibAnalytic
end MGAP4D
