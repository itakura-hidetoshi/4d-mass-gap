import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathCondExpL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- On every strongly measurable uniformly bounded observable, the abstract
`condExpL2` heat-bath projection is exactly the `L²` class of the concrete
Haar-kernel conditional expectation. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjectionL2_toLp_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f)
    (M : ℝ)
    (hM0 : 0 ≤ M)
    (hM : ∀ A, |f A| ≤ M) :
    C.singleLinkHeatBathProjectionL2 target
        ((continuous_compact_oriented_memLp_two_of_uniform_bound
          C f hf M hM0 hM).toLp f) =
      ((continuous_compact_oriented_memLp_two_of_uniform_bound
        C (C.singleLinkHeatBathProjection target f)
        (continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
          C target f hf)
        M hM0
        (continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
          C target f hf M hM0 hM)).toLp
        (C.singleLinkHeatBathProjection target f)) := by
  let hfLp : MemLp f 2 C.gibbsMeasure :=
    continuous_compact_oriented_memLp_two_of_uniform_bound
      C f hf M hM0 hM
  let Pf : C.base.Configuration → ℝ :=
    C.singleLinkHeatBathProjection target f
  have hPfStrong : StronglyMeasurable Pf :=
    continuous_compact_oriented_singleLinkHeatBathProjection_stronglyMeasurable
      C target f hf
  have hPfBound : ∀ A, |Pf A| ≤ M :=
    continuous_compact_oriented_singleLinkHeatBathProjection_abs_le
      C target f hf M hM0 hM
  let hPfLp : MemLp Pf 2 C.gibbsMeasure :=
    continuous_compact_oriented_memLp_two_of_uniform_bound
      C Pf hPfStrong M hM0 hPfBound
  have hae : Pf =ᵐ[C.gibbsMeasure]
      (condExpL2 ℝ ℝ
        (compact_oriented_offLinkMeasurableSpace_le C.base target)
        (hfLp.toLp f) : Lp ℝ 2 C.gibbsMeasure) := by
    simpa [Pf, hfLp] using
      continuous_compact_oriented_singleLinkHeatBathProjection_ae_eq_condExpL2
        C target f hf M hM0 hM
  apply Lp.ext
  rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_apply]
  exact hae.symm.trans hPfLp.coeFn_toLp.symm

end

end MathlibAnalytic
end MGAP4D
