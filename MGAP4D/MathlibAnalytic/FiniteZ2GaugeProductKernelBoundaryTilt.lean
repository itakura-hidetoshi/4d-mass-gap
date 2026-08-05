import MGAP4D.MathlibAnalytic.FinitePositiveKernelNormalizerTiltCrossRatio
import MGAP4D.MathlibAnalytic.FinitePositiveWeightLocalTiltConditional
import MGAP4D.MathlibAnalytic.FiniteZ2GaugeProductKernelLikelihoodRatio
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Strict positivity of every normalized local `Z₂` crossing entry for
`0 ≤ q < 1`. -/
theorem finiteZ2NormalizedLocalKernel_pos_of_nonneg_lt_one
    {q : ℝ}
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (x y : Bool) :
    0 < finiteZ2NormalizedLocalKernel q x y := by
  by_cases hxy : x = y
  · simp [finiteZ2NormalizedLocalKernel, hxy]
    linarith
  · simp [finiteZ2NormalizedLocalKernel, hxy]
    linarith

/-- Strict positivity of every actual-carrier normalized product-kernel entry. -/
theorem finiteZ2GaugeNormalizedProductKernel_pos
    {q : ℝ}
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (ι : Type)
    [Fintype ι]
    [DecidableEq ι]
    (hidden environment : ι → Z2Gauge) :
    0 < finiteZ2GaugeNormalizedProductKernel q ι hidden environment := by
  rw [finiteZ2GaugeNormalizedProductKernel_apply]
  exact Finset.prod_pos fun coordinate _hCoordinate =>
    finiteZ2NormalizedLocalKernel_pos_of_nonneg_lt_one
      hq0 hq1
      (boolEquivZ2Gauge.symm (hidden coordinate))
      (boolEquivZ2Gauge.symm (environment coordinate))

/-- Hidden-state Radon--Nikodym tilt for changing one observed coordinate of
the normalized product crossing kernel. -/
def finiteZ2GaugeNormalizedProductKernelBoundaryTilt
    (q : ℝ)
    {ι : Type}
    [DecidableEq ι]
    (base : ι → Z2Gauge)
    (source : ι)
    (replacement : Z2Gauge)
    (hidden : ι → Z2Gauge) : ℝ :=
  finiteZ2NormalizedLocalKernel q
      (boolEquivZ2Gauge.symm (hidden source))
      (boolEquivZ2Gauge.symm replacement) /
    finiteZ2NormalizedLocalKernel q
      (boolEquivZ2Gauge.symm (hidden source))
      (boolEquivZ2Gauge.symm (base source))

/-- The one-coordinate product-kernel tilt is strictly positive. -/
theorem finiteZ2GaugeNormalizedProductKernelBoundaryTilt_pos
    {q : ℝ}
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    {ι : Type}
    [DecidableEq ι]
    (base : ι → Z2Gauge)
    (source : ι)
    (replacement : Z2Gauge)
    (hidden : ι → Z2Gauge) :
    0 < finiteZ2GaugeNormalizedProductKernelBoundaryTilt
      q base source replacement hidden := by
  unfold finiteZ2GaugeNormalizedProductKernelBoundaryTilt
  exact div_pos
    (finiteZ2NormalizedLocalKernel_pos_of_nonneg_lt_one
      hq0 hq1 _ _)
    (finiteZ2NormalizedLocalKernel_pos_of_nonneg_lt_one
      hq0 hq1 _ _)

/-- The boundary tilt depends exactly on the hidden source coordinate. -/
theorem finiteZ2GaugeNormalizedProductKernelBoundaryTilt_supportedOn_source
    (q : ℝ)
    {ι : Type}
    [DecidableEq ι]
    (base : ι → Z2Gauge)
    (source : ι)
    (replacement : Z2Gauge) :
    FiniteProductFunctionSupportedOn ({source} : Finset ι)
      (finiteZ2GaugeNormalizedProductKernelBoundaryTilt
        q base source replacement) := by
  intro hidden hidden' hAgree
  unfold finiteZ2GaugeNormalizedProductKernelBoundaryTilt
  rw [hAgree source (by simp)]

/-- Replacing one observed coordinate multiplies the complete normalized
product-kernel column by the corresponding one-coordinate hidden tilt. -/
theorem finiteZ2GaugeNormalizedProductKernel_boundaryTiltRelation
    {q : ℝ}
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (ι : Type)
    [Fintype ι]
    [DecidableEq ι]
    (base : ι → Z2Gauge)
    (source : ι)
    (replacement : Z2Gauge) :
    FinitePositiveKernelBoundaryTiltRelation
      (finiteZ2GaugeNormalizedProductKernel q ι)
      base
      (finiteZ2GaugeReplaceCoordinate base source replacement)
      (finiteZ2GaugeNormalizedProductKernelBoundaryTilt
        q base source replacement) := by
  classical
  intro hidden
  rw [finiteZ2GaugeNormalizedProductKernel_apply,
    finiteZ2GaugeNormalizedProductKernel_apply]
  let oldLocal :=
    finiteZ2NormalizedLocalKernel q
      (boolEquivZ2Gauge.symm (hidden source))
      (boolEquivZ2Gauge.symm (base source))
  let newLocal :=
    finiteZ2NormalizedLocalKernel q
      (boolEquivZ2Gauge.symm (hidden source))
      (boolEquivZ2Gauge.symm replacement)
  have hOldLocal : oldLocal ≠ 0 := by
    exact ne_of_gt
      (finiteZ2NormalizedLocalKernel_pos_of_nonneg_lt_one
        hq0 hq1 _ _)
  change
    (∏ coordinate : ι,
      finiteZ2NormalizedLocalKernel q
        (boolEquivZ2Gauge.symm (hidden coordinate))
        (boolEquivZ2Gauge.symm
          (finiteZ2GaugeReplaceCoordinate base source replacement coordinate))) =
      (newLocal / oldLocal) *
        ∏ coordinate : ι,
          finiteZ2NormalizedLocalKernel q
            (boolEquivZ2Gauge.symm (hidden coordinate))
            (boolEquivZ2Gauge.symm (base coordinate))
  calc
    (∏ coordinate : ι,
      finiteZ2NormalizedLocalKernel q
        (boolEquivZ2Gauge.symm (hidden coordinate))
        (boolEquivZ2Gauge.symm
          (finiteZ2GaugeReplaceCoordinate base source replacement coordinate))) =
      ∏ coordinate : ι,
        ((if coordinate = source then newLocal / oldLocal else 1) *
          finiteZ2NormalizedLocalKernel q
            (boolEquivZ2Gauge.symm (hidden coordinate))
            (boolEquivZ2Gauge.symm (base coordinate))) := by
      apply Finset.prod_congr rfl
      intro coordinate _hCoordinate
      by_cases hCoordinateSource : coordinate = source
      · subst coordinate
        rw [finiteZ2GaugeReplaceCoordinate_same]
        simp only [if_pos rfl]
        change newLocal = (newLocal / oldLocal) * oldLocal
        field_simp [hOldLocal]
      · rw [finiteZ2GaugeReplaceCoordinate_noteq
          base source coordinate replacement hCoordinateSource]
        simp [hCoordinateSource]
    _ =
      (∏ coordinate : ι,
        if coordinate = source then newLocal / oldLocal else 1) *
        ∏ coordinate : ι,
          finiteZ2NormalizedLocalKernel q
            (boolEquivZ2Gauge.symm (hidden coordinate))
            (boolEquivZ2Gauge.symm (base coordinate)) := by
      rw [Finset.prod_mul_distrib]
    _ = (newLocal / oldLocal) *
        ∏ coordinate : ι,
          finiteZ2NormalizedLocalKernel q
            (boolEquivZ2Gauge.symm (hidden coordinate))
            (boolEquivZ2Gauge.symm (base coordinate)) := by
      simp

/-- Environments agreeing off one source are related by the same exact local
product-kernel tilt. -/
theorem finiteZ2GaugeNormalizedProductKernel_boundaryTiltRelation_of_agreeOff
    {q : ℝ}
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (ι : Type)
    [Fintype ι]
    [DecidableEq ι]
    (base updated : ι → Z2Gauge)
    (source : ι)
    (hAgree : FiniteProductAgreeOff base updated source) :
    FinitePositiveKernelBoundaryTiltRelation
      (finiteZ2GaugeNormalizedProductKernel q ι)
      base updated
      (finiteZ2GaugeNormalizedProductKernelBoundaryTilt
        q base source (updated source)) := by
  have hUpdated :
      updated = finiteZ2GaugeReplaceCoordinate base source (updated source) := by
    funext coordinate
    by_cases hCoordinate : coordinate = source
    · subst coordinate
      simp
    · rw [finiteZ2GaugeReplaceCoordinate_noteq
        base source coordinate (updated source) hCoordinate]
      exact (hAgree coordinate hCoordinate).symm
  rw [hUpdated]
  simpa [finiteZ2GaugeReplaceCoordinate_same] using
    finiteZ2GaugeNormalizedProductKernel_boundaryTiltRelation
      hq0 hq1 ι base source (updated source)

end

end MathlibAnalytic
end MGAP4D
