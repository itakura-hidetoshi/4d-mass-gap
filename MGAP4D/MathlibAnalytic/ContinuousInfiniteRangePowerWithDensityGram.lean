import MGAP4D.MathlibAnalytic.ContinuousInfiniteRangePowerLpLinearIndependent
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.WithDensity

namespace MGAP4D
namespace MathlibAnalytic

open Function MeasureTheory Set
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

/-- A strictly positive a.e. density preserves the full-support input needed by
the canonical `ContinuousMap.toLp` power-family theorem.

The direction of absolute continuity is important: positivity of the density
gives `μ ≪ μ.withDensity w`, hence positivity on nonempty opens transfers from
`μ` to the weighted measure. -/
theorem continuousMap_infiniteRange_powerFamily_toLp_withDensity_linearIndependent
    {α : Type*}
    [TopologicalSpace α]
    [MeasurableSpace α]
    [BorelSpace α]
    [CompactSpace α]
    [SecondCountableTopologyEither α ℝ]
    {μ : Measure α}
    [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    (w : α → ENNReal)
    (hw : AEMeasurable w μ)
    (hw_ne_zero : ∀ᵐ x ∂μ, w x ≠ 0)
    [IsFiniteMeasure (μ.withDensity w)]
    {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    (f : C(α, ℝ))
    (hf : (Set.range fun x => f x).Infinite) :
    LinearIndependent ℝ
      (fun n : ℕ =>
        ContinuousMap.toLp (E := ℝ) p (μ.withDensity w) ℝ (f ^ n)) := by
  letI : Measure.IsOpenPosMeasure (μ.withDensity w) :=
    (withDensity_absolutelyContinuous' hw hw_ne_zero).isOpenPosMeasure
  exact continuousMap_infiniteRange_powerFamily_toLp_linearIndependent
    (μ := μ.withDensity w) (p := p) f hf

/-- Every finite initial power family therefore has a nonzero Gram determinant
in `L²` for any finite weighted measure whose density is nonzero almost
everywhere.

This is the weighted-moment nondegeneracy surface needed by the positive-
Wilson-coupling route: once an actual pairing matrix is reduced to such a
weighted power Gram matrix, no further determinant calculation is required. -/
theorem continuousMap_infiniteRange_powerFamily_toLp_withDensity_fin_gram_det_ne_zero
    {α : Type*}
    [TopologicalSpace α]
    [MeasurableSpace α]
    [BorelSpace α]
    [CompactSpace α]
    [SecondCountableTopologyEither α ℝ]
    {μ : Measure α}
    [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    (w : α → ENNReal)
    (hw : AEMeasurable w μ)
    (hw_ne_zero : ∀ᵐ x ∂μ, w x ≠ 0)
    [IsFiniteMeasure (μ.withDensity w)]
    (f : C(α, ℝ))
    (hf : (Set.range fun x => f x).Infinite)
    (k : ℕ) :
    (Matrix.gram ℝ
      (fun j : Fin (k + 1) =>
        ContinuousMap.toLp (E := ℝ) 2 (μ.withDensity w) ℝ
          (f ^ (j : ℕ)))).det ≠ 0 := by
  have hLI :
      LinearIndependent ℝ
        (fun n : ℕ =>
          ContinuousMap.toLp (E := ℝ) 2 (μ.withDensity w) ℝ (f ^ n)) :=
    continuousMap_infiniteRange_powerFamily_toLp_withDensity_linearIndependent
      w hw hw_ne_zero f hf
  have hFin :
      LinearIndependent ℝ
        (fun j : Fin (k + 1) =>
          ContinuousMap.toLp (E := ℝ) 2 (μ.withDensity w) ℝ
            (f ^ (j : ℕ))) := by
    simpa [Function.comp_def] using
      hLI.comp (fun j : Fin (k + 1) => (j : ℕ)) Fin.val_injective
  exact (Matrix.det_gram_ne_zero_iff_linearIndependent).mpr hFin

end

end MathlibAnalytic
end MGAP4D
