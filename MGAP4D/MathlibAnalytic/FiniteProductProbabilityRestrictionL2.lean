import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

universe u v

/-- Restriction of a finite product probability variable to any decidable
coordinate predicate is measure-preserving.

Mathlib first splits the full product into the selected subtype and its
complement by `measurePreserving_piEquivPiSubtypeProd`; the first projection
then forgets the complementary probability block.  Working directly with the
predicate subtype also keeps the `Fintype` instance definitionally identical
to the one used by Mathlib's split theorem. -/
theorem measurePreserving_finiteProductProbabilityRestriction
    {ι : Type u} [Fintype ι]
    {α : ι → Type v}
    [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving
      (fun (x : ∀ i, α i) (i : Subtype p) => x i)
      (Measure.pi μ)
      (Measure.pi fun i : Subtype p => μ i) := by
  have hSplit :=
    MeasureTheory.measurePreserving_piEquivPiSubtypeProd (μ := μ) p
  have h := MeasureTheory.measurePreserving_fst.comp hSplit
  simpa [Function.comp_def] using h

/-- Exact real `L²` pullback from a predicate-selected coordinate block into
the full finite product probability space. -/
noncomputable def finiteProductProbabilityRestrictionL2Pullback
    {ι : Type u} [Fintype ι]
    {α : ι → Type v}
    [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    Lp ℝ 2 (Measure.pi fun i : Subtype p => μ i) →ₗᵢ[ℝ]
      Lp ℝ 2 (Measure.pi μ) :=
  Lp.compMeasurePreservingₗᵢ
    (𝕜 := ℝ)
    (fun (x : ∀ i, α i) (i : Subtype p) => x i)
    (measurePreserving_finiteProductProbabilityRestriction μ p)

/-- Any orthonormal family on a predicate-selected finite coordinate block
remains orthonormal after pullback to the full product probability `L²`
space. -/
theorem finiteProductProbabilityRestrictionL2Pullback_orthonormal
    {ι : Type u} [Fintype ι]
    {α : ι → Type v}
    [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p]
    {κ : Type*}
    (v : κ → Lp ℝ 2 (Measure.pi fun i : Subtype p => μ i))
    (hv : Orthonormal ℝ v) :
    Orthonormal ℝ
      ((finiteProductProbabilityRestrictionL2Pullback μ p) ∘ v) :=
  hv.comp_linearIsometry
    (finiteProductProbabilityRestrictionL2Pullback μ p)

end

end MathlibAnalytic
end MGAP4D
