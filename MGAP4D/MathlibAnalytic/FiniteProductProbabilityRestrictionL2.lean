import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

universe u v

/-- Restriction of a finite product probability variable to an arbitrary
finite coordinate block is measure-preserving.

Mathlib first splits the full product into the selected subtype and its
complement by `measurePreserving_piEquivPiSubtypeProd`; the first projection
then forgets the complementary probability block.  Thus no coordinate-wise
independence calculation is reproduced here. -/
theorem measurePreserving_finiteProductProbabilityRestriction
    {ι : Type u} [Fintype ι]
    {α : ι → Type v}
    [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset ι) :
    MeasurePreserving
      (fun (x : ∀ i, α i) (i : s) => x i)
      (Measure.pi μ)
      (Measure.pi fun i : s => μ i) := by
  classical
  let p : ι → Prop := fun i => i ∈ s
  have hSplit :=
    MeasureTheory.measurePreserving_piEquivPiSubtypeProd (μ := μ) p
  have h := MeasureTheory.measurePreserving_fst.comp hSplit
  simpa [p, Function.comp_def] using h

/-- Exact real `L²` pullback from a selected finite block of coordinates into
the full finite product probability space. -/
noncomputable def finiteProductProbabilityRestrictionL2Pullback
    {ι : Type u} [Fintype ι]
    {α : ι → Type v}
    [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset ι) :
    Lp ℝ 2 (Measure.pi fun i : s => μ i) →ₗᵢ[ℝ]
      Lp ℝ 2 (Measure.pi μ) :=
  Lp.compMeasurePreservingₗᵢ
    (𝕜 := ℝ)
    (fun (x : ∀ i, α i) (i : s) => x i)
    (measurePreserving_finiteProductProbabilityRestriction μ s)

/-- Any orthonormal family on a selected finite coordinate block remains
orthonormal after pullback to the full product probability `L²` space. -/
theorem finiteProductProbabilityRestrictionL2Pullback_orthonormal
    {ι : Type u} [Fintype ι]
    {α : ι → Type v}
    [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset ι)
    {κ : Type*}
    (v : κ → Lp ℝ 2 (Measure.pi fun i : s => μ i))
    (hv : Orthonormal ℝ v) :
    Orthonormal ℝ
      ((finiteProductProbabilityRestrictionL2Pullback μ s) ∘ v) :=
  hv.comp_linearIsometry
    (finiteProductProbabilityRestrictionL2Pullback μ s)

end

end MathlibAnalytic
end MGAP4D
