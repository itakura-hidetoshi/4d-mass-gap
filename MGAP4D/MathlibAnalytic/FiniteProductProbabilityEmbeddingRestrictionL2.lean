import MGAP4D.MathlibAnalytic.FiniteProductProbabilityRestrictionL2
import Mathlib.MeasureTheory.Constructions.Pi

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

universe u v w

/-- An embedding is canonically equivalent to its range subtype.

This small generic equivalence is stated explicitly because the pinned Mathlib
API does not expose an `Embedding.equivRange` projection. -/
noncomputable def finiteEmbeddingRangeEquiv
    {κ : Type v} {ι : Type u}
    (e : κ ↪ ι) :
    κ ≃ {i : ι // i ∈ Set.range e} where
  toFun k := ⟨e k, ⟨k, rfl⟩⟩
  invFun i := Classical.choose i.property
  left_inv k := by
    apply e.injective
    exact Classical.choose_spec
      (show e k ∈ Set.range e from ⟨k, rfl⟩)
  right_inv i := by
    apply Subtype.ext
    exact Classical.choose_spec i.property

@[simp]
theorem finiteEmbeddingRangeEquiv_apply_coe
    {κ : Type v} {ι : Type u}
    (e : κ ↪ ι) (k : κ) :
    ((finiteEmbeddingRangeEquiv e k : {i : ι // i ∈ Set.range e}) : ι) = e k :=
  rfl

/-- Coordinate extraction along a finite index embedding preserves a homogeneous
product probability measure.

The proof first restricts the full product to the range subtype of the
embedding, then reindexes that subtype back to the source index through the
explicit range equivalence above. Both steps are Mathlib measure-preserving
maps. -/
theorem measurePreserving_finiteProductProbabilityEmbeddingRestriction
    {ι : Type u} [Fintype ι]
    {κ : Type v} [Fintype κ]
    {α : Type w} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (e : κ ↪ ι) :
    MeasurePreserving
      (fun (x : ι → α) (k : κ) => x (e k))
      (Measure.pi fun _ : ι => μ)
      (Measure.pi fun _ : κ => μ) := by
  classical
  let p : ι → Prop := fun i => i ∈ Set.range e
  letI : Fintype (Subtype p) := Subtype.fintype p
  have hRestrict :
      MeasurePreserving
        (fun (x : ι → α) (i : Subtype p) => x i)
        (Measure.pi fun _ : ι => μ)
        (Measure.pi fun _ : Subtype p => μ) :=
    measurePreserving_finiteProductProbabilityRestriction
      (fun _ : ι => μ) p
  let erange : κ ≃ Subtype p := finiteEmbeddingRangeEquiv e
  have hReindex :
      MeasurePreserving
        (MeasurableEquiv.piCongrLeft (fun _ : κ => α) erange.symm)
        (Measure.pi fun _ : Subtype p => μ)
        (Measure.pi fun _ : κ => μ) := by
    simpa using
      (MeasureTheory.measurePreserving_piCongrLeft
        (fun _ : κ => μ) erange.symm)
  have h := hReindex.comp hRestrict
  convert h using 1
  funext x k
  have hk :=
    MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : κ => α)
      erange.symm
      (fun i : Subtype p => x i)
      (erange k)
  simpa [erange, p] using hk.symm

/-- Exact real `L²` pullback from the coordinates selected by a finite embedding
into the full homogeneous product probability space. -/
noncomputable def finiteProductProbabilityEmbeddingRestrictionL2Pullback
    {ι : Type u} [Fintype ι]
    {κ : Type v} [Fintype κ]
    {α : Type w} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (e : κ ↪ ι) :
    Lp ℝ 2 (Measure.pi fun _ : κ => μ) →ₗᵢ[ℝ]
      Lp ℝ 2 (Measure.pi fun _ : ι => μ) :=
  Lp.compMeasurePreservingₗᵢ
    (𝕜 := ℝ)
    (fun (x : ι → α) (k : κ) => x (e k))
    (measurePreserving_finiteProductProbabilityEmbeddingRestriction μ e)

/-- Orthonormal families on finitely embedded coordinates remain orthonormal
after pullback to the full homogeneous product probability space. -/
theorem finiteProductProbabilityEmbeddingRestrictionL2Pullback_orthonormal
    {ι : Type u} [Fintype ι]
    {κ : Type v} [Fintype κ]
    {α : Type w} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (e : κ ↪ ι)
    {γ : Type*}
    (v : γ → Lp ℝ 2 (Measure.pi fun _ : κ => μ))
    (hv : Orthonormal ℝ v) :
    Orthonormal ℝ
      ((finiteProductProbabilityEmbeddingRestrictionL2Pullback μ e) ∘ v) :=
  hv.comp_linearIsometry
    (finiteProductProbabilityEmbeddingRestrictionL2Pullback μ e)

end

end MathlibAnalytic
end MGAP4D
