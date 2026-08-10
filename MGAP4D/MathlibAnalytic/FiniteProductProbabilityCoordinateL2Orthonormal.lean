import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LpSpace.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

universe u v

/-- Pull one coordinate `L²` space isometrically into a finite product
probability `L²` space.

The coordinate projection is measure-preserving for finite products of
probability measures, so composition is an exact `LinearIsometry`. -/
noncomputable def finiteProductProbabilityCoordinateL2Pullback
    {ι : Type u} [Fintype ι]
    {α : ι → Type v}
    [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) :
    Lp ℝ 2 (μ i) →ₗᵢ[ℝ] Lp ℝ 2 (Measure.pi μ) :=
  Lp.compMeasurePreservingₗᵢ
    (𝕜 := ℝ)
    (Function.eval i)
    (MeasureTheory.measurePreserving_eval (μ := μ) i)

/-- Orthonormal families on one probability coordinate remain orthonormal after
pullback to the finite product probability space. -/
theorem finiteProductProbabilityCoordinateL2Pullback_orthonormal
    {ι : Type u} [Fintype ι]
    {α : ι → Type v}
    [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι)
    {κ : Type*}
    (v : κ → Lp ℝ 2 (μ i))
    (hv : Orthonormal ℝ v) :
    Orthonormal ℝ
      ((finiteProductProbabilityCoordinateL2Pullback μ i) ∘ v) :=
  hv.comp_linearIsometry
    (finiteProductProbabilityCoordinateL2Pullback μ i)

end

end MathlibAnalytic
end MGAP4D
