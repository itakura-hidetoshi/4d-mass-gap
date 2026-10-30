import MGAP4D.MathlibAnalytic.FiniteProductEmbeddingAssemblyIntegral
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

/-!
# Weighted finite-product kernel integration along a genuine embedding

Keep an arbitrary continuous full-configuration weight inside the actual
remote integral. The selected temporal factors split, but the full weight
need not factor or be independent of the selected coordinates.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

/-- Continuous compact-parameter integration, with an explicit integrable
constant dominator obtained from the joint continuous function's norm. -/
theorem continuous_compactParameter_integral
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [FirstCountableTopology X] [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (F : X × Y → ℝ) (hF : Continuous F) :
    Continuous (fun x : X => ∫ y : Y, F (x, y) ∂μ) := by
  let Fc : C(X × Y, ℝ) := ⟨F, hF⟩
  apply continuous_of_dominated (bound := fun _ : Y => ‖Fc‖)
  · intro x
    exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro x
    filter_upwards with y
    exact Fc.norm_coe_le_norm (x, y)
  · exact integrable_const ‖Fc‖
  · filter_upwards with y
    exact hF.comp (continuous_id.prodMk continuous_const)

/-- A strictly positive, integrable function on a probability space has
strictly positive integral. Integrability is an explicit premise. -/
theorem integral_pos_of_forall_pos_probability
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (hf : Integrable f μ) (hpos : ∀ x, 0 < f x) :
    0 < ∫ x, f x ∂μ := by
  have hs : Function.support f = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hpos x).ne'
  apply (integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) hf).mpr
  rw [hs, measure_univ]
  exact zero_lt_one

/-- Exact selected/remote formula for a product kernel with an arbitrary
continuous full weight. No factorization of the full weight is assumed. -/
theorem integral_finiteProductEmbedding_weightedKernel
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
    [SecondCountableTopology α] [CompactSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (e : κ ↪ ι)
    (q : ι → α → ℝ) (hq : ∀ i, Continuous (q i))
    (w : (ι → α) → ℝ) (hw : Continuous w)
    (f : (κ → α) → ℝ) (hf : Continuous f) :
    (∫ A : ι → α, w A * (∏ i : ι, q i (A i)) * f (fun j => A (e j))
      ∂Measure.pi (fun _ : ι => μ)) =
      ∫ x : κ → α, (∏ j : κ, q (e j) (x j)) *
        (∫ r : {i : ι // i ∉ Set.range e} → α,
          w (finiteProductEmbeddingAssemble e x r) *
            (∏ i : {i : ι // i ∉ Set.range e}, q i.1 (r i))
          ∂Measure.pi (fun _ : {i : ι // i ∉ Set.range e} => μ)) * f x
        ∂Measure.pi (fun _ : κ => μ) := by
  have hprod : Continuous (fun A : ι → α => ∏ i : ι, q i (A i)) :=
    continuous_finset_prod _ (fun i _ => (hq i).comp (continuous_apply i))
  have hcoords : Continuous (fun A : ι → α => fun j : κ => A (e j)) :=
    continuous_pi (fun j => continuous_apply (e j))
  have hsplit := integral_finiteProductEmbeddingAssemble μ e
    (fun A : ι → α => w A * (∏ i : ι, q i (A i)) * f (fun j => A (e j)))
    ((hw.mul hprod).mul (hf.comp hcoords))
  rw [hsplit]
  apply integral_congr_ae
  filter_upwards with x
  have hc (r : {i : ι // i ∉ Set.range e} → α) :
      (fun j : κ => finiteProductEmbeddingAssemble e x r (e j)) = x := by
    funext j
    exact finiteProductEmbeddingAssemble_selected e x r j
  calc
    _ = ∫ r : {i : ι // i ∉ Set.range e} → α,
        ((∏ j : κ, q (e j) (x j)) * f x) *
          (w (finiteProductEmbeddingAssemble e x r) *
            (∏ i : {i : ι // i ∉ Set.range e}, q i.1 (r i)))
          ∂Measure.pi (fun _ : {i : ι // i ∉ Set.range e} => μ) := by
      apply integral_congr_ae
      filter_upwards with r
      rw [hc r, finiteProductEmbeddingAssemble_prod]
      ring
    _ = _ := by
      rw [integral_const_mul]
      ring

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.continuous_compactParameter_integral
#print axioms MGAP4D.MathlibAnalytic.integral_pos_of_forall_pos_probability
#print axioms MGAP4D.MathlibAnalytic.integral_finiteProductEmbedding_weightedKernel
