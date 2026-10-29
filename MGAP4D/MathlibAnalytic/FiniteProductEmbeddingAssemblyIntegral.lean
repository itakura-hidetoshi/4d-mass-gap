import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic

/-!
# Finite product assembly along an embedding

Actual selected coordinates and the actual complementary coordinates are
reassembled by the measurable product splitting. No substitute law is used.
The continuous-test Fubini theorem proves integrability before iterating.
The range/complement predicates are kept explicit throughout, avoiding
hidden finite-enumeration choices for a locally aliased predicate.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

universe u v w

/-- Reassemble selected coordinates and their full complement. -/
noncomputable def finiteProductEmbeddingAssemble
    {ι : Type u} {κ : Type v} {α : Type w} [MeasurableSpace α]
    (e : κ ↪ ι) (x : κ → α) (r : {i : ι // i ∉ Set.range e} → α) : ι → α :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => α)
    (fun i => i ∈ Set.range e)).symm
    ((MeasurableEquiv.piCongrLeft (fun _ : {i : ι // i ∈ Set.range e} => α)
      (Equiv.ofInjective e e.injective)) x, r)

/-- Explicitly remove the dependent transport cast in piCongrLeft.
This equality is propositional, not an assumed definitional reduction. -/
private theorem finiteProductEmbeddingAssemble_apply
    {ι : Type u} {κ : Type v} {α : Type w} [MeasurableSpace α]
    (e : κ ↪ ι) (x : κ → α) (r : {i : ι // i ∉ Set.range e} → α) (i : ι) :
    finiteProductEmbeddingAssemble e x r i =
      if h : i ∈ Set.range e then
        x ((Equiv.ofInjective e e.injective).symm ⟨i, h⟩) else r ⟨i, h⟩ := by
  simp only [finiteProductEmbeddingAssemble,
    MeasurableEquiv.piEquivPiSubtypeProd_symm_apply,
    MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, cast_eq]

/-- Reconstruction preserves each selected coordinate exactly. -/
theorem finiteProductEmbeddingAssemble_selected
    {ι : Type u} {κ : Type v} {α : Type w} [MeasurableSpace α]
    (e : κ ↪ ι) (x : κ → α) (r : {i : ι // i ∉ Set.range e} → α) (j : κ) :
    finiteProductEmbeddingAssemble e x r (e j) = x j := by
  rw [finiteProductEmbeddingAssemble_apply,
    dif_pos (show e j ∈ Set.range e from ⟨j, rfl⟩)]
  exact congrArg x ((Equiv.ofInjective e e.injective).symm_apply_apply j)

/-- Reconstruction preserves every actual remote coordinate exactly. -/
theorem finiteProductEmbeddingAssemble_remote
    {ι : Type u} {κ : Type v} {α : Type w} [MeasurableSpace α]
    (e : κ ↪ ι) (x : κ → α) (r : {i : ι // i ∉ Set.range e}) :
    finiteProductEmbeddingAssemble e x r i.1 = r i := by
  rw [finiteProductEmbeddingAssemble_apply, dif_neg i.2]

/-- Reconstruction is jointly continuous in the selected and remote data. -/
theorem finiteProductEmbeddingAssemble_continuous
    {ι : Type u} {κ : Type v} {α : Type w}
    [MeasurableSpace α] [TopologicalSpace α] (e : κ ↪ ι) :
    Continuous (fun z : (κ → α) × ({i : ι // i ∉ Set.range e} → α) =>
      finiteProductEmbeddingAssemble e z.1 z.2) := by
  apply continuous_pi
  intro i
  simp_rw [finiteProductEmbeddingAssemble_apply]
  by_cases hi : i ∈ Set.range e
  · simpa only [dif_pos hi] using
      ((continuous_apply ((Equiv.ofInjective e e.injective).symm ⟨i, hi⟩)).comp
        (continuous_fst : Continuous (fun z : (κ → α) ×
          ({i : ι // i ∉ Set.range e} → α) => z.1)))
  · simpa only [dif_neg hi] using
      ((continuous_apply (⟨i, hi⟩ : {i : ι // i ∉ Set.range e})).comp
        (continuous_snd : Continuous (fun z : (κ → α) ×
          ({i : ι // i ∉ Set.range e} → α) => z.2)))

/-- The full coordinate product splits into exactly the selected and remote
products under reconstruction. -/
theorem finiteProductEmbeddingAssemble_prod
    {ι : Type u} {κ : Type v} {α : Type w}
    [Fintype ι] [Fintype κ] [MeasurableSpace α]
    (e : κ ↪ ι) (q : ι → α → ℝ) (x : κ → α)
    (r : {i : ι // i ∉ Set.range e} → α) :
    (∏ i : ι, q i (finiteProductEmbeddingAssemble e x r i)) =
      (∏ j : κ, q (e j) (x j)) * ∏ i : {i : ι // i ∉ Set.range e}, q i.1 (r i) := by
  letI : Fintype {i : ι // i ∈ Set.range e} := Subtype.fintype (fun i => i ∈ Set.range e)
  let erange : κ ≃ {i : ι // i ∈ Set.range e} := Equiv.ofInjective e e.injective
  have hselected :
      (∏ i : {i : ι // i ∈ Set.range e}, q i.1 (finiteProductEmbeddingAssemble e x r i.1)) =
        ∏ j : κ, q (e j) (finiteProductEmbeddingAssemble e x r (e j)) :=
    (erange.prod_comp (fun i : {i : ι // i ∈ Set.range e} =>
      q i.1 (finiteProductEmbeddingAssemble e x r i.1))).symm
  calc
    _ = (∏ i : {i : ι // i ∈ Set.range e}, q i.1 (finiteProductEmbeddingAssemble e x r i.1)) *
        ∏ i : {i : ι // i ∉ Set.range e}, q i.1 (finiteProductEmbeddingAssemble e x r i.1) :=
      (Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ Set.range e)
        (fun i => q i (finiteProductEmbeddingAssemble e x r i))).symm
    _ = _ := by
      rw [hselected]
      simp_rw [finiteProductEmbeddingAssemble_selected,
        finiteProductEmbeddingAssemble_remote]

/-- Continuous tests on a finite compact product admit exact selected/remote
Fubini integration with the original product probability measure. -/
theorem integral_finiteProductEmbeddingAssemble
    {ι : Type u} {κ : Type v} {α : Type w}
    [Fintype ι] [Fintype κ] [MeasurableSpace α] [TopologicalSpace α]
    [BorelSpace α] [SecondCountableTopology α] [CompactSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (e : κ ↪ ι) (F : (ι → α) → ℝ) (hF : Continuous F) :
    (∫ A : ι → α, F A ∂Measure.pi (fun _ : ι => μ)) =
      ∫ x : κ → α, ∫ r : {i : ι // i ∉ Set.range e} → α,
        F (finiteProductEmbeddingAssemble e x r)
          ∂Measure.pi (fun _ : {i : ι // i ∉ Set.range e} => μ)
          ∂Measure.pi (fun _ : κ => μ) := by
  letI : Fintype {i : ι // i ∈ Set.range e} := Subtype.fintype (fun i => i ∈ Set.range e)
  let erange : κ ≃ {i : ι // i ∈ Set.range e} := Equiv.ofInjective e e.injective
  let split := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => α)
    (fun i => i ∈ Set.range e)
  let reindex := MeasurableEquiv.piCongrLeft (fun _ : {i : ι // i ∈ Set.range e} => α) erange
  have hSplit := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ)
    (fun i => i ∈ Set.range e)
  have hReindex := measurePreserving_piCongrLeft
    (fun _ : {i : ι // i ∈ Set.range e} => μ) erange
  have hJoin : Continuous (fun z : ({i : ι // i ∈ Set.range e} → α) ×
      ({i : ι // i ∉ Set.range e} → α) => split.symm z) := by
    apply continuous_pi
    intro i
    change Continuous (fun z : ({i : ι // i ∈ Set.range e} → α) ×
      ({i : ι // i ∉ Set.range e} → α) =>
      if hi : i ∈ Set.range e then z.1 ⟨i, hi⟩ else z.2 ⟨i, hi⟩)
    by_cases hi : i ∈ Set.range e
    · simpa only [dif_pos hi] using
        ((continuous_apply (⟨i, hi⟩ : {i : ι // i ∈ Set.range e})).comp
          (continuous_fst : Continuous (fun z : ({i : ι // i ∈ Set.range e} → α) ×
            ({i : ι // i ∉ Set.range e} → α) => z.1)))
    · simpa only [dif_neg hi] using
        ((continuous_apply (⟨i, hi⟩ : {i : ι // i ∉ Set.range e})).comp
          (continuous_snd : Continuous (fun z : ({i : ι // i ∈ Set.range e} → α) ×
            ({i : ι // i ∉ Set.range e} → α) => z.2)))
  have hInt : Integrable (fun z => F (split.symm z))
      ((Measure.pi (fun _ : {i : ι // i ∈ Set.range e} => μ)).prod
        (Measure.pi (fun _ : {i : ι // i ∉ Set.range e} => μ))) :=
    (hF.comp hJoin).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ z : ({i : ι // i ∈ Set.range e} → α) × ({i : ι // i ∉ Set.range e} → α),
        F (split.symm z)
        ∂((Measure.pi (fun _ : {i : ι // i ∈ Set.range e} => μ)).prod
          (Measure.pi (fun _ : {i : ι // i ∉ Set.range e} => μ))) :=
      (hSplit.symm.integral_comp' F).symm
    _ = ∫ u : {i : ι // i ∈ Set.range e} → α,
        ∫ r : {i : ι // i ∉ Set.range e} → α, F (split.symm (u, r))
        ∂Measure.pi (fun _ : {i : ι // i ∉ Set.range e} => μ)
        ∂Measure.pi (fun _ : {i : ι // i ∈ Set.range e} => μ) := integral_prod _ hInt
    _ = ∫ x : κ → α, ∫ r : {i : ι // i ∉ Set.range e} → α, F (split.symm (reindex x, r))
        ∂Measure.pi (fun _ : {i : ι // i ∉ Set.range e} => μ)
        ∂Measure.pi (fun _ : κ => μ) :=
      (hReindex.integral_comp' (fun u => ∫ r : {i : ι // i ∉ Set.range e} → α,
        F (split.symm (u, r)) ∂Measure.pi (fun _ : {i : ι // i ∉ Set.range e} => μ))).symm
    _ = ∫ x : κ → α, ∫ r : {i : ι // i ∉ Set.range e} → α,
        F (finiteProductEmbeddingAssemble e x r)
        ∂Measure.pi (fun _ : {i : ι // i ∉ Set.range e} => μ)
        ∂Measure.pi (fun _ : κ => μ) := by
      apply integral_congr_ae
      filter_upwards with x
      apply integral_congr_ae
      filter_upwards with r
      apply congrArg F
      funext i
      dsimp only [split, reindex, erange]
      rw [MeasurableEquiv.piEquivPiSubtypeProd_symm_apply,
        finiteProductEmbeddingAssemble_apply]
      split_ifs with hi
      · simp only [MeasurableEquiv.coe_piCongrLeft,
          Equiv.piCongrLeft_apply_eq_cast, cast_eq]
      · rfl

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.finiteProductEmbeddingAssemble_selected
#print axioms MGAP4D.MathlibAnalytic.finiteProductEmbeddingAssemble_remote
#print axioms MGAP4D.MathlibAnalytic.finiteProductEmbeddingAssemble_continuous
#print axioms MGAP4D.MathlibAnalytic.finiteProductEmbeddingAssemble_prod
#print axioms MGAP4D.MathlibAnalytic.integral_finiteProductEmbeddingAssemble
