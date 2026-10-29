import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Logic.Equiv.Set

/-!
# Finite product integration along an embedded set of coordinates

Split a finite product measure into the coordinates selected by an embedding
and their complement. A product of scalar coordinate weights times an
observable of the selected coordinates integrates to the selected integral
times the product of the remaining one-coordinate masses.

The proof uses the actual product measure, its measurable coordinate splitting,
and the finite-product integral formula. No independence hypothesis or
substitute measure is introduced. Mathlib's Bochner product identities also
cover the nonintegrable case through the usual zero-integral convention, so
the algebraic identity needs no additional regularity hypotheses.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option autoImplicit false

universe u v t

/-- Integrate a product of coordinate weights against an observable depending
only on coordinates selected by an embedding. Every remote coordinate
contributes its actual one-coordinate integral. -/
theorem integral_finiteProduct_mul_embedding
    {ι : Type u} {κ : Type v} {α : Type t}
    [Fintype ι] [Fintype κ] [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ]
    (e : κ ↪ ι) (w : ι → α → ℝ) (f : (κ → α) → ℝ) :
    (∫ x : ι → α,
      (∏ i : ι, w i (x i)) * f (fun j => x (e j))
        ∂Measure.pi (fun _ : ι => μ)) =
      (∫ x : κ → α, (∏ j : κ, w (e j) (x j)) * f x
        ∂Measure.pi (fun _ : κ => μ)) *
      ∏ i : {i : ι // i ∉ Set.range e}, ∫ x : α, w i.1 x ∂μ := by
  classical
  let p : ι → Prop := fun i => i ∈ Set.range e
  let erange : κ ≃ Subtype p := Equiv.ofInjective e e.injective
  let split : (ι → α) ≃ᵐ
      ((Subtype p → α) × ({i : ι // ¬p i} → α)) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => α) p
  let reindex : (κ → α) ≃ᵐ (Subtype p → α) :=
    MeasurableEquiv.piCongrLeft (fun _ : Subtype p => α) erange
  let F : (κ → α) → ℝ := fun x => (∏ j : κ, w (e j) (x j)) * f x
  let H : (Subtype p → α) → ℝ := fun x => F (reindex.symm x)
  let R : ({i : ι // ¬p i} → α) → ℝ := fun x => ∏ i, w i.1 (x i)
  have hSplit : MeasurePreserving split
      (Measure.pi (fun _ : ι => μ))
      ((Measure.pi (fun _ : Subtype p => μ)).prod
        (Measure.pi (fun _ : {i : ι // ¬p i} => μ))) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) p
  have hReindex : MeasurePreserving reindex
      (Measure.pi (fun _ : κ => μ))
      (Measure.pi (fun _ : Subtype p => μ)) :=
    measurePreserving_piCongrLeft (fun _ : Subtype p => μ) erange
  have hFactor (x : ι → α) :
      (∏ i : ι, w i (x i)) * f (fun j => x (e j)) =
        H (split x).1 * R (split x).2 := by
    have hprod :
        (∏ i : ι, w i (x i)) =
          (∏ j : κ, w (e j) (x (e j))) *
            ∏ i : {i : ι // ¬p i}, w i.1 (x i.1) := by
      calc
        _ = (∏ i : Subtype p, w i.1 (x i.1)) *
            ∏ i : {i : ι // ¬p i}, w i.1 (x i.1) :=
          (Fintype.prod_subtype_mul_prod_subtype p (fun i => w i (x i))).symm
        _ = _ := congrArg
          (fun a : ℝ => a * ∏ i : {i : ι // ¬p i}, w i.1 (x i.1))
          (erange.prod_comp (fun i : Subtype p => w i.1 (x i.1))).symm
    change (∏ i : ι, w i (x i)) * f (fun j => x (e j)) =
      ((∏ j : κ, w (e j) (x (e j))) * f (fun j => x (e j))) *
        ∏ i : {i : ι // ¬p i}, w i.1 (x i.1)
    rw [hprod]
    exact mul_right_comm _ _ _
  have hSelected :
      (∫ x : Subtype p → α, H x ∂Measure.pi (fun _ : Subtype p => μ)) =
        ∫ x : κ → α, F x ∂Measure.pi (fun _ : κ => μ) :=
    hReindex.symm.integral_comp' F
  have hRemote :
      (∫ x : {i : ι // ¬p i} → α, R x
        ∂Measure.pi (fun _ : {i : ι // ¬p i} => μ)) =
        ∏ i : {i : ι // ¬p i}, ∫ x : α, w i.1 x ∂μ :=
    integral_fintype_prod_eq_prod (fun i : {i : ι // ¬p i} => w i.1)
  calc
    _ = ∫ x : ι → α, H (split x).1 * R (split x).2
        ∂Measure.pi (fun _ : ι => μ) :=
      integral_congr_ae (Filter.Eventually.of_forall hFactor)
    _ = ∫ z : (Subtype p → α) × ({i : ι // ¬p i} → α), H z.1 * R z.2
        ∂((Measure.pi (fun _ : Subtype p => μ)).prod
          (Measure.pi (fun _ : {i : ι // ¬p i} => μ))) :=
      hSplit.integral_comp' (fun z => H z.1 * R z.2)
    _ = (∫ x : Subtype p → α, H x ∂Measure.pi (fun _ : Subtype p => μ)) *
        ∫ x : {i : ι // ¬p i} → α, R x
          ∂Measure.pi (fun _ : {i : ι // ¬p i} => μ) :=
      integral_prod_mul H R
    _ = _ := by rw [hSelected, hRemote]

/-- When every coordinate weight has mass one, integrating the remote
coordinates leaves exactly the selected weighted integral. -/
theorem integral_finiteProduct_mul_embedding_of_mass_one
    {ι : Type u} {κ : Type v} {α : Type t}
    [Fintype ι] [Fintype κ] [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ]
    (e : κ ↪ ι) (w : ι → α → ℝ) (f : (κ → α) → ℝ)
    (hw : ∀ i, (∫ x : α, w i x ∂μ) = 1) :
    (∫ x : ι → α,
      (∏ i : ι, w i (x i)) * f (fun j => x (e j))
        ∂Measure.pi (fun _ : ι => μ)) =
      ∫ x : κ → α, (∏ j : κ, w (e j) (x j)) * f x
        ∂Measure.pi (fun _ : κ => μ) := by
  rw [integral_finiteProduct_mul_embedding μ e w f]
  simp [hw]

end

end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.integral_finiteProduct_mul_embedding
#print axioms MGAP4D.MathlibAnalytic.integral_finiteProduct_mul_embedding_of_mass_one
