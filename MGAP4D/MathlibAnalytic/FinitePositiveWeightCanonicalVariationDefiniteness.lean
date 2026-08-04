import MGAP4D.MathlibAnalytic.FinitePositiveWeightDobrushinRandomScanContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The canonical coordinate oscillation is the least declared variation
bound at that coordinate. -/
theorem finiteProductCanonicalVariation_le_variationBound
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (e : ι) :
    finiteProductCanonicalVariation f e ≤ P.variation e := by
  classical
  unfold finiteProductCanonicalVariation
  rw [Finset.max'_le_iff]
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨x, _hx, rfl⟩
  exact P.variation_bound e
    (Function.update x.1 e x.2.1)
    (Function.update x.1 e x.2.2)
    (finiteProductUpdates_sameBase_agreeOff x.1 e x.2.1 x.2.2)

/-- A constant observable has zero canonical coordinate variation. -/
theorem finiteProductCanonicalVariation_const_eq_zero
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (c : ℝ)
    (e : ι) :
    finiteProductCanonicalVariation (fun _ : ι → G => c) e = 0 := by
  let P : FiniteProductVariationBound (fun _ : ι → G => c) :=
    { variation := fun _ => 0
      variation_nonneg := fun _ => le_rfl
      variation_bound := by
        intro source A B hAgree
        simp }
  exact le_antisymm
    (finiteProductCanonicalVariation_le_variationBound P e)
    (finiteProductCanonicalVariation_nonneg (fun _ : ι → G => c) e)

/-- Scaling an observable gives the expected upper bound on each canonical
coordinate variation. -/
theorem finiteProductCanonicalVariation_smul_le
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (c : ℝ)
    (f : (ι → G) → ℝ)
    (e : ι) :
    finiteProductCanonicalVariation (c • f) e ≤
      |c| * finiteProductCanonicalVariation f e := by
  let P : FiniteProductVariationBound (c • f) :=
    { variation := fun source =>
        |c| * finiteProductCanonicalVariation f source
      variation_nonneg := by
        intro source
        exact mul_nonneg (abs_nonneg c)
          (finiteProductCanonicalVariation_nonneg f source)
      variation_bound := by
        intro source A B hAgree
        change |c * f A - c * f B| ≤
          |c| * finiteProductCanonicalVariation f source
        calc
          |c * f A - c * f B| = |c| * |f A - f B| := by
            rw [← mul_sub, abs_mul]
          _ ≤ |c| * finiteProductCanonicalVariation f source :=
            mul_le_mul_of_nonneg_left
              (finiteProduct_difference_abs_le_canonicalVariation
                f source A B hAgree)
              (abs_nonneg c) }
  exact finiteProductCanonicalVariation_le_variationBound P e

/-- Canonical coordinate variation is exactly homogeneous under real scalar
multiplication. -/
theorem finiteProductCanonicalVariation_smul
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (c : ℝ)
    (f : (ι → G) → ℝ)
    (e : ι) :
    finiteProductCanonicalVariation (c • f) e =
      |c| * finiteProductCanonicalVariation f e := by
  by_cases hc : c = 0
  · subst c
    rw [zero_smul, abs_zero, zero_mul]
    exact finiteProductCanonicalVariation_const_eq_zero 0 e
  · have hForward := finiteProductCanonicalVariation_smul_le c f e
    have hInv :
        finiteProductCanonicalVariation f e ≤
          |c⁻¹| * finiteProductCanonicalVariation (c • f) e := by
      simpa [smul_smul, hc] using
        (finiteProductCanonicalVariation_smul_le c⁻¹ (c • f) e)
    have hBackward :
        |c| * finiteProductCanonicalVariation f e ≤
          finiteProductCanonicalVariation (c • f) e := by
      calc
        |c| * finiteProductCanonicalVariation f e ≤
            |c| *
              (|c⁻¹| * finiteProductCanonicalVariation (c • f) e) :=
          mul_le_mul_of_nonneg_left hInv (abs_nonneg c)
        _ = finiteProductCanonicalVariation (c • f) e := by
          rw [abs_inv, ← mul_assoc,
            mul_inv_cancel₀ (abs_ne_zero.mpr hc), one_mul]
    exact le_antisymm hForward hBackward

/-- Canonical total variation is exactly homogeneous under real scalar
multiplication. -/
theorem finiteProductCanonicalTotalVariation_smul
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (c : ℝ)
    (f : (ι → G) → ℝ) :
    finiteProductCanonicalTotalVariation (c • f) =
      |c| * finiteProductCanonicalTotalVariation f := by
  unfold finiteProductCanonicalTotalVariation
  calc
    (∑ e : ι, finiteProductCanonicalVariation (c • f) e) =
        ∑ e : ι, |c| * finiteProductCanonicalVariation f e := by
      apply Finset.sum_congr rfl
      intro e _he
      exact finiteProductCanonicalVariation_smul c f e
    _ = |c| * ∑ e : ι, finiteProductCanonicalVariation f e := by
      rw [Finset.mul_sum]

/-- Patch into `A` the values of `B` on a selected finite coordinate set. -/
def finiteProductPatch
    {ι G : Type}
    [DecidableEq ι]
    (A B : ι → G)
    (s : Finset ι) : ι → G :=
  fun e => if e ∈ s then B e else A e

@[simp] theorem finiteProductPatch_empty
    {ι G : Type}
    [DecidableEq ι]
    (A B : ι → G) :
    finiteProductPatch A B ∅ = A := by
  funext e
  simp [finiteProductPatch]

@[simp] theorem finiteProductPatch_univ
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    (A B : ι → G) :
    finiteProductPatch A B Finset.univ = B := by
  funext e
  simp [finiteProductPatch]

/-- Adding one coordinate to a patch changes no other coordinate. -/
theorem finiteProductPatch_agreeOff_insert
    {ι G : Type}
    [DecidableEq ι]
    (A B : ι → G)
    (s : Finset ι)
    (e : ι) :
    FiniteProductAgreeOff
      (finiteProductPatch A B s)
      (finiteProductPatch A B (insert e s)) e := by
  intro e' hne
  by_cases hs : e' ∈ s
  · simp [finiteProductPatch, hs]
  · have hInsert : e' ∉ insert e s := by
      simp [hne, hs]
    simp [finiteProductPatch, hs, hInsert]

/-- Zero canonical variation at one coordinate forces invariance under every
change supported on that coordinate. -/
theorem finiteProduct_eq_of_agreeOff_of_canonicalVariation_eq_zero
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (f : (ι → G) → ℝ)
    (e : ι)
    (A B : ι → G)
    (hAgree : FiniteProductAgreeOff A B e)
    (hZero : finiteProductCanonicalVariation f e = 0) :
    f A = f B := by
  have hBound : |f A - f B| ≤ 0 := by
    simpa [hZero] using
      (finiteProduct_difference_abs_le_canonicalVariation
        f e A B hAgree)
  have hAbs : |f A - f B| = 0 :=
    le_antisymm hBound (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hAbs)

/-- If all canonical coordinate variations vanish, the observable is constant
on the full finite product configuration space. -/
theorem finiteProduct_eq_of_all_canonicalVariations_eq_zero
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (f : (ι → G) → ℝ)
    (hZero : ∀ e : ι, finiteProductCanonicalVariation f e = 0)
    (A B : ι → G) :
    f A = f B := by
  have hPatch :
      ∀ s : Finset ι, f A = f (finiteProductPatch A B s) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert e s he ih =>
        calc
          f A = f (finiteProductPatch A B s) := ih
          _ = f (finiteProductPatch A B (insert e s)) :=
            finiteProduct_eq_of_agreeOff_of_canonicalVariation_eq_zero
              f e
              (finiteProductPatch A B s)
              (finiteProductPatch A B (insert e s))
              (finiteProductPatch_agreeOff_insert A B s e)
              (hZero e)
  simpa using hPatch Finset.univ

/-- Vanishing total canonical variation forces all coordinate variations to
vanish. -/
theorem finiteProductCanonicalVariation_eq_zero_of_total_eq_zero
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (f : (ι → G) → ℝ)
    (hTotal : finiteProductCanonicalTotalVariation f = 0)
    (e : ι) :
    finiteProductCanonicalVariation f e = 0 := by
  have hLe :
      finiteProductCanonicalVariation f e ≤
        finiteProductCanonicalTotalVariation f := by
    unfold finiteProductCanonicalTotalVariation
    exact Finset.single_le_sum
      (fun e' _he' => finiteProductCanonicalVariation_nonneg f e')
      (Finset.mem_univ e)
  rw [hTotal] at hLe
  exact le_antisymm hLe (finiteProductCanonicalVariation_nonneg f e)

/-- Unnormalized total mass of a strictly positive finite product weight. -/
def finitePositiveWeightTotal
    {ι G : Type}
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ) : ℝ :=
  ∑ A : ι → G, weight A

/-- A pointwise-positive finite product weight has strictly positive total
mass. -/
theorem finitePositiveWeightTotal_pos
    {ι G : Type}
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A) :
    0 < finitePositiveWeightTotal weight := by
  let A0 : ι → G := Classical.choice inferInstance
  unfold finitePositiveWeightTotal
  exact Finset.sum_pos
    (fun A _hA => hweight A)
    ⟨A0, Finset.mem_univ A0⟩

/-- Unnormalized weighted first moment of an observable. -/
def finitePositiveWeightSum
    {ι G : Type}
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ) : ℝ :=
  ∑ A : ι → G, weight A * f A

/-- Weighted first moment of a constant observable. -/
theorem finitePositiveWeightSum_const
    {ι G : Type}
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (c : ℝ) :
    finitePositiveWeightSum weight (fun _ : ι → G => c) =
      finitePositiveWeightTotal weight * c := by
  unfold finitePositiveWeightSum finitePositiveWeightTotal
  rw [Finset.sum_mul]

/-- On the positive-weight centered sector, all coordinate variations have
trivial joint kernel. -/
theorem finitePositiveWeight_centered_eq_zero_of_all_canonicalVariations_eq_zero
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (hCenter : finitePositiveWeightSum weight f = 0)
    (hZero : ∀ e : ι, finiteProductCanonicalVariation f e = 0) :
    f = 0 := by
  let A0 : ι → G := Classical.choice inferInstance
  have hConst : f = fun _ : ι → G => f A0 := by
    funext A
    exact finiteProduct_eq_of_all_canonicalVariations_eq_zero
      f hZero A A0
  have hValue : f A0 = 0 := by
    rw [hConst, finitePositiveWeightSum_const] at hCenter
    exact (mul_eq_zero.mp hCenter).resolve_left
      (ne_of_gt (finitePositiveWeightTotal_pos weight hweight))
  rw [hConst, hValue]
  rfl

/-- A nonzero centered observable has nonzero total canonical variation. -/
theorem finitePositiveWeight_centered_canonicalTotalVariation_ne_zero
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (hCenter : finitePositiveWeightSum weight f = 0)
    (hNonzero : f ≠ 0) :
    finiteProductCanonicalTotalVariation f ≠ 0 := by
  intro hTotal
  apply hNonzero
  exact finitePositiveWeight_centered_eq_zero_of_all_canonicalVariations_eq_zero
    weight hweight f hCenter
    (finiteProductCanonicalVariation_eq_zero_of_total_eq_zero f hTotal)

end

end MathlibAnalytic
end MGAP4D
