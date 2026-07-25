import MGAP4D.MathlibAnalytic.StandardRealHilbertDiagonalStarSubalgebraCompleteClosed
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Topology

namespace StandardRealHilbertComplexification

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The canonical embedding of the real Hilbert space into its standard
complexification, bundled as a real-linear isometry. -/
noncomputable def standardOfRealLinearIsometry :
    H →ₗᵢ[ℝ] StandardRealHilbertComplexification H where
  toLinearMap :=
    { toFun := ofReal
      map_add' := by
        intro x y
        apply Prod.ext <;> simp [ofReal]
      map_smul' := by
        intro r x
        change (r • x, 0) = (r • x, r • (0 : H))
        apply Prod.ext <;> simp }
  norm_map' := norm_ofReal

@[simp]
theorem standardOfRealLinearIsometry_apply (x : H) :
    standardOfRealLinearIsometry (H := H) x = ofReal x :=
  rfl

/-- Standard conjugation, bundled as a real-linear isometry. -/
noncomputable def standardConjugationLinearIsometry :
    StandardRealHilbertComplexification H →ₗᵢ[ℝ]
      StandardRealHilbertComplexification H where
  toLinearMap :=
    { toFun := conjugation
      map_add' := by
        intro z w
        apply Prod.ext
        · simp [conjugation]
        · change -(z.2 + w.2) = -z.2 + -w.2
          abel
      map_smul' := by
        intro r z
        change (r • z.1, -(r • z.2)) = (r • z.1, r • (-z.2))
        apply Prod.ext <;> simp }
  norm_map' := norm_conjugation

@[simp]
theorem standardConjugationLinearIsometry_apply
    (z : StandardRealHilbertComplexification H) :
    standardConjugationLinearIsometry (H := H) z = conjugation z :=
  rfl

/-- Standard conjugation is continuous. -/
theorem continuous_standardConjugation :
    Continuous (conjugation : StandardRealHilbertComplexification H →
      StandardRealHilbertComplexification H) :=
  (standardConjugationLinearIsometry (H := H)).continuous

/-- The real-coordinate norm is bounded by the standard complexification norm. -/
theorem norm_standardRealPart_le
    (z : StandardRealHilbertComplexification H) :
    ‖z.1‖ ≤ ‖z‖ := by
  have hsq : ‖z.1‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [norm_eq_standardNorm, standardNorm_sq]
    nlinarith [sq_nonneg ‖z.2‖]
  exact (sq_le_sq₀ (norm_nonneg z.1) (norm_nonneg z)).mp hsq

/-- A vector fixed by standard conjugation has zero imaginary coordinate. -/
theorem imag_eq_zero_of_conjugation_eq
    (z : StandardRealHilbertComplexification H)
    (hz : conjugation z = z) :
    z.2 = 0 := by
  have hcoord := congrArg Prod.snd hz
  change -z.2 = z.2 at hcoord
  have hsum : z.2 + z.2 = 0 := by
    calc
      z.2 + z.2 = z.2 + (-z.2) :=
        congrArg (fun w : H => z.2 + w) hcoord.symm
      _ = 0 := add_neg_cancel _
  have htwo : (2 : ℝ) • z.2 = 0 := by
    simpa [two_smul] using hsum
  have h := congrArg (fun w : H => (2 : ℝ)⁻¹ • w) htwo
  simpa [smul_smul] using h

/-- A vector fixed by standard conjugation is exactly its embedded real part. -/
theorem ofReal_realPart_eq_of_conjugation_eq
    (z : StandardRealHilbertComplexification H)
    (hz : conjugation z = z) :
    ofReal z.1 = z := by
  apply Prod.ext
  · simp [ofReal]
  · simpa [ofReal] using (imag_eq_zero_of_conjugation_eq (H := H) z hz).symm

/-- Restrict a bounded complex-linear operator to the embedded real form and
project to its real coordinate. -/
def standardRealRestrictionLinearMap
    (X : StandardRealHilbertComplexification H →L[ℂ]
      StandardRealHilbertComplexification H) :
    H →ₗ[ℝ] H where
  toFun x := (X (ofReal x)).1
  map_add' := by
    intro x y
    have hOfReal : ofReal (x + y) = ofReal x + ofReal y := by
      apply Prod.ext <;> simp [ofReal]
    change (X (ofReal (x + y))).1 =
      (X (ofReal x)).1 + (X (ofReal y)).1
    rw [hOfReal, map_add]
    rfl
  map_smul' := by
    intro r x
    have hReal : ofReal (r • x) = r • ofReal x := by
      change (r • x, 0) = (r • x, r • (0 : H))
      apply Prod.ext <;> simp
    have hOfReal : ofReal (r • x) = (r : ℂ) • ofReal x :=
      hReal.trans (Complex.coe_smul r (ofReal x)).symm
    calc
      (X (ofReal (r • x))).1 = (X ((r : ℂ) • ofReal x)).1 := by rw [hOfReal]
      _ = (((r : ℂ) • X (ofReal x))).1 :=
        congrArg Prod.fst (X.map_smul (r : ℂ) (ofReal x))
      _ = ((r • X (ofReal x))).1 :=
        congrArg Prod.fst (Complex.coe_smul r (X (ofReal x)))
      _ = r • (X (ofReal x)).1 := rfl

@[simp]
theorem standardRealRestrictionLinearMap_apply
    (X : StandardRealHilbertComplexification H →L[ℂ]
      StandardRealHilbertComplexification H)
    (x : H) :
    standardRealRestrictionLinearMap X x = (X (ofReal x)).1 :=
  rfl

/-- The real restriction is bounded by the operator norm of the complex
operator. -/
theorem standardRealRestrictionLinearMap_norm_bound
    (X : StandardRealHilbertComplexification H →L[ℂ]
      StandardRealHilbertComplexification H)
    (x : H) :
    ‖standardRealRestrictionLinearMap X x‖ ≤ ‖X‖ * ‖x‖ := by
  change ‖(X (ofReal x)).1‖ ≤ ‖X‖ * ‖x‖
  calc
    ‖(X (ofReal x)).1‖ ≤ ‖X (ofReal x)‖ :=
      norm_standardRealPart_le (H := H) _
    _ ≤ ‖X‖ * ‖ofReal x‖ := X.le_opNorm _
    _ = ‖X‖ * ‖x‖ := by rw [norm_ofReal]

/-- The real restriction of a bounded complex operator. -/
noncomputable def standardRealRestriction
    (X : StandardRealHilbertComplexification H →L[ℂ]
      StandardRealHilbertComplexification H) :
    H →L[ℝ] H :=
  (standardRealRestrictionLinearMap X).mkContinuous ‖X‖
    (standardRealRestrictionLinearMap_norm_bound X)

@[simp]
theorem standardRealRestriction_apply
    (X : StandardRealHilbertComplexification H →L[ℂ]
      StandardRealHilbertComplexification H)
    (x : H) :
    standardRealRestriction X x = (X (ofReal x)).1 :=
  rfl

/-- Complex-linear operators are determined by their values on the embedded
real form. -/
theorem complexLinearMap_eq_of_eq_on_ofReal
    {X Y : StandardRealHilbertComplexification H →L[ℂ]
      StandardRealHilbertComplexification H}
    (h : ∀ x : H, X (ofReal x) = Y (ofReal x)) :
    X = Y := by
  ext z
  calc
    X z = X (ofReal z.1 + Complex.I • ofReal z.2) :=
      congrArg X (decompose z)
    _ = X (ofReal z.1) + X (Complex.I • ofReal z.2) :=
      X.map_add _ _
    _ = X (ofReal z.1) + Complex.I • X (ofReal z.2) := by
      rw [X.map_smul]
    _ = Y (ofReal z.1) + Complex.I • Y (ofReal z.2) := by
      rw [h, h]
    _ = Y (ofReal z.1) + Y (Complex.I • ofReal z.2) := by
      rw [Y.map_smul]
    _ = Y (ofReal z.1 + Complex.I • ofReal z.2) :=
      (Y.map_add _ _).symm
    _ = Y z := congrArg Y (decompose z).symm

/-- A conjugation-commuting complex operator agrees on real vectors with the
diagonal complexification of its real restriction. -/
theorem diagonalComplexification_standardRealRestriction_apply_ofReal
    (X : StandardRealHilbertComplexification H →L[ℂ]
      StandardRealHilbertComplexification H)
    (hX : ∀ z : StandardRealHilbertComplexification H,
      conjugation (X z) = X (conjugation z))
    (x : H) :
    diagonalComplexification (standardRealRestriction X) (ofReal x) =
      X (ofReal x) := by
  rw [diagonalComplexification_ofReal, standardRealRestriction_apply]
  apply ofReal_realPart_eq_of_conjugation_eq
  calc
    conjugation (X (ofReal x)) = X (conjugation (ofReal x)) := hX _
    _ = X (ofReal x) := by rw [conjugation_ofReal]

/-- A conjugation-commuting bounded complex operator is exactly the diagonal
complexification of its real restriction. -/
theorem diagonalComplexification_standardRealRestriction_eq
    (X : StandardRealHilbertComplexification H →L[ℂ]
      StandardRealHilbertComplexification H)
    (hX : ∀ z : StandardRealHilbertComplexification H,
      conjugation (X z) = X (conjugation z)) :
    diagonalComplexification (standardRealRestriction X) = X := by
  apply complexLinearMap_eq_of_eq_on_ofReal
  exact diagonalComplexification_standardRealRestriction_apply_ofReal X hX

/-- A complex bounded operator belongs to the diagonal real-form range exactly
when it commutes with standard conjugation. -/
theorem mem_diagonalComplexificationStarSubalgebra_iff_commutes
    (X : StandardRealHilbertComplexification H →L[ℂ]
      StandardRealHilbertComplexification H) :
    X ∈ diagonalComplexificationStarSubalgebra (H := H) ↔
      ∀ z : StandardRealHilbertComplexification H,
        conjugation (X z) = X (conjugation z) := by
  constructor
  · intro hX
    rcases (mem_diagonalComplexificationStarSubalgebra_iff (H := H) X).1 hX with
      ⟨T, hT⟩
    intro z
    rw [← hT]
    exact (diagonalComplexification_conjugation T z).symm
  · intro hX
    exact (mem_diagonalComplexificationStarSubalgebra_iff (H := H) X).2
      ⟨standardRealRestriction X,
        diagonalComplexification_standardRealRestriction_eq X hX⟩

/-- The diagonal real-form range is closed under pointwise strong-operator
limits along any nontrivial filter.  No uniform operator-norm bound is needed
once the limit is already supplied as a bounded complex-linear operator. -/
theorem mem_diagonalComplexificationStarSubalgebra_of_tendsto_apply
    {ι : Type*} {l : Filter ι} [NeBot l]
    (F : ι → diagonalComplexificationStarSubalgebra (H := H))
    (X : StandardRealHilbertComplexification H →L[ℂ]
      StandardRealHilbertComplexification H)
    (hF : ∀ z : StandardRealHilbertComplexification H,
      Tendsto (fun i => (F i : StandardRealHilbertComplexification H →L[ℂ]
        StandardRealHilbertComplexification H) z) l (nhds (X z))) :
    X ∈ diagonalComplexificationStarSubalgebra (H := H) := by
  rw [mem_diagonalComplexificationStarSubalgebra_iff_commutes]
  intro z
  have hconj :
      Tendsto
        (fun i => conjugation
          ((F i : StandardRealHilbertComplexification H →L[ℂ]
            StandardRealHilbertComplexification H) z))
        l (nhds (conjugation (X z))) :=
    (continuous_standardConjugation (H := H)).tendsto (X z) |>.comp (hF z)
  have hfun :
      (fun i => conjugation
        ((F i : StandardRealHilbertComplexification H →L[ℂ]
          StandardRealHilbertComplexification H) z)) =
      (fun i => (F i : StandardRealHilbertComplexification H →L[ℂ]
        StandardRealHilbertComplexification H) (conjugation z)) := by
    funext i
    exact
      (mem_diagonalComplexificationStarSubalgebra_iff_commutes
        (H := H) (F i : StandardRealHilbertComplexification H →L[ℂ]
          StandardRealHilbertComplexification H)).1 (F i).property z
  rw [hfun] at hconj
  exact tendsto_nhds_unique hconj (hF (conjugation z))

/-- A pointwise strong limit of diagonal complexifications is the
complexification of a unique bounded real operator. -/
theorem tendsto_diagonalComplexification_apply_existsUnique_real_limit
    {ι : Type*} {l : Filter ι} [NeBot l]
    (f : ι → H →L[ℝ] H)
    (X : StandardRealHilbertComplexification H →L[ℂ]
      StandardRealHilbertComplexification H)
    (hF : ∀ z : StandardRealHilbertComplexification H,
      Tendsto (fun i => diagonalComplexification (f i) z) l (nhds (X z))) :
    ∃! T : H →L[ℝ] H, diagonalComplexification T = X := by
  let F : ι → diagonalComplexificationStarSubalgebra (H := H) :=
    fun i => diagonalComplexificationStarAlgEquiv (H := H) (f i)
  have hF' : ∀ z : StandardRealHilbertComplexification H,
      Tendsto (fun i => (F i : StandardRealHilbertComplexification H →L[ℂ]
        StandardRealHilbertComplexification H) z) l (nhds (X z)) := by
    intro z
    simpa [F] using hF z
  have hmem :=
    mem_diagonalComplexificationStarSubalgebra_of_tendsto_apply
      (H := H) F X hF'
  rcases (mem_diagonalComplexificationStarSubalgebra_iff (H := H) X).1 hmem with
    ⟨T, hT⟩
  refine ⟨T, hT, ?_⟩
  intro U hU
  apply (diagonalComplexificationLinearIsometry (H := H)).injective
  simpa only [diagonalComplexificationLinearIsometry_apply] using hU.trans hT.symm

end StandardRealHilbertComplexification

end
end MathlibAnalytic
end MGAP4D
