import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Kernel of a real linear mass functional, viewed as the centered sector of
a finite-dimensional Hilbert space. -/
def finiteLinearFunctionalCenteredSubspace
    (mass : E →ₗ[ℝ] ℝ) : Submodule ℝ E :=
  LinearMap.ker mass

/-- Restriction of a mass-preserving continuous linear operator to its centered
sector. -/
noncomputable def finiteCenteredRestriction
    (T : E →L[ℝ] E)
    (mass : E →ₗ[ℝ] ℝ)
    (hmass : ∀ x : E, mass (T x) = mass x) :
    finiteLinearFunctionalCenteredSubspace mass →L[ℝ]
      finiteLinearFunctionalCenteredSubspace mass :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x =>
        ⟨T x.1, by
          change mass (T x.1) = 0
          rw [hmass]
          exact x.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro c x
        apply Subtype.ext
        simp }

@[simp] theorem finiteCenteredRestriction_apply_coe
    (T : E →L[ℝ] E)
    (mass : E →ₗ[ℝ] ℝ)
    (hmass : ∀ x : E, mass (T x) = mass x)
    (x : finiteLinearFunctionalCenteredSubspace mass) :
    (finiteCenteredRestriction T mass hmass x).1 = T x.1 :=
  rfl

/-- Symmetry descends to a mass-preserving centered restriction. -/
theorem finiteCenteredRestriction_isSymmetric
    (T : E →L[ℝ] E)
    (mass : E →ₗ[ℝ] ℝ)
    (hmass : ∀ x : E, mass (T x) = mass x)
    (hsymm : T.toLinearMap.IsSymmetric) :
    (finiteCenteredRestriction T mass hmass).toLinearMap.IsSymmetric := by
  intro x y
  exact hsymm x.1 y.1

/-- A nonnegative centered Rayleigh upper bound is an operator-norm upper
bound on the centered restriction. -/
theorem finiteCenteredRestriction_norm_le
    (T : E →L[ℝ] E)
    (mass : E →ₗ[ℝ] ℝ)
    (hmass : ∀ x : E, mass (T x) = mass x)
    {q : ℝ}
    (hq0 : 0 ≤ q)
    (hsymm : T.toLinearMap.IsSymmetric)
    (hquadratic :
      ∀ x : finiteLinearFunctionalCenteredSubspace mass,
        0 ≤ inner ℝ (T x.1) x.1)
    (hrayleigh :
      ∀ x : finiteLinearFunctionalCenteredSubspace mass,
        inner ℝ (T x.1) x.1 ≤ q * ‖x‖ ^ 2) :
    ‖finiteCenteredRestriction T mass hmass‖ ≤ q := by
  let R := finiteCenteredRestriction T mass hmass
  have hsymmR : R.toLinearMap.IsSymmetric :=
    finiteCenteredRestriction_isSymmetric T mass hmass hsymm
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient R hsymmR]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have hden : 0 < ‖x‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hx)
    have hnonneg : 0 ≤ R.rayleighQuotient x := by
      change 0 ≤ inner ℝ (R x) x / ‖x‖ ^ 2
      apply div_nonneg
      · change 0 ≤ inner ℝ (T x.1) x.1
        exact hquadratic x
      · exact hden.le
    have hle : R.rayleighQuotient x ≤ q := by
      change inner ℝ (R x) x / ‖x‖ ^ 2 ≤ q
      rw [div_le_iff₀ hden]
      change inner ℝ (T x.1) x.1 ≤ q * ‖x‖ ^ 2
      exact hrayleigh x
    simpa [abs_of_nonneg hnonneg] using hle

/-- Natural powers of a symmetric positive centered transfer decay at the
corresponding geometric rate. -/
theorem finiteCenteredRestriction_pow_norm_apply_le
    (T : E →L[ℝ] E)
    (mass : E →ₗ[ℝ] ℝ)
    (hmass : ∀ x : E, mass (T x) = mass x)
    {q : ℝ}
    (hq0 : 0 ≤ q)
    (hsymm : T.toLinearMap.IsSymmetric)
    (hquadratic :
      ∀ x : finiteLinearFunctionalCenteredSubspace mass,
        0 ≤ inner ℝ (T x.1) x.1)
    (hrayleigh :
      ∀ x : finiteLinearFunctionalCenteredSubspace mass,
        inner ℝ (T x.1) x.1 ≤ q * ‖x‖ ^ 2)
    (n : ℕ)
    (x : finiteLinearFunctionalCenteredSubspace mass) :
    ‖(finiteCenteredRestriction T mass hmass) ^ n x‖ ≤
      q ^ n * ‖x‖ := by
  let R := finiteCenteredRestriction T mass hmass
  have hnorm : ‖R‖ ≤ q :=
    finiteCenteredRestriction_norm_le
      T mass hmass hq0 hsymm hquadratic hrayleigh
  induction n with
  | zero =>
      simp
  | succ n ih =>
      change ‖R ^ (n + 1) x‖ ≤ q ^ (n + 1) * ‖x‖
      rw [pow_succ']
      calc
        ‖R (R ^ n x)‖ ≤ ‖R‖ * ‖R ^ n x‖ :=
          R.le_opNorm (R ^ n x)
        _ ≤ q * (q ^ n * ‖x‖) :=
          mul_le_mul hnorm ih (norm_nonneg _) hq0
        _ = q ^ (n + 1) * ‖x‖ := by
          rw [pow_succ']
          ring

end

end MathlibAnalytic
end MGAP4D
