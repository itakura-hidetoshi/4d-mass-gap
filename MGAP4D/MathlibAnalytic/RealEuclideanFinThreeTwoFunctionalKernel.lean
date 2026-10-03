import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# A unit vector in R^3 annihilating two real linear functionals

The three-mode Yang--Mills replacement route needs only a finite-dimensional
linear-algebra fact: two real linear scalar constraints cannot exhaust a
three-dimensional coefficient space.

This file records that fact directly on EuclideanSpace R (Fin 3), using pinned
mathlib rank--nullity.  No Yang--Mills input appears here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProductSpace

noncomputable section

/-- Given two real linear functionals on three-dimensional Euclidean space,
there is a unit vector annihilated by both.

The proof packages the two functionals into a map to R x R.  Since the target
has finrank two and the source finrank three, rank--nullity forces a nonzero
kernel vector; normalization preserves kernel membership. -/
theorem realEuclideanFinThree_exists_unit_annihilating_two
    (phi psi : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) :
    ∃ c : EuclideanSpace ℝ (Fin 3),
      ‖c‖ = 1 ∧ phi c = 0 ∧ psi c = 0 := by
  let T : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] (ℝ × ℝ) :=
    LinearMap.prod phi psi
  have hdim :
      Module.finrank ℝ (ℝ × ℝ) <
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    simp
  have hker : LinearMap.ker T ≠ ⊥ :=
    T.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨c, hcKer, hcNe⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hker
  let u : EuclideanSpace ℝ (Fin 3) := ‖c‖⁻¹ • c
  have huNorm : ‖u‖ = 1 := by
    simpa [u] using (norm_smul_inv_norm (𝕜 := ℝ) hcNe)
  have huKer : u ∈ LinearMap.ker T := by
    exact Submodule.smul_mem (LinearMap.ker T) ‖c‖⁻¹ hcKer
  have hTu : T u = 0 :=
    (LinearMap.mem_ker.mp huKer)
  have hphi : phi u = 0 := by
    have hfst := congrArg Prod.fst hTu
    simpa [T] using hfst
  have hpsi : psi u = 0 := by
    have hsnd := congrArg Prod.snd hTu
    simpa [T] using hsnd
  exact ⟨u, huNorm, hphi, hpsi⟩

end

end MathlibAnalytic
end MGAP4D
