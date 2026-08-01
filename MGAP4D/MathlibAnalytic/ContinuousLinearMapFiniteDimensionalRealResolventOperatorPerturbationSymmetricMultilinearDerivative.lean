import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationSymmetricMultilinearCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Right composition by a fixed permutation is an equivalence of the finite
permutation group. -/
def continuousLinearMapRealResolventPermutationRightComposition
    (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun σ := σ.trans τ
  invFun σ := σ.trans τ.symm
  left_inv σ := by
    ext i
    simp
  right_inv σ := by
    ext i
    simp

/-- The fully symmetrized resolvent word is invariant under every permutation
of its direction tuple. -/
theorem continuousLinearMapRealResolventSymmetricDysonMultilinear_apply_perm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : V →L[ℝ] V) (τ : Equiv.Perm (Fin n))
    (H : Fin n → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventSymmetricDysonMultilinear n R
        (fun i => H (τ i)) =
      continuousLinearMapRealResolventSymmetricDysonMultilinear n R H := by
  rw [continuousLinearMapRealResolventSymmetricDysonMultilinear_apply,
    continuousLinearMapRealResolventSymmetricDysonMultilinear_apply]
  let e := continuousLinearMapRealResolventPermutationRightComposition n τ
  exact Fintype.sum_equiv e
    (fun σ : Equiv.Perm (Fin n) =>
      continuousLinearMapRealResolventOrderedDysonMultilinear n R
        (fun i => H (τ (σ i))))
    (fun σ : Equiv.Perm (Fin n) =>
      continuousLinearMapRealResolventOrderedDysonMultilinear n R
        (fun i => H (σ i)))
    (fun σ => by
      congr 1)

/-- The bundled symmetric derivative is fixed by reindexing its domain with
an arbitrary permutation. -/
theorem continuousLinearMapRealResolventSymmetricDysonMultilinear_domDomCongr
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : V →L[ℝ] V) (τ : Equiv.Perm (Fin n)) :
    ContinuousMultilinearMap.domDomCongr τ
        (continuousLinearMapRealResolventSymmetricDysonMultilinear n R) =
      continuousLinearMapRealResolventSymmetricDysonMultilinear n R := by
  apply ContinuousMultilinearMap.ext
  intro H
  exact
    continuousLinearMapRealResolventSymmetricDysonMultilinear_apply_perm
      n R τ H

/-- On a constant direction tuple, the ordered multilinear word is the
ordinary one-direction Dyson coefficient. -/
theorem continuousLinearMapRealResolventOrderedDysonMultilinear_const
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A H : V →L[ℝ] V) (z : ℝ) :
    continuousLinearMapRealResolventOrderedDysonMultilinear n
        (continuousLinearMapRealResolvent A z) (fun _ => H) =
      continuousLinearMapRealResolventOperatorDysonCoefficient n A H z := by
  simp [continuousLinearMapRealResolventOperatorDysonCoefficient]

/-- The full diagonal of the symmetric multilinear derivative is `n!` times
the ordinary one-direction Dyson coefficient. -/
theorem continuousLinearMapRealResolventOperatorSymmetricDerivative_const
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A H : V →L[ℝ] V) (z : ℝ) :
    continuousLinearMapRealResolventOperatorSymmetricDerivative n A z
        (fun _ => H) =
      (n.factorial : ℝ) •
        continuousLinearMapRealResolventOperatorDysonCoefficient n A H z := by
  rw [continuousLinearMapRealResolventOperatorSymmetricDerivative_apply]
  calc
    (∑ σ : Equiv.Perm (Fin n),
        continuousLinearMapRealResolventOrderedDysonMultilinear n
          (continuousLinearMapRealResolvent A z)
          (fun i => (fun _ : Fin n => H) (σ i))) =
        ∑ _σ : Equiv.Perm (Fin n),
          continuousLinearMapRealResolventOperatorDysonCoefficient n A H z := by
      apply Finset.sum_congr rfl
      intro σ _hσ
      simpa using
        continuousLinearMapRealResolventOrderedDysonMultilinear_const n A H z
    _ = (n.factorial : ℝ) •
          continuousLinearMapRealResolventOperatorDysonCoefficient n A H z := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]

/-- The symmetric continuous multilinear map recovers the true one-variable
iterated derivative on every full diagonal. -/
theorem continuousLinearMapRealResolventOperatorLine_iteratedDeriv_eq_symmetricDiagonal
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M)
    (n : ℕ) {t : ℝ} (ht : t ∈ U) :
    iteratedDeriv n (continuousLinearMapRealResolventOperatorLine A H z) t =
      continuousLinearMapRealResolventOperatorSymmetricDerivative n
        (A + t • H) z (fun _ => H) := by
  rw [continuousLinearMapRealResolventOperatorLine_iteratedDeriv
    A H z U M hU hM hunit hnorm n ht,
    continuousLinearMapRealResolventOperatorSymmetricDerivative_const]

end MathlibAnalytic
end MGAP4D
