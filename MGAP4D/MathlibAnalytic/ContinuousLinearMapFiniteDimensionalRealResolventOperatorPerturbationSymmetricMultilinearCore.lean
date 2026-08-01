import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationMixedDysonResponse
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The ordered `n`-direction resolvent word, bundled as a continuous
multilinear map in the perturbation directions.  Its value is

`(R * H₀) * ... * (R * Hₙ₋₁) * R`.

No commutativity assumption is used. -/
def continuousLinearMapRealResolventOrderedDysonMultilinear
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : V →L[ℝ] V) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin n => (V →L[ℝ] V)) (V →L[ℝ] V) :=
  ((ContinuousLinearMap.mul ℝ (V →L[ℝ] V)).flip R).compContinuousMultilinearMap
    ((ContinuousMultilinearMap.mkPiAlgebraFin ℝ n (V →L[ℝ] V)).compContinuousLinearMap
      (fun _ => (ContinuousLinearMap.mul ℝ (V →L[ℝ] V)) R))

@[simp]
theorem continuousLinearMapRealResolventOrderedDysonMultilinear_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : V →L[ℝ] V) (H : Fin n → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventOrderedDysonMultilinear n R H =
      (List.ofFn (fun i => R * H i)).prod * R := by
  simp [continuousLinearMapRealResolventOrderedDysonMultilinear]

/-- Reindex an ordered resolvent word by a permutation of its direction
coordinates. -/
def continuousLinearMapRealResolventPermutedDysonMultilinear
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : V →L[ℝ] V) (σ : Equiv.Perm (Fin n)) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin n => (V →L[ℝ] V)) (V →L[ℝ] V) :=
  ContinuousMultilinearMap.domDomCongr σ
    (continuousLinearMapRealResolventOrderedDysonMultilinear n R)

@[simp]
theorem continuousLinearMapRealResolventPermutedDysonMultilinear_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : V →L[ℝ] V) (σ : Equiv.Perm (Fin n))
    (H : Fin n → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventPermutedDysonMultilinear n R σ H =
      continuousLinearMapRealResolventOrderedDysonMultilinear n R
        (fun i => H (σ i)) := by
  simp [continuousLinearMapRealResolventPermutedDysonMultilinear]

/-- The fully symmetrized resolvent derivative word.  This is a genuine
continuous multilinear map, defined as the sum of all noncommutative ordered
words indexed by permutations of the direction tuple. -/
def continuousLinearMapRealResolventSymmetricDysonMultilinear
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : V →L[ℝ] V) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin n => (V →L[ℝ] V)) (V →L[ℝ] V) :=
  ∑ σ : Equiv.Perm (Fin n),
    continuousLinearMapRealResolventPermutedDysonMultilinear n R σ

@[simp]
theorem continuousLinearMapRealResolventSymmetricDysonMultilinear_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : V →L[ℝ] V) (H : Fin n → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventSymmetricDysonMultilinear n R H =
      ∑ σ : Equiv.Perm (Fin n),
        continuousLinearMapRealResolventOrderedDysonMultilinear n R
          (fun i => H (σ i)) := by
  simp [continuousLinearMapRealResolventSymmetricDysonMultilinear]

/-- The symmetric operator-direction derivative candidate of the finite-
dimensional real resolvent, bundled as a continuous multilinear map. -/
def continuousLinearMapRealResolventOperatorSymmetricDerivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A : V →L[ℝ] V) (z : ℝ) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin n => (V →L[ℝ] V)) (V →L[ℝ] V) :=
  continuousLinearMapRealResolventSymmetricDysonMultilinear n
    (continuousLinearMapRealResolvent A z)

@[simp]
theorem continuousLinearMapRealResolventOperatorSymmetricDerivative_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A : V →L[ℝ] V) (z : ℝ)
    (H : Fin n → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventOperatorSymmetricDerivative n A z H =
      ∑ σ : Equiv.Perm (Fin n),
        continuousLinearMapRealResolventOrderedDysonMultilinear n
          (continuousLinearMapRealResolvent A z) (fun i => H (σ i)) := by
  simp [continuousLinearMapRealResolventOperatorSymmetricDerivative]

/-- The operator norm of the bundled symmetric derivative controls its value
by the product of the direction norms. -/
theorem continuousLinearMapRealResolventOperatorSymmetricDerivative_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A : V →L[ℝ] V) (z : ℝ)
    (H : Fin n → (V →L[ℝ] V)) :
    ‖continuousLinearMapRealResolventOperatorSymmetricDerivative n A z H‖ ≤
      ‖continuousLinearMapRealResolventOperatorSymmetricDerivative n A z‖ *
        ∏ i : Fin n, ‖H i‖ :=
  (continuousLinearMapRealResolventOperatorSymmetricDerivative n A z).le_opNorm H

end MathlibAnalytic
end MGAP4D
