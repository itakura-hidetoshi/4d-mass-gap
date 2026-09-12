import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationSymmetricMultilinearDysonCore
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The algebraic mixed Dyson coefficient packaged as a genuine multilinear
map in all perturbation directions.  The recursion inserts each new direction
at every possible coordinate, exactly matching the polarization recursion. -/
def continuousLinearMapRealResolventMixedDysonMultilinearMapFromResolvent :
    (n : ℕ) → {V : Type*} → [NormedAddCommGroup V] → [NormedSpace ℝ V] →
      (V →L[ℝ] V) →
        MultilinearMap ℝ (fun _ : Fin n => (V →L[ℝ] V)) (V →L[ℝ] V)
  | 0, V, _, _, R =>
      MultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => (V →L[ℝ] V)) R
  | n + 1, V, _, _, R =>
      ∑ i : Fin (n + 1),
        LinearMap.uncurryMid i
          { toFun := fun H =>
              { toFun := fun K =>
                  continuousLinearMapRealResolventMixedDysonMultilinearMapFromResolvent
                      n R K * H * R
                map_update_add' := by
                  intros
                  simp [add_mul]
                map_update_smul' := by
                  intros
                  simp }
            map_add' := by
              intro x y
              ext K
              simp [mul_add, add_mul]
            map_smul' := by
              intro c x
              ext K
              simp }

/-- Evaluation of the algebraic multilinear carrier is exactly the mixed
Dyson polynomial in the resolvent variable. -/
@[simp]
theorem continuousLinearMapRealResolventMixedDysonMultilinearMapFromResolvent_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : V →L[ℝ] V) (H : Fin n → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventMixedDysonMultilinearMapFromResolvent n R H =
      continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent n R H := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [continuousLinearMapRealResolventMixedDysonMultilinearMapFromResolvent,
        continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent]
      let F : Fin (n + 1) →
          MultilinearMap ℝ (fun _ : Fin (n + 1) => (V →L[ℝ] V)) (V →L[ℝ] V) :=
        fun i =>
          LinearMap.uncurryMid i
            { toFun := fun h =>
                { toFun := fun K =>
                    continuousLinearMapRealResolventMixedDysonMultilinearMapFromResolvent
                        n R K * h * R
                  map_update_add' := by
                    intros
                    simp [add_mul]
                  map_update_smul' := by
                    intros
                    simp }
              map_add' := by
                intro x y
                ext K
                simp [mul_add, add_mul]
              map_smul' := by
                intro c x
                ext K
                simp }
      change (∑ i, F i) H =
        ∑ i : Fin (n + 1),
          continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent n R
              (fun j => H (i.succAbove j)) * H i * R
      rw [show (∑ i, F i) H = ∑ i, F i H by
        simpa using (MultilinearMap.sum_apply F H (s := Finset.univ))]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [show F i H =
          continuousLinearMapRealResolventMixedDysonMultilinearMapFromResolvent n R
              (i.removeNth H) * H i * R by
        simp [F, LinearMap.uncurryMid_apply]]
      rw [ih]
      rfl

/-- The operator mixed Dyson coefficient as an algebraic multilinear map in
all perturbation directions. -/
def continuousLinearMapRealResolventOperatorMixedDysonMultilinearMap
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A : V →L[ℝ] V) (z : ℝ) :
    MultilinearMap ℝ (fun _ : Fin n => (V →L[ℝ] V)) (V →L[ℝ] V) :=
  continuousLinearMapRealResolventMixedDysonMultilinearMapFromResolvent n
    (continuousLinearMapRealResolvent A z)

@[simp]
theorem continuousLinearMapRealResolventOperatorMixedDysonMultilinearMap_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A : V →L[ℝ] V)
    (H : Fin n → (V →L[ℝ] V)) (z : ℝ) :
    continuousLinearMapRealResolventOperatorMixedDysonMultilinearMap n A z H =
      continuousLinearMapRealResolventOperatorMixedDysonCoefficient n A H z := by
  rw [continuousLinearMapRealResolventOperatorMixedDysonCoefficient_eq_fromResolvent]
  simp [continuousLinearMapRealResolventOperatorMixedDysonMultilinearMap]

/-- The genuine continuous multilinear mixed Dyson carrier.  Its continuity
constant is the sharp factorial resolvent envelope. -/
def continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearMap
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A : V →L[ℝ] V) (z M : ℝ)
    (hM : 0 ≤ M) (hR : ‖continuousLinearMapRealResolvent A z‖ ≤ M) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => (V →L[ℝ] V)) (V →L[ℝ] V) :=
  (continuousLinearMapRealResolventOperatorMixedDysonMultilinearMap n A z).mkContinuous
    (continuousLinearMapRealResolventMixedDysonMultilinearBound n M) (by
      intro H
      simpa [continuousLinearMapRealResolventMixedDysonMultilinearBound] using
        continuousLinearMapRealResolventOperatorMixedDysonCoefficient_norm_le_prod
          n A H z M hM hR)

@[simp]
theorem continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearMap_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A : V →L[ℝ] V)
    (H : Fin n → (V →L[ℝ] V)) (z M : ℝ)
    (hM : 0 ≤ M) (hR : ‖continuousLinearMapRealResolvent A z‖ ≤ M) :
    continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearMap
        n A z M hM hR H =
      continuousLinearMapRealResolventOperatorMixedDysonCoefficient n A H z := by
  simp [continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearMap]

/-- On the full diagonal, the continuous multilinear carrier recovers the
factorial one-direction Dyson coefficient. -/
theorem continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearMap_const
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A H : V →L[ℝ] V) (z M : ℝ)
    (hM : 0 ≤ M) (hR : ‖continuousLinearMapRealResolvent A z‖ ≤ M) :
    continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearMap
        n A z M hM hR (fun _ => H) =
      (n.factorial : ℝ) •
        continuousLinearMapRealResolventOperatorDysonCoefficient n A H z := by
  rw [continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearMap_apply,
    continuousLinearMapRealResolventOperatorMixedDysonCoefficient_const]

end MathlibAnalytic
end MGAP4D
