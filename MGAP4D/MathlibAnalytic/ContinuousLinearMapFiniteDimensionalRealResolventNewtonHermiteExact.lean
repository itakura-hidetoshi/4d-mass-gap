import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventNewtonHermiteRemainder
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The true-resolvent Newton-Hermite interpolant exposes its final
coefficient recursively. -/
theorem continuousLinearMapRealResolventNewtonHermiteInterpolant_succ
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n : ℕ) (A : V →L[ℝ] V) (nodes : Fin (n + 2) → ℝ) (z : ℝ) :
    continuousLinearMapRealResolventNewtonHermiteInterpolant
        (n + 1) A nodes z =
      continuousLinearMapRealResolventNewtonHermiteInterpolant
          n A (Fin.init nodes) z +
        continuousLinearMapRealResolventNewtonNodeProduct
            (n + 1) (Fin.init nodes) z •
          continuousLinearMapRealResolventHermiteCoefficient (n + 1) A nodes := by
  rfl

/-- Exact defect form of Newton-Hermite interpolation for a finite-dimensional
real resolvent.  Spectral nodes may repeat; only invertibility at the nodes and
the evaluation point is required. -/
theorem continuousLinearMapRealResolvent_sub_newtonHermiteInterpolant_eq_remainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] :
    ∀ degree : ℕ, ∀ A : V →L[ℝ] V,
      ∀ nodes : Fin (degree + 1) → ℝ, ∀ z : ℝ,
      (∀ i, IsUnit (continuousLinearMapRealShift A (nodes i))) →
      IsUnit (continuousLinearMapRealShift A z) →
      continuousLinearMapRealResolvent A z -
          continuousLinearMapRealResolventNewtonHermiteInterpolant
            degree A nodes z =
        continuousLinearMapRealResolventNewtonHermiteRemainder
          degree A nodes z
  | 0, A, nodes, z, hnodes, hz => by
      have hres := continuousLinearMapRealResolvent_sub_eq_smul_mul
        A (hnodes 0) hz
      calc
        continuousLinearMapRealResolvent A z -
            continuousLinearMapRealResolventNewtonHermiteInterpolant
              0 A nodes z =
            -(continuousLinearMapRealResolvent A (nodes 0) -
              continuousLinearMapRealResolvent A z) := by
          simp [continuousLinearMapRealResolventNewtonHermiteInterpolant,
            continuousLinearMapRealResolventNewtonHermiteInterpolantObservable]
        _ = -((z - nodes 0) •
              (continuousLinearMapRealResolvent A (nodes 0) *
                continuousLinearMapRealResolvent A z)) := by
          rw [hres]
        _ = continuousLinearMapRealResolventNewtonHermiteRemainder
              0 A nodes z := by
          unfold continuousLinearMapRealResolventNewtonHermiteRemainder
          rw [continuousLinearMapRealResolventHermiteCoefficient_finAppend]
          simp [continuousLinearMapRealResolventNewtonNodeProduct,
            continuousLinearMapOrderedProduct]
  | n + 1, A, nodes, z, hnodes, hz => by
      have hprefix :
          ∀ i, IsUnit
            (continuousLinearMapRealShift A ((Fin.init nodes) i)) := by
        intro i
        exact hnodes i.castSucc
      have hih :=
        continuousLinearMapRealResolvent_sub_newtonHermiteInterpolant_eq_remainder
          n A (Fin.init nodes) z hprefix hz
      have hlast : IsUnit
          (continuousLinearMapRealShift A (nodes (Fin.last (n + 1)))) :=
        hnodes (Fin.last (n + 1))
      have hcoef :=
        continuousLinearMapRealResolventHermiteCoefficient_finAppend_sub
          (n + 1) A (Fin.init nodes) z (nodes (Fin.last (n + 1))) hz hlast
      rw [continuousLinearMapFinAppend_init_last] at hcoef
      rw [continuousLinearMapRealResolventNewtonHermiteInterpolant_succ]
      calc
        continuousLinearMapRealResolvent A z -
            (continuousLinearMapRealResolventNewtonHermiteInterpolant
                n A (Fin.init nodes) z +
              continuousLinearMapRealResolventNewtonNodeProduct
                  (n + 1) (Fin.init nodes) z •
                continuousLinearMapRealResolventHermiteCoefficient
                  (n + 1) A nodes) =
            (continuousLinearMapRealResolvent A z -
              continuousLinearMapRealResolventNewtonHermiteInterpolant
                n A (Fin.init nodes) z) -
              continuousLinearMapRealResolventNewtonNodeProduct
                  (n + 1) (Fin.init nodes) z •
                continuousLinearMapRealResolventHermiteCoefficient
                  (n + 1) A nodes := by
          abel
        _ = continuousLinearMapRealResolventNewtonHermiteRemainder
              n A (Fin.init nodes) z -
              continuousLinearMapRealResolventNewtonNodeProduct
                  (n + 1) (Fin.init nodes) z •
                continuousLinearMapRealResolventHermiteCoefficient
                  (n + 1) A nodes := by
          rw [hih]
        _ = continuousLinearMapRealResolventNewtonNodeProduct
                (n + 1) (Fin.init nodes) z •
              (continuousLinearMapRealResolventHermiteCoefficient
                  (n + 1) A
                  (continuousLinearMapFinAppend (Fin.init nodes) z) -
                continuousLinearMapRealResolventHermiteCoefficient
                  (n + 1) A nodes) := by
          unfold continuousLinearMapRealResolventNewtonHermiteRemainder
          rw [← smul_sub]
        _ = continuousLinearMapRealResolventNewtonNodeProduct
                (n + 1) (Fin.init nodes) z •
              ((z - nodes (Fin.last (n + 1))) •
                continuousLinearMapRealResolventHermiteCoefficient
                  (n + 2) A (continuousLinearMapFinAppend nodes z)) := by
          rw [hcoef]
        _ = continuousLinearMapRealResolventNewtonHermiteRemainder
              (n + 1) A nodes z := by
          unfold continuousLinearMapRealResolventNewtonHermiteRemainder
          rw [smul_smul]
          rfl

/-- Exact Newton-Hermite interpolation formula with its closed resolvent
remainder. -/
theorem continuousLinearMapRealResolvent_eq_newtonHermiteInterpolant_add_remainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (A : V →L[ℝ] V)
    (nodes : Fin (degree + 1) → ℝ) (z : ℝ)
    (hnodes : ∀ i, IsUnit (continuousLinearMapRealShift A (nodes i)))
    (hz : IsUnit (continuousLinearMapRealShift A z)) :
    continuousLinearMapRealResolvent A z =
      continuousLinearMapRealResolventNewtonHermiteInterpolant
          degree A nodes z +
        continuousLinearMapRealResolventNewtonHermiteRemainder
          degree A nodes z := by
  have h :=
    continuousLinearMapRealResolvent_sub_newtonHermiteInterpolant_eq_remainder
      degree A nodes z hnodes hz
  calc
    continuousLinearMapRealResolvent A z =
        (continuousLinearMapRealResolvent A z -
          continuousLinearMapRealResolventNewtonHermiteInterpolant
            degree A nodes z) +
          continuousLinearMapRealResolventNewtonHermiteInterpolant
            degree A nodes z := by
      abel
    _ = continuousLinearMapRealResolventNewtonHermiteRemainder
          degree A nodes z +
        continuousLinearMapRealResolventNewtonHermiteInterpolant
          degree A nodes z := by
      rw [h]
    _ = continuousLinearMapRealResolventNewtonHermiteInterpolant
          degree A nodes z +
        continuousLinearMapRealResolventNewtonHermiteRemainder
          degree A nodes z := add_comm _ _

/-- The Newton-Hermite interpolant agrees exactly with the resolvent at every
listed interpolation node, including repeated nodes. -/
theorem continuousLinearMapRealResolventNewtonHermiteInterpolant_eq_at_node
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (A : V →L[ℝ] V)
    (nodes : Fin (degree + 1) → ℝ)
    (hnodes : ∀ i, IsUnit (continuousLinearMapRealShift A (nodes i)))
    (i : Fin (degree + 1)) :
    continuousLinearMapRealResolventNewtonHermiteInterpolant
        degree A nodes (nodes i) =
      continuousLinearMapRealResolvent A (nodes i) := by
  have h := continuousLinearMapRealResolvent_eq_newtonHermiteInterpolant_add_remainder
    degree A nodes (nodes i) hnodes (hnodes i)
  rw [continuousLinearMapRealResolventNewtonHermiteRemainder_eq_zero_at_node,
    add_zero] at h
  exact h.symm

/-- Exact interpolation error norm bound inherited from the closed remainder
formula. -/
theorem continuousLinearMapRealResolvent_sub_newtonHermiteInterpolant_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (A : V →L[ℝ] V)
    (nodes : Fin (degree + 1) → ℝ) (z M D : ℝ)
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hnodesUnit : ∀ i, IsUnit (continuousLinearMapRealShift A (nodes i)))
    (hzUnit : IsUnit (continuousLinearMapRealShift A z))
    (hnodesDist : ∀ i, |z - nodes i| ≤ D)
    (hnodesNorm : ∀ i, ‖continuousLinearMapRealResolvent A (nodes i)‖ ≤ M)
    (hzNorm : ‖continuousLinearMapRealResolvent A z‖ ≤ M) :
    ‖continuousLinearMapRealResolvent A z -
        continuousLinearMapRealResolventNewtonHermiteInterpolant
          degree A nodes z‖ ≤
      D ^ (degree + 1) * M ^ (degree + 2) := by
  rw [continuousLinearMapRealResolvent_sub_newtonHermiteInterpolant_eq_remainder
    degree A nodes z hnodesUnit hzUnit]
  exact continuousLinearMapRealResolventNewtonHermiteRemainder_norm_le
    degree A nodes z M D hM hD hnodesDist hnodesNorm hzNorm

end MathlibAnalytic
end MGAP4D
