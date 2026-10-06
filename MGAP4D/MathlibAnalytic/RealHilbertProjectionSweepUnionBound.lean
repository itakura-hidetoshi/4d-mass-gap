import MGAP4D.MathlibAnalytic.RealHilbertCommutingProjectionSweepTensorization
import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepVectorTelescoping

/-!
# Noncommuting projection sweeps: initial defects control actual path loss

Reuse the existing chronological sweep and path loss. For orthogonal
projections P_i, with NO cross-projection commutativity, prove

  PathLoss(cs,x) + 2 ||x - Sweep(cs)x||^2 <= 4 sum_i ||x - P_i x||^2,
  ||x - Sweep(cs)x||^2 <= sum_i ||x - P_i x||^2.

The initial vector on the right is fixed throughout. The proof telescopes a
one-step Pythagorean potential, rather than identifying path loss with total
vector displacement. Empty lists and repeated labels are allowed. No finite
dimension, normalized input, completeness, or probability hypothesis is used.

This is a real-Hilbert version of the projection union-bound mechanism; see
J. Gao, Quantum union bounds for sequential projective measurements,
Phys. Rev. A 92, 052331 (2015), arXiv:1410.5688. All statements below are
proved from the existing projection identities and mathlib, not imported
as an axiom or an external numerical certificate.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

variable {E C : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pythagoras with a fixed reference x and an independently moving input y. -/
theorem realHilbertProjection_reference_distance_sq
    (P : E →L[ℝ] E) (hIdem : P.comp P = P)
    (hSymm : ∀ x y : E, inner ℝ (P x) y = inner ℝ x (P y)) (x y : E) :
    ‖x - P y‖ ^ 2 = ‖x - P x‖ ^ 2 + ‖P (x - y)‖ ^ 2 := by
  have hFixed : P (P (x - y)) = P (x - y) :=
    congrArg (fun Q : E →L[ℝ] E => Q (x - y)) hIdem
  have hOrth := realHilbertProjection_defect_inner_eq_zero_of_fixed
    P hSymm x (P (x - y)) hFixed
  have hSplit : x - P y = (x - P x) + P (x - y) := by
    rw [map_sub]
    abel
  rw [hSplit, norm_add_sq_real, hOrth]
  ring

/-- The one-step union potential pays only for the defect of the reference x. -/
theorem realHilbertProjection_union_potential_step
    (P : E →L[ℝ] E) (hIdem : P.comp P = P)
    (hSymm : ∀ x y : E, inner ℝ (P x) y = inner ℝ x (P y)) (x y : E) :
    ‖y - P y‖ ^ 2 + 2 * ‖x - P y‖ ^ 2 ≤
      2 * ‖x - y‖ ^ 2 + 4 * ‖x - P x‖ ^ 2 := by
  let a := x - P x
  let b := (x - y) - P (x - y)
  have hSplit : y - P y = a - b := by
    dsimp [a, b]
    rw [map_sub]
    abel
  have hsq : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (norm_sub_le a b)
  have hSmall : ‖y - P y‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    rw [hSplit]
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  dsimp [a, b] at hSmall
  have hDist := realHilbertProjection_reference_distance_sq P hIdem hSymm x y
  have hPyth := realHilbertProjection_residual_norm_sq P hIdem hSymm (x - y)
  linarith

/-- Telescoping potential for arbitrary starting y and fixed reference x. -/
theorem realHilbertProjectionSweep_union_potential
    (P : C → E →L[ℝ] E) (hIdem : ∀ c, (P c).comp (P c) = P c)
    (hSymm : ∀ c (x y : E), inner ℝ (P c x) y = inner ℝ x (P c y))
    (cs : List C) (x y : E) :
    realHilbertProjectionSweepPathLoss P cs y +
        2 * ‖x - realHilbertProjectionSweep P cs y‖ ^ 2 ≤
      2 * ‖x - y‖ ^ 2 + 4 * (cs.map fun c => ‖x - P c x‖ ^ 2).sum := by
  induction cs generalizing y with
  | nil => simp [realHilbertProjectionSweepPathLoss, realHilbertProjectionSweep]
  | cons c cs ih =>
      have hStep := realHilbertProjection_union_potential_step (P c) (hIdem c) (hSymm c) x y
      have hTail := ih (P c y)
      simp only [realHilbertProjectionSweepPathLoss, realHilbertProjectionSweep,
        ContinuousLinearMap.comp_apply, List.map_cons, List.sum_cons]
      linarith

/-- A strengthened union bound: actual losses and total displacement stay distinct. -/
theorem realHilbertProjectionSweep_pathLoss_add_two_displacement_sq_le_four_initial
    (P : C → E →L[ℝ] E) (hIdem : ∀ c, (P c).comp (P c) = P c)
    (hSymm : ∀ c (x y : E), inner ℝ (P c x) y = inner ℝ x (P c y))
    (cs : List C) (x : E) :
    realHilbertProjectionSweepPathLoss P cs x +
        2 * ‖x - realHilbertProjectionSweep P cs x‖ ^ 2 ≤
      4 * (cs.map fun c => ‖x - P c x‖ ^ 2).sum := by
  simpa using realHilbertProjectionSweep_union_potential P hIdem hSymm cs x x

/-- Actual chronological path loss is at most four times the original defects. -/
theorem realHilbertProjectionSweep_pathLoss_le_four_initial
    (P : C → E →L[ℝ] E) (hIdem : ∀ c, (P c).comp (P c) = P c)
    (hSymm : ∀ c (x y : E), inner ℝ (P c x) y = inner ℝ x (P c y))
    (cs : List C) (x : E) :
    realHilbertProjectionSweepPathLoss P cs x ≤
      4 * (cs.map fun c => ‖x - P c x‖ ^ 2).sum := by
  have h := realHilbertProjectionSweep_pathLoss_add_two_displacement_sq_le_four_initial
    P hIdem hSymm cs x
  nlinarith [sq_nonneg ‖x - realHilbertProjectionSweep P cs x‖]

/-- Squared displacement from a fixed reference has coefficient-one accumulation. -/
theorem realHilbertProjectionSweep_reference_distance_sq_le
    (P : C → E →L[ℝ] E) (hIdem : ∀ c, (P c).comp (P c) = P c)
    (hSymm : ∀ c (x y : E), inner ℝ (P c x) y = inner ℝ x (P c y))
    (cs : List C) (x y : E) :
    ‖x - realHilbertProjectionSweep P cs y‖ ^ 2 ≤
      ‖x - y‖ ^ 2 + (cs.map fun c => ‖x - P c x‖ ^ 2).sum := by
  induction cs generalizing y with
  | nil => simp [realHilbertProjectionSweep]
  | cons c cs ih =>
      have hTail := ih (P c y)
      have hDist := realHilbertProjection_reference_distance_sq (P c) (hIdem c) (hSymm c) x y
      have hPyth := realHilbertProjection_residual_norm_sq (P c) (hIdem c) (hSymm c) (x - y)
      simp only [realHilbertProjectionSweep, ContinuousLinearMap.comp_apply,
        List.map_cons, List.sum_cons]
      nlinarith [sq_nonneg ‖(x - y) - P c (x - y)‖]

/-- No commutativity is needed for this inequality, unlike an exact defect decomposition. -/
theorem realHilbertProjectionSweep_displacement_sq_le_initial
    (P : C → E →L[ℝ] E) (hIdem : ∀ c, (P c).comp (P c) = P c)
    (hSymm : ∀ c (x y : E), inner ℝ (P c x) y = inner ℝ x (P c y))
    (cs : List C) (x : E) :
    ‖x - realHilbertProjectionSweep P cs x‖ ^ 2 ≤
      (cs.map fun c => ‖x - P c x‖ ^ 2).sum := by
  simpa using realHilbertProjectionSweep_reference_distance_sq_le P hIdem hSymm cs x x

/-- Append bookkeeping for the existing path loss, used to expose an arbitrary stage. -/
theorem realHilbertProjectionSweepPathLoss_append_union
    (P : C → E →L[ℝ] E) (pre suffix : List C) (x : E) :
    realHilbertProjectionSweepPathLoss P (pre ++ suffix) x =
      realHilbertProjectionSweepPathLoss P pre x +
        realHilbertProjectionSweepPathLoss P suffix (realHilbertProjectionSweep P pre x) := by
  induction pre generalizing x with
  | nil => simp [realHilbertProjectionSweepPathLoss, realHilbertProjectionSweep]
  | cons c pre ih =>
      simp only [List.cons_append, realHilbertProjectionSweepPathLoss,
        realHilbertProjectionSweep, ContinuousLinearMap.comp_apply]
      rw [ih]
      ring

/-- Every selected prefix stage is bounded by original one-link L2 defects. -/
theorem realHilbertProjectionSweep_stageResidual_sq_le_four_initial
    (P : C → E →L[ℝ] E) (hIdem : ∀ c, (P c).comp (P c) = P c)
    (hSymm : ∀ c (x y : E), inner ℝ (P c x) y = inner ℝ x (P c y))
    (pre : List C) (e : C) (x : E) :
    ‖realHilbertProjectionSweep P pre x - P e (realHilbertProjectionSweep P pre x)‖ ^ 2 ≤
      4 * ((pre ++ [e]).map fun c => ‖x - P c x‖ ^ 2).sum := by
  have h := realHilbertProjectionSweep_pathLoss_le_four_initial P hIdem hSymm (pre ++ [e]) x
  rw [realHilbertProjectionSweepPathLoss_append_union] at h
  simp only [realHilbertProjectionSweepPathLoss, add_zero] at h
  have hPre := realHilbertProjectionSweepPathLoss_nonneg P pre x
  linarith

end

end MGAP4D.MathlibAnalytic
