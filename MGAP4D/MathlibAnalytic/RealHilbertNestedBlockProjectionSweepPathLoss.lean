import MGAP4D.MathlibAnalytic.RealHilbertCommutingProjectionSweepTensorization
import Mathlib.Tactic

/-!
# Nested block projection dominates sequential projection path loss

For a real Hilbert space, let B be one orthogonal block projection and let
P_c be a finite sequence of orthogonal projections.  Assume the block range is
contained in every retained one-link range appearing in the sequence.  At the
operator level this is the absorption identity

  B (P_c x) = B x.

Then B also absorbs the complete ordered sweep.  Since B is norm-contracting,

  ||B x|| <= ||P_sweep x||.

Exact Pythagoras for B and the exact telescoping path-loss identity for the
ordered sweep therefore give

  pathLoss(P, cs, x) <= ||x - B x||^2.

No commutativity between the P_c is required.

This is the Hilbert-space bridge needed when a positive-beta color-block
conditional expectation is stronger than all one-link conditional
expectations in that color.  It allows local sweep residuals to be charged to
one fixed color-block residual without a cardinality factor.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

/-- A block projection that absorbs every projection in an ordered list also
absorbs their complete sweep. -/
theorem realHilbertNestedBlock_projectionSweep_absorb
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (B : E →L[ℝ] E)
    (P : C → E →L[ℝ] E)
    (cs : List C)
    (hAbsorb : ∀ c ∈ cs, ∀ x : E, B (P c x) = B x)
    (x : E) :
    B (realHilbertProjectionSweep P cs x) = B x := by
  induction cs generalizing x with
  | nil =>
      simp [realHilbertProjectionSweep]
  | cons c cs ih =>
      simp only [realHilbertProjectionSweep, ContinuousLinearMap.comp_apply]
      have hHead : ∀ y : E, B (P c y) = B y := by
        intro y
        exact hAbsorb c (by simp) y
      have hTail :
          ∀ d ∈ cs, ∀ y : E, B (P d y) = B y := by
        intro d hd y
        exact hAbsorb d (by simp [hd]) y
      calc
        B (realHilbertProjectionSweep P cs (P c x)) =
            B (P c x) :=
          ih hTail (P c x)
        _ = B x := hHead x

/-- Under the same absorption hypothesis, the norm of the block projection is
bounded by the norm left after the ordered sweep. -/
theorem realHilbertNestedBlock_norm_le_projectionSweep
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (B : E →L[ℝ] E)
    (hBid : B.comp B = B)
    (hBsymm : ∀ x y : E, inner ℝ (B x) y = inner ℝ x (B y))
    (P : C → E →L[ℝ] E)
    (cs : List C)
    (hAbsorb : ∀ c ∈ cs, ∀ x : E, B (P c x) = B x)
    (x : E) :
    ‖B x‖ ≤ ‖realHilbertProjectionSweep P cs x‖ := by
  have hEq :
      B (realHilbertProjectionSweep P cs x) = B x :=
    realHilbertNestedBlock_projectionSweep_absorb B P cs hAbsorb x
  calc
    ‖B x‖ =
        ‖B (realHilbertProjectionSweep P cs x)‖ := by
      rw [hEq]
    _ ≤ ‖realHilbertProjectionSweep P cs x‖ :=
      realHilbertProjection_norm_le
        B hBid hBsymm
        (realHilbertProjectionSweep P cs x)

/-- Main nested-block theorem: the squared residual of the stronger block
projection dominates the entire telescoping path loss of an arbitrary ordered
sequence of weaker orthogonal projections. -/
theorem realHilbertNestedBlock_projectionSweepPathLoss_le_residual
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (B : E →L[ℝ] E)
    (hBid : B.comp B = B)
    (hBsymm : ∀ x y : E, inner ℝ (B x) y = inner ℝ x (B y))
    (P : C → E →L[ℝ] E)
    (hPid : ∀ c : C, (P c).comp (P c) = P c)
    (hPsymm : ∀ (c : C) (x y : E),
      inner ℝ (P c x) y = inner ℝ x (P c y))
    (cs : List C)
    (hAbsorb : ∀ c ∈ cs, ∀ x : E, B (P c x) = B x)
    (x : E) :
    realHilbertProjectionSweepPathLoss P cs x ≤
      ‖x - B x‖ ^ 2 := by
  have hNorm :
      ‖B x‖ ≤ ‖realHilbertProjectionSweep P cs x‖ :=
    realHilbertNestedBlock_norm_le_projectionSweep
      B hBid hBsymm P cs hAbsorb x
  have hNormSq :
      ‖B x‖ ^ 2 ≤ ‖realHilbertProjectionSweep P cs x‖ ^ 2 := by
    nlinarith [
      norm_nonneg (B x),
      norm_nonneg (realHilbertProjectionSweep P cs x)]
  have hSweepLoss :=
    realHilbertProjectionSweep_norm_sq_loss
      P hPid hPsymm cs x
  have hBlockResidual :=
    realHilbertProjection_residual_norm_sq
      B hBid hBsymm x
  calc
    realHilbertProjectionSweepPathLoss P cs x =
        ‖x‖ ^ 2 - ‖realHilbertProjectionSweep P cs x‖ ^ 2 :=
      hSweepLoss.symm
    _ ≤ ‖x‖ ^ 2 - ‖B x‖ ^ 2 := by
      linarith
    _ = ‖x - B x‖ ^ 2 :=
      hBlockResidual.symm

end

end MGAP4D.MathlibAnalytic
