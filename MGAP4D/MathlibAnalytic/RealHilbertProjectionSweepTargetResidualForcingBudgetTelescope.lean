import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateTargetResidualCommutatorNonexpansiveStep
import Mathlib.Tactic

/-!
# Target-residual forcing-budget telescope

Suppose every ordered source step satisfies a one-step estimate

  ||r_target(P_source x)||
    <= forcing(source,x) + ||r_target(x)||.

Then an arbitrary ordered source sweep satisfies

  ||r_target(sweep sources x)||
    <= accumulatedForcing(sources,x) + ||r_target(x)||,

where the forcing budget is evaluated at the actual intermediate stage vector
before each source projection.

This is the correct list-level receiver for the cyclic second-visit argument:
the feedback transports the already-created target residual without any
multiplicity, while each source contributes its forcing exactly once.

The file also instantiates the generic receiver with the commutator coefficient
from PRs #4917--#4919.

No finite-cardinality Cauchy estimate, arbitrary factor two, source reordering,
or positive-beta commutativity is used.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

/-- Recursive forcing budget evaluated along the actual ordered projection
trajectory. -/
def realHilbertProjectionSweepTargetResidualForcingBudget
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (forcing : C → E → ℝ) :
    List C → E → ℝ
  | [], _ => 0
  | source :: sources, x =>
      forcing source x +
        realHilbertProjectionSweepTargetResidualForcingBudget
          P forcing sources (P source x)

/-- Generic list telescope from a one-step target-residual forcing estimate. -/
theorem realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_add_initial
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target : C)
    (forcing : C → E → ℝ)
    (hStep :
      ∀ (source : C) (x : E),
        ‖P source x - P target (P source x)‖ ≤
          forcing source x + ‖x - P target x‖)
    (sources : List C)
    (x : E) :
    ‖realHilbertProjectionSweep P sources x -
        P target (realHilbertProjectionSweep P sources x)‖ ≤
      realHilbertProjectionSweepTargetResidualForcingBudget
          P forcing sources x +
        ‖x - P target x‖ := by
  induction sources generalizing x with
  | nil =>
      simp [
        realHilbertProjectionSweep,
        realHilbertProjectionSweepTargetResidualForcingBudget]
  | cons source sources ih =>
      have hTail := ih (P source x)
      have hOne := hStep source x
      simp only [
        realHilbertProjectionSweep,
        ContinuousLinearMap.comp_apply]
      calc
        ‖realHilbertProjectionSweep P sources (P source x) -
            P target
              (realHilbertProjectionSweep P sources (P source x))‖ ≤
          realHilbertProjectionSweepTargetResidualForcingBudget
              P forcing sources (P source x) +
            ‖P source x - P target (P source x)‖ := hTail
        _ ≤
          realHilbertProjectionSweepTargetResidualForcingBudget
              P forcing sources (P source x) +
            (forcing source x + ‖x - P target x‖) := by
              exact add_le_add_left hOne _
        _ =
          realHilbertProjectionSweepTargetResidualForcingBudget
              P forcing (source :: sources) x +
            ‖x - P target x‖ := by
              simp [
                realHilbertProjectionSweepTargetResidualForcingBudget]
              ring

/-- If the initial vector is already target-fixed, the final target residual is
controlled purely by the accumulated forcing budget. -/
theorem realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_of_fixed
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target : C)
    (forcing : C → E → ℝ)
    (hStep :
      ∀ (source : C) (x : E),
        ‖P source x - P target (P source x)‖ ≤
          forcing source x + ‖x - P target x‖)
    (sources : List C)
    (x : E)
    (hFixed : P target x = x) :
    ‖realHilbertProjectionSweep P sources x -
        P target (realHilbertProjectionSweep P sources x)‖ ≤
      realHilbertProjectionSweepTargetResidualForcingBudget
        P forcing sources x := by
  have h :=
    realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_add_initial
      P target forcing hStep sources x
  rw [hFixed, sub_self, norm_zero, add_zero] at h
  exact h

/-- The commutator forcing evaluated along an ordered source trajectory. -/
def realHilbertProjectionSweepTargetResidualCommutatorForcingBudget
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target : C) :
    List C → E → ℝ :=
  realHilbertProjectionSweepTargetResidualForcingBudget
    P
    (fun source x =>
      realHilbertProjectionSweepTargetSourceCommutatorCoefficient
          P target source *
        ‖P target x‖)

/-- For self-adjoint idempotent projections, the complete target residual is
controlled by the accumulated commutator forcing plus the initial target
residual. -/
theorem realHilbertProjectionSweep_targetResidual_norm_le_commutatorForcingBudget_add_initial
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target : C)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hSymm : ∀ (c : C) (x y : E),
      inner ℝ (P c x) y = inner ℝ x (P c y))
    (sources : List C)
    (x : E) :
    ‖realHilbertProjectionSweep P sources x -
        P target (realHilbertProjectionSweep P sources x)‖ ≤
      realHilbertProjectionSweepTargetResidualCommutatorForcingBudget
          P target sources x +
        ‖x - P target x‖ := by
  exact
    realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_add_initial
      P target
      (fun source y =>
        realHilbertProjectionSweepTargetSourceCommutatorCoefficient
            P target source *
          ‖P target y‖)
      (fun source y =>
        realHilbertProjectionSweep_targetResidual_apply_norm_le_commutatorCoefficient_mul_projectedNorm_add_residual
          P target source hIdem hSymm y)
      sources x

/-- Target-fixed specialization of the commutator-forcing telescope. -/
theorem realHilbertProjectionSweep_targetResidual_norm_le_commutatorForcingBudget_of_fixed
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target : C)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hSymm : ∀ (c : C) (x y : E),
      inner ℝ (P c x) y = inner ℝ x (P c y))
    (sources : List C)
    (x : E)
    (hFixed : P target x = x) :
    ‖realHilbertProjectionSweep P sources x -
        P target (realHilbertProjectionSweep P sources x)‖ ≤
      realHilbertProjectionSweepTargetResidualCommutatorForcingBudget
        P target sources x := by
  exact
    realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_of_fixed
      P target
      (fun source y =>
        realHilbertProjectionSweepTargetSourceCommutatorCoefficient
            P target source *
          ‖P target y‖)
      (fun source y =>
        realHilbertProjectionSweep_targetResidual_apply_norm_le_commutatorCoefficient_mul_projectedNorm_add_residual
          P target source hIdem hSymm y)
      sources x hFixed

end

end MGAP4D.MathlibAnalytic
