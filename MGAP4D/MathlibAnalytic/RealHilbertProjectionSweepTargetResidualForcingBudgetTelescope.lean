import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateTargetResidualCommutatorNonexpansiveStep
import Mathlib.Tactic

/-!
# Target-residual forcing-budget telescope

A one-step estimate

  ||r_target(P_source x)|| <= forcing(source,x) + ||r_target(x)||

implies the ordered-sweep bound by the accumulated forcing and the initial
residual. Each forcing is evaluated at its actual intermediate stage vector.
Feedback introduces no multiplicity. No finite-cardinality Cauchy estimate,
arbitrary factor two, reordering, or positive-beta commutativity is used.
The explicit List.rec definition also exposes := to the source preflight.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

/-- Recursive forcing budget along the actual ordered projection trajectory. -/
def realHilbertProjectionSweepTargetResidualForcingBudget
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (forcing : C → E → ℝ) :
    List C → E → ℝ :=
  fun sources =>
    List.rec
      (motive := fun _ => E → ℝ)
      (fun _ => 0)
      (fun source _sources tailBudget x =>
        forcing source x + tailBudget (P source x))
      sources

/-- Generic list telescope from a one-step forcing estimate. -/
theorem realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_add_initial
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target : C)
    (forcing : C → E → ℝ)
    (hStep : ∀ (source : C) (x : E),
      ‖P source x - P target (P source x)‖ ≤
        forcing source x + ‖x - P target x‖)
    (sources : List C) (x : E) :
    ‖realHilbertProjectionSweep P sources x -
        P target (realHilbertProjectionSweep P sources x)‖ ≤
      realHilbertProjectionSweepTargetResidualForcingBudget P forcing sources x +
        ‖x - P target x‖ := by
  induction sources generalizing x with
  | nil =>
      simpa only [realHilbertProjectionSweep,
        realHilbertProjectionSweepTargetResidualForcingBudget,
        ContinuousLinearMap.id_apply, zero_add] using
        (le_rfl : ‖x - P target x‖ ≤ ‖x - P target x‖)
  | cons source sources ih =>
      have hTail := ih (P source x)
      have hOne := hStep source x
      simp only [realHilbertProjectionSweep, ContinuousLinearMap.comp_apply]
      calc
        ‖realHilbertProjectionSweep P sources (P source x) -
            P target (realHilbertProjectionSweep P sources (P source x))‖ ≤
          realHilbertProjectionSweepTargetResidualForcingBudget
              P forcing sources (P source x) +
            ‖P source x - P target (P source x)‖ := hTail
        _ ≤ realHilbertProjectionSweepTargetResidualForcingBudget
              P forcing sources (P source x) +
            (forcing source x + ‖x - P target x‖) :=
          _root_.add_le_add le_rfl hOne
        _ = realHilbertProjectionSweepTargetResidualForcingBudget
              P forcing (source :: sources) x + ‖x - P target x‖ := by
          change
            realHilbertProjectionSweepTargetResidualForcingBudget
                P forcing sources (P source x) +
              (forcing source x + ‖x - P target x‖) =
            (forcing source x +
              realHilbertProjectionSweepTargetResidualForcingBudget
                P forcing sources (P source x)) + ‖x - P target x‖
          ring

/-- A target-fixed initial vector has no initial residual contribution. -/
theorem realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_of_fixed
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target : C)
    (forcing : C → E → ℝ)
    (hStep : ∀ (source : C) (x : E),
      ‖P source x - P target (P source x)‖ ≤
        forcing source x + ‖x - P target x‖)
    (sources : List C) (x : E) (hFixed : P target x = x) :
    ‖realHilbertProjectionSweep P sources x -
        P target (realHilbertProjectionSweep P sources x)‖ ≤
      realHilbertProjectionSweepTargetResidualForcingBudget P forcing sources x := by
  have h := realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_add_initial
    P target forcing hStep sources x
  simpa only [hFixed, sub_self, norm_zero, add_zero] using h

/-- Commutator forcing evaluated on the actual ordered source trajectory. -/
def realHilbertProjectionSweepTargetResidualCommutatorForcingBudget
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target : C) : List C → E → ℝ :=
  realHilbertProjectionSweepTargetResidualForcingBudget P
    (fun source x =>
      realHilbertProjectionSweepTargetSourceCommutatorCoefficient P target source *
        ‖P target x‖)

/-- The complete residual is bounded by commutator forcing and initial residual. -/
theorem realHilbertProjectionSweep_targetResidual_norm_le_commutatorForcingBudget_add_initial
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target : C)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hSymm : ∀ (c : C) (x y : E), inner ℝ (P c x) y = inner ℝ x (P c y))
    (sources : List C) (x : E) :
    ‖realHilbertProjectionSweep P sources x -
        P target (realHilbertProjectionSweep P sources x)‖ ≤
      realHilbertProjectionSweepTargetResidualCommutatorForcingBudget P target sources x +
        ‖x - P target x‖ := by
  exact realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_add_initial
    P target
    (fun source y =>
      realHilbertProjectionSweepTargetSourceCommutatorCoefficient P target source * ‖P target y‖)
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
    (hSymm : ∀ (c : C) (x y : E), inner ℝ (P c x) y = inner ℝ x (P c y))
    (sources : List C) (x : E) (hFixed : P target x = x) :
    ‖realHilbertProjectionSweep P sources x -
        P target (realHilbertProjectionSweep P sources x)‖ ≤
      realHilbertProjectionSweepTargetResidualCommutatorForcingBudget P target sources x := by
  exact realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_of_fixed
    P target
    (fun source y =>
      realHilbertProjectionSweepTargetSourceCommutatorCoefficient P target source * ‖P target y‖)
    (fun source y =>
      realHilbertProjectionSweep_targetResidual_apply_norm_le_commutatorCoefficient_mul_projectedNorm_add_residual
        P target source hIdem hSymm y)
    sources x hFixed

end

end MGAP4D.MathlibAnalytic
