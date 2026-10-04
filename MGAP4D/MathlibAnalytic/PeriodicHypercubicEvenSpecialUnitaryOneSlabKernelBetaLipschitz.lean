import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationDiagnostic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Operator-facing beta Lipschitz control for the exact one-slab Wilson kernel

The exact finite-volume one-slab kernel is

  K_beta(A,B) = exp (- beta * S_slab(A,B)).

The one-slab action is nonnegative and bounded uniformly in the boundary
configurations by the explicit finite-volume global action budget.  Therefore
the derivative in beta is

  d K_beta / d beta = - S_slab K_beta,

and on the physical half-line beta >= 0 its absolute value is bounded by the
same global action budget because 0 < K_beta <= 1.

The mean-value estimate hence gives the actual-model pointwise Lipschitz bound

  |K_gamma(A,B) - K_beta(A,B)|
    <= globalActionBudget(H) * |gamma - beta|.

No transfer compatibility, gap, thermodynamic-limit, or continuum-limit
assumption enters.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped Topology

noncomputable section

/-- The exact one-slab Wilson kernel has the expected beta derivative. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_hasDerivAt_beta
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    HasDerivAt
      (fun beta' : ℝ =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta' A B)
      (-periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B)
      beta := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B
  have hlinear : HasDerivAt (fun beta' : ℝ => -beta' * S) (-S) beta := by
    simpa [S] using (hasDerivAt_id (x := beta)).neg.mul_const S
  have hexp :
      HasDerivAt
        (fun beta' : ℝ => Real.exp (-beta' * S))
        (Real.exp (-beta * S) * (-S))
        beta :=
    hlinear.exp
  simpa only [S,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    neg_mul, mul_neg, neg_neg, mul_comm, mul_left_comm, mul_assoc] using hexp

/-- The finite one-slab global action budget is nonnegative. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg
    (H : ℕ) :
    0 ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget
  positivity

/-- On the physical nonnegative-coupling half-line, the exact one-slab Wilson
kernel is Lipschitz in beta with the explicit finite-volume global action
budget. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_norm_sub_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N gamma A B -
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta A B‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        ‖gamma - beta‖ := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let S :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B
  let K := fun t : ℝ =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N t A B
  let dK := fun t : ℝ => -S * K t
  have hderiv :
      ∀ t ∈ Ici (0 : ℝ),
        HasDerivWithinAt K (dK t) (Ici (0 : ℝ)) t := by
    intro t ht
    have h :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_hasDerivAt_beta
        H N t A B
    simpa [K, dK, S] using h.hasDerivWithinAt
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hSnonneg : 0 ≤ S := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
        H N hN A B
  have hSle : S ≤ C := by
    simpa [S, C] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
        H N hN A B
  have hSnorm : ‖S‖ ≤ C := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hSnonneg] using hSle
  have hbound :
      ∀ t ∈ Ici (0 : ℝ), ‖dK t‖ ≤ C := by
    intro t ht
    have hKt : |K t| ≤ 1 := by
      simpa [K] using
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
          H N hN t ht A B
    calc
      ‖dK t‖ = ‖S‖ * |K t| := by
        simp [dK, Real.norm_eq_abs]
      _ ≤ C * 1 :=
        mul_le_mul hSnorm hKt (abs_nonneg _) hC
      _ = C := by ring
  have hmvt :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound (convex_Ici (0 : ℝ)) hbeta hgamma
  simpa [K, C] using hmvt

end

end MathlibAnalytic
end MGAP4D
