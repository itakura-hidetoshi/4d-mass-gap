import MGAP4D.MathlibAnalytic.ContinuousLinearMapFinitePowerJetCombination
import MGAP4D.MathlibAnalytic.ContinuousLinearMapResolventDividedDifference
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

variable {α E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Ordered products turn list concatenation into operator multiplication. -/
@[simp] theorem orderedProduct_append
    (A : α → E →L[ℝ] E)
    (s t : List α) :
    orderedProduct A (s ++ t) = orderedProduct A s * orderedProduct A t := by
  induction s with
  | nil =>
      simp [orderedProduct]
  | cons a s ih =>
      simp [orderedProduct, ih, mul_assoc]

/-- A word consisting of one repeated node followed by one distinct node is the
corresponding power times the final operator. -/
@[simp] theorem orderedProduct_replicate_append_singleton
    (A : α → E →L[ℝ] E)
    (a b : α)
    (n : ℕ) :
    orderedProduct A (List.replicate n a ++ [b]) = (A a) ^ n * A b := by
  simp [orderedProduct_append, orderedProduct]

/-- The one-sided confluent resolvent jet normal form.  It treats an arbitrary
finite multiplicity at `lambda` and one simple node at the distinct parameter
`mu`.  The recursion explicitly generates the Hermite partial-fraction
coefficients without dividing by a repeated-node difference. -/
noncomputable def oneSidedConfluentResolventJetNormalForm
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ) :
    ℕ → E →L[ℝ] E
  | 0 => Rmu
  | n + 1 =>
      (lambda - mu)⁻¹ •
        (Rlambda ^ (n + 1) -
          oneSidedConfluentResolventJetNormalForm
            Rlambda Rmu lambda mu n)

@[simp] theorem oneSidedConfluentResolventJetNormalForm_zero
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ) :
    oneSidedConfluentResolventJetNormalForm
      Rlambda Rmu lambda mu 0 = Rmu := by
  simp [oneSidedConfluentResolventJetNormalForm]

@[simp] theorem oneSidedConfluentResolventJetNormalForm_succ
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ)
    (n : ℕ) :
    oneSidedConfluentResolventJetNormalForm
        Rlambda Rmu lambda mu (n + 1) =
      (lambda - mu)⁻¹ •
        (Rlambda ^ (n + 1) -
          oneSidedConfluentResolventJetNormalForm
            Rlambda Rmu lambda mu n) := by
  simp [oneSidedConfluentResolventJetNormalForm]

/-- Under the real resolvent identity, an arbitrary power at one node followed
by one resolvent at a distinct node is exactly its one-sided confluent jet
normal form. -/
theorem pow_mul_eq_oneSidedConfluentResolventJetNormalForm
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ)
    (hne : lambda ≠ mu)
    (hIdentity :
      Rlambda - Rmu =
        (lambda - mu) • (Rlambda * Rmu)) :
    ∀ n : ℕ,
      Rlambda ^ n * Rmu =
        oneSidedConfluentResolventJetNormalForm
          Rlambda Rmu lambda mu n := by
  intro n
  have hProduct :
      Rlambda * Rmu =
        (lambda - mu)⁻¹ • (Rlambda - Rmu) := by
    simpa using
      (comp_eq_inv_smul_sub_of_resolvent_identity_of_ne
        Rlambda Rmu lambda mu hne hIdentity)
  induction n with
  | zero =>
      simp [oneSidedConfluentResolventJetNormalForm]
  | succ n ih =>
      rw [oneSidedConfluentResolventJetNormalForm_succ]
      calc
        Rlambda ^ (n + 1) * Rmu =
            Rlambda ^ n * (Rlambda * Rmu) := by
              rw [pow_succ, mul_assoc]
        _ = Rlambda ^ n *
            ((lambda - mu)⁻¹ • (Rlambda - Rmu)) := by
              rw [hProduct]
        _ = (lambda - mu)⁻¹ •
            (Rlambda ^ n * (Rlambda - Rmu)) := by
              rw [mul_smul_comm]
        _ = (lambda - mu)⁻¹ •
            (Rlambda ^ (n + 1) - Rlambda ^ n * Rmu) := by
              rw [mul_sub, pow_succ]
        _ = (lambda - mu)⁻¹ •
            (Rlambda ^ (n + 1) -
              oneSidedConfluentResolventJetNormalForm
                Rlambda Rmu lambda mu n) := by
              rw [ih]

/-- Pointwise form of the one-sided confluent resolvent jet identity. -/
theorem pow_apply_comp_eq_oneSidedConfluentResolventJetNormalForm_apply
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ)
    (hne : lambda ≠ mu)
    (hIdentity :
      Rlambda - Rmu =
        (lambda - mu) • (Rlambda * Rmu))
    (n : ℕ)
    (x : E) :
    (Rlambda ^ n) (Rmu x) =
      oneSidedConfluentResolventJetNormalForm
        Rlambda Rmu lambda mu n x := by
  have hOperator :=
    pow_mul_eq_oneSidedConfluentResolventJetNormalForm
      Rlambda Rmu lambda mu hne hIdentity n
  exact DFunLike.congr_fun hOperator x

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
