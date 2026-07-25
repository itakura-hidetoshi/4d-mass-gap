import MGAP4D.MathlibAnalytic.ContinuousLinearMapOneSidedConfluentResolventJet
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

variable {α E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A word consisting of two repeated blocks evaluates to the product of the
corresponding operator powers. -/
@[simp] theorem orderedProduct_replicate_append_replicate
    (A : α → E →L[ℝ] E)
    (a b : α)
    (m n : ℕ) :
    orderedProduct A (List.replicate m a ++ List.replicate n b) =
      (A a) ^ m * (A b) ^ n := by
  simp [orderedProduct_append]

/-- The two-sided confluent resolvent jet normal form.  The boundary values are
pure powers at either node, and the interior obeys the Pascal-type resolvent
recursion.  No repeated-node denominator appears. -/
noncomputable def twoSidedConfluentResolventJetNormalForm
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ) :
    ℕ → ℕ → E →L[ℝ] E
  | 0, n => Rmu ^ n
  | m + 1, 0 => Rlambda ^ (m + 1)
  | m + 1, n + 1 =>
      (lambda - mu)⁻¹ •
        (twoSidedConfluentResolventJetNormalForm
            Rlambda Rmu lambda mu (m + 1) n -
          twoSidedConfluentResolventJetNormalForm
            Rlambda Rmu lambda mu m (n + 1))
termination_by m n => m + n

@[simp] theorem twoSidedConfluentResolventJetNormalForm_zero_left
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ)
    (n : ℕ) :
    twoSidedConfluentResolventJetNormalForm
      Rlambda Rmu lambda mu 0 n = Rmu ^ n := by
  simp [twoSidedConfluentResolventJetNormalForm]

@[simp] theorem twoSidedConfluentResolventJetNormalForm_zero_right
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ)
    (m : ℕ) :
    twoSidedConfluentResolventJetNormalForm
      Rlambda Rmu lambda mu (m + 1) 0 = Rlambda ^ (m + 1) := by
  simp [twoSidedConfluentResolventJetNormalForm]

@[simp] theorem twoSidedConfluentResolventJetNormalForm_succ_succ
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ)
    (m n : ℕ) :
    twoSidedConfluentResolventJetNormalForm
        Rlambda Rmu lambda mu (m + 1) (n + 1) =
      (lambda - mu)⁻¹ •
        (twoSidedConfluentResolventJetNormalForm
            Rlambda Rmu lambda mu (m + 1) n -
          twoSidedConfluentResolventJetNormalForm
            Rlambda Rmu lambda mu m (n + 1)) := by
  simp [twoSidedConfluentResolventJetNormalForm]

/-- The two-sided confluent normal form extends the one-sided recursion when the
second multiplicity is one. -/
theorem twoSidedConfluentResolventJetNormalForm_succ_one_eq_oneSided
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ) :
    ∀ m : ℕ,
      twoSidedConfluentResolventJetNormalForm
          Rlambda Rmu lambda mu m 1 =
        oneSidedConfluentResolventJetNormalForm
          Rlambda Rmu lambda mu m := by
  intro m
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [twoSidedConfluentResolventJetNormalForm_succ_succ]
      rw [oneSidedConfluentResolventJetNormalForm_succ]
      simp [ih]

/-- Under the real resolvent identity, arbitrary finite powers at two distinct
nodes are exactly the two-sided confluent jet normal form. -/
theorem pow_mul_pow_eq_twoSidedConfluentResolventJetNormalForm
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ)
    (hne : lambda ≠ mu)
    (hIdentity :
      Rlambda - Rmu =
        (lambda - mu) • (Rlambda * Rmu)) :
    ∀ m n : ℕ,
      Rlambda ^ m * Rmu ^ n =
        twoSidedConfluentResolventJetNormalForm
          Rlambda Rmu lambda mu m n := by
  intro m
  induction m with
  | zero =>
      intro n
      simp
  | succ m ihM =>
      intro n
      induction n with
      | zero =>
          simp
      | succ n ihN =>
          rw [twoSidedConfluentResolventJetNormalForm_succ_succ]
          rw [← ihN, ← ihM (n + 1)]
          have hDifference :
              Rlambda ^ (m + 1) * Rmu ^ n -
                  Rlambda ^ m * Rmu ^ (n + 1) =
                (lambda - mu) •
                  (Rlambda ^ (m + 1) * Rmu ^ (n + 1)) := by
            calc
              Rlambda ^ (m + 1) * Rmu ^ n -
                    Rlambda ^ m * Rmu ^ (n + 1) =
                  Rlambda ^ m * (Rlambda - Rmu) * Rmu ^ n := by
                    rw [pow_succ Rlambda m, pow_succ' Rmu n]
                    noncomm_ring
              _ = Rlambda ^ m *
                    ((lambda - mu) • (Rlambda * Rmu)) * Rmu ^ n := by
                    rw [hIdentity]
              _ = (lambda - mu) •
                    ((Rlambda ^ m * (Rlambda * Rmu)) * Rmu ^ n) := by
                    rw [mul_smul_comm, smul_mul_assoc]
              _ = (lambda - mu) •
                    (Rlambda ^ (m + 1) * Rmu ^ (n + 1)) := by
                    congr 1
                    rw [pow_succ Rlambda m, pow_succ' Rmu n]
                    noncomm_ring
          rw [hDifference, smul_smul]
          rw [inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]

/-- Pointwise form of the two-sided confluent resolvent jet identity. -/
theorem pow_apply_pow_eq_twoSidedConfluentResolventJetNormalForm_apply
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ)
    (hne : lambda ≠ mu)
    (hIdentity :
      Rlambda - Rmu =
        (lambda - mu) • (Rlambda * Rmu))
    (m n : ℕ)
    (x : E) :
    (Rlambda ^ m) ((Rmu ^ n) x) =
      twoSidedConfluentResolventJetNormalForm
        Rlambda Rmu lambda mu m n x := by
  have hOperator :=
    pow_mul_pow_eq_twoSidedConfluentResolventJetNormalForm
      Rlambda Rmu lambda mu hne hIdentity m n
  exact DFunLike.congr_fun hOperator x

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
