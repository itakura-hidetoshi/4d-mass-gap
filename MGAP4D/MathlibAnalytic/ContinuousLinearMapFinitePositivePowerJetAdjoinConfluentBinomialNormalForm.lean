import MGAP4D.MathlibAnalytic.ContinuousLinearMapTwoSidedConfluentResolventBinomialNormalForm
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFinitePowerJetCombination
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

variable {α β E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite positive power-jet combination.  The labelled order `order b`
represents the actual positive power `order b + 1`. -/
noncomputable def finitePositivePowerJetCombination
    (A : α → E →L[ℝ] E)
    (s : Finset β)
    (node : β → α)
    (order : β → ℕ)
    (c : β → ℝ) :
    E →L[ℝ] E :=
  finitePowerJetCombination A s node (fun b => order b + 1) c

/-- Adjoin one new positive-multiplicity node to a finite positive power jet by
expanding every old jet term against the new node with the closed two-node
binomial normal form.  Repeated old nodes are allowed. -/
noncomputable def finitePositivePowerJetAdjoinConfluentBinomialNormalForm
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (s : Finset β)
    (node : β → α)
    (order : β → ℕ)
    (c : β → ℝ)
    (newNode : α)
    (newOrder : ℕ) :
    E →L[ℝ] E :=
  s.sum (fun b =>
    c b •
      twoSidedConfluentResolventBinomialNormalForm
        (A (node b)) (A newNode)
        (value (node b) - value newNode)⁻¹
        (order b) newOrder)

/-- Multiplying a finite positive power jet by one new positive resolvent power
is exactly the termwise adjoined closed binomial normal form.  No distinctness
among the old labelled nodes is required. -/
theorem finitePositivePowerJetCombination_mul_pow_succ_eq_adjoinConfluentBinomialNormalForm
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (s : Finset β)
    (node : β → α)
    (order : β → ℕ)
    (c : β → ℝ)
    (newNode : α)
    (newOrder : ℕ)
    (hne : ∀ b ∈ s, value (node b) ≠ value newNode)
    (hIdentity : ∀ b ∈ s,
      A (node b) - A newNode =
        (value (node b) - value newNode) •
          (A (node b) * A newNode)) :
    finitePositivePowerJetCombination A s node order c *
        (A newNode) ^ (newOrder + 1) =
      finitePositivePowerJetAdjoinConfluentBinomialNormalForm
        A value s node order c newNode newOrder := by
  simp only [finitePositivePowerJetCombination, finitePowerJetCombination,
    finitePositivePowerJetAdjoinConfluentBinomialNormalForm]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [smul_mul_assoc]
  rw [pow_succ_mul_pow_succ_eq_twoSidedConfluentResolventBinomialNormalForm
    (A (node b)) (A newNode)
    (value (node b)) (value newNode)
    (hne b hb) (hIdentity b hb) (order b) newOrder]

/-- The adjoined normal form is exactly the finite word-sum obtained by appending
one repeated block to every replicated positive jet word. -/
theorem finitePositivePowerJetAdjoinConfluentBinomialNormalForm_eq_finset_sum_smul_orderedProduct_append_replicate
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (s : Finset β)
    (node : β → α)
    (order : β → ℕ)
    (c : β → ℝ)
    (newNode : α)
    (newOrder : ℕ)
    (hne : ∀ b ∈ s, value (node b) ≠ value newNode)
    (hIdentity : ∀ b ∈ s,
      A (node b) - A newNode =
        (value (node b) - value newNode) •
          (A (node b) * A newNode)) :
    finitePositivePowerJetAdjoinConfluentBinomialNormalForm
        A value s node order c newNode newOrder =
      s.sum (fun b => c b •
        orderedProduct A
          (List.replicate (order b + 1) (node b) ++
            List.replicate (newOrder + 1) newNode)) := by
  calc
    finitePositivePowerJetAdjoinConfluentBinomialNormalForm
        A value s node order c newNode newOrder =
      finitePositivePowerJetCombination A s node order c *
        (A newNode) ^ (newOrder + 1) :=
      (finitePositivePowerJetCombination_mul_pow_succ_eq_adjoinConfluentBinomialNormalForm
        A value s node order c newNode newOrder hne hIdentity).symm
    _ = s.sum (fun b => c b •
        orderedProduct A
          (List.replicate (order b + 1) (node b) ++
            List.replicate (newOrder + 1) newNode)) := by
      rw [finitePositivePowerJetCombination, finitePowerJetCombination,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      simp [orderedProduct_append]

/-- Pointwise form of the finite-jet adjoin identity. -/
theorem finitePositivePowerJetCombination_apply_pow_succ_eq_adjoinConfluentBinomialNormalForm_apply
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (s : Finset β)
    (node : β → α)
    (order : β → ℕ)
    (c : β → ℝ)
    (newNode : α)
    (newOrder : ℕ)
    (hne : ∀ b ∈ s, value (node b) ≠ value newNode)
    (hIdentity : ∀ b ∈ s,
      A (node b) - A newNode =
        (value (node b) - value newNode) •
          (A (node b) * A newNode))
    (x : E) :
    finitePositivePowerJetCombination A s node order c
        (((A newNode) ^ (newOrder + 1)) x) =
      finitePositivePowerJetAdjoinConfluentBinomialNormalForm
        A value s node order c newNode newOrder x := by
  have hOperator :=
    finitePositivePowerJetCombination_mul_pow_succ_eq_adjoinConfluentBinomialNormalForm
      A value s node order c newNode newOrder hne hIdentity
  exact DFunLike.congr_fun hOperator x

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
