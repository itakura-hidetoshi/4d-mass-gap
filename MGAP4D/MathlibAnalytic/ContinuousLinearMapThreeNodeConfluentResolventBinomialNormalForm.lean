import MGAP4D.MathlibAnalytic.ContinuousLinearMapTwoSidedConfluentResolventBinomialNormalForm
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

variable {α E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Three consecutive repeated blocks evaluate to the corresponding ordered
product of powers. -/
@[simp] theorem orderedProduct_three_replicate_blocks
    (A : α → E →L[ℝ] E)
    (a b c : α)
    (m n p : ℕ) :
    orderedProduct A
        (List.replicate m a ++ List.replicate n b ++ List.replicate p c) =
      ((A a) ^ m * (A b) ^ n) * (A c) ^ p := by
  simp [orderedProduct_append, mul_assoc]

/-- Iterated closed binomial normal form for positive multiplicities at three
pairwise-distinct resolvent nodes.  First the `lambda`/`mu` product is expanded;
each resulting pure power is then expanded against the `nu` block. -/
noncomputable def threeNodeConfluentResolventBinomialNormalForm
    (Rlambda Rmu Rnu : E →L[ℝ] E)
    (lambda mu nu : ℝ)
    (m n p : ℕ) : E →L[ℝ] E :=
  (Finset.range (m + 1)).sum (fun k =>
      twoSidedConfluentLeftBinomialCoefficient
          (lambda - mu)⁻¹ m n k •
        twoSidedConfluentResolventBinomialNormalForm
          Rlambda Rnu (lambda - nu)⁻¹ k p) +
    (Finset.range (n + 1)).sum (fun k =>
      twoSidedConfluentRightBinomialCoefficient
          (lambda - mu)⁻¹ m n k •
        twoSidedConfluentResolventBinomialNormalForm
          Rmu Rnu (mu - nu)⁻¹ k p)

/-- Under the three pairwise resolvent identities, the positive three-block
mixed product is exactly the iterated three-node binomial normal form. -/
theorem pow_succ_mul_pow_succ_mul_pow_succ_eq_threeNodeConfluentResolventBinomialNormalForm
    (Rlambda Rmu Rnu : E →L[ℝ] E)
    (lambda mu nu : ℝ)
    (hneLambdaMu : lambda ≠ mu)
    (hneLambdaNu : lambda ≠ nu)
    (hneMuNu : mu ≠ nu)
    (hLambdaMu :
      Rlambda - Rmu =
        (lambda - mu) • (Rlambda * Rmu))
    (hLambdaNu :
      Rlambda - Rnu =
        (lambda - nu) • (Rlambda * Rnu))
    (hMuNu :
      Rmu - Rnu =
        (mu - nu) • (Rmu * Rnu))
    (m n p : ℕ) :
    (Rlambda ^ (m + 1) * Rmu ^ (n + 1)) * Rnu ^ (p + 1) =
      threeNodeConfluentResolventBinomialNormalForm
        Rlambda Rmu Rnu lambda mu nu m n p := by
  rw [pow_succ_mul_pow_succ_eq_twoSidedConfluentResolventBinomialNormalForm
    Rlambda Rmu lambda mu hneLambdaMu hLambdaMu m n]
  simp only [twoSidedConfluentResolventBinomialNormalForm,
    twoSidedConfluentLeftBinomialSum,
    twoSidedConfluentRightBinomialSum,
    threeNodeConfluentResolventBinomialNormalForm]
  rw [add_mul, Finset.sum_mul, Finset.sum_mul]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro k hk
    rw [smul_mul_assoc]
    rw [pow_succ_mul_pow_succ_eq_twoSidedConfluentResolventBinomialNormalForm
      Rlambda Rnu lambda nu hneLambdaNu hLambdaNu k p]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [smul_mul_assoc]
    rw [pow_succ_mul_pow_succ_eq_twoSidedConfluentResolventBinomialNormalForm
      Rmu Rnu mu nu hneMuNu hMuNu k p]

/-- Pointwise three-node closed confluent partial-fraction expansion. -/
theorem pow_succ_apply_pow_succ_apply_pow_succ_eq_threeNodeConfluentResolventBinomialNormalForm_apply
    (Rlambda Rmu Rnu : E →L[ℝ] E)
    (lambda mu nu : ℝ)
    (hneLambdaMu : lambda ≠ mu)
    (hneLambdaNu : lambda ≠ nu)
    (hneMuNu : mu ≠ nu)
    (hLambdaMu :
      Rlambda - Rmu =
        (lambda - mu) • (Rlambda * Rmu))
    (hLambdaNu :
      Rlambda - Rnu =
        (lambda - nu) • (Rlambda * Rnu))
    (hMuNu :
      Rmu - Rnu =
        (mu - nu) • (Rmu * Rnu))
    (m n p : ℕ)
    (x : E) :
    (Rlambda ^ (m + 1))
        ((Rmu ^ (n + 1)) ((Rnu ^ (p + 1)) x)) =
      threeNodeConfluentResolventBinomialNormalForm
        Rlambda Rmu Rnu lambda mu nu m n p x := by
  have hOperator :=
    pow_succ_mul_pow_succ_mul_pow_succ_eq_threeNodeConfluentResolventBinomialNormalForm
      Rlambda Rmu Rnu lambda mu nu
      hneLambdaMu hneLambdaNu hneMuNu
      hLambdaMu hLambdaNu hMuNu m n p
  exact DFunLike.congr_fun hOperator x

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
