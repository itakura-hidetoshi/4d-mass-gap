import MGAP4D.MathlibAnalytic.FinitePositiveWeightDobrushinRandomScanEigenvalueBound
import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathProductSum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Exchange the old and newly resampled values at one coordinate. -/
noncomputable def finitePositiveWeightSingleSiteUpdateSwapEquiv
    {ι G : Type}
    [DecidableEq ι]
    (e : ι) :
    ((ι → G) × G) ≃ ((ι → G) × G) where
  toFun := fun x => (Function.update x.1 e x.2, x.1 e)
  invFun := fun x => (Function.update x.1 e x.2, x.1 e)
  left_inv := by
    rintro ⟨A, g⟩
    apply Prod.ext
    · funext i
      by_cases hie : i = e
      · subst i
        simp
      · simp [Function.update, hie]
    · simp
  right_inv := by
    rintro ⟨A, g⟩
    apply Prod.ext
    · funext i
      by_cases hie : i = e
      · subst i
        simp
      · simp [Function.update, hie]
    · simp

/-- Restoring the old value after a one-coordinate update returns the original
configuration. -/
@[simp] theorem finitePositiveWeightSingleSiteUpdate_roundTrip
    {ι G : Type}
    [DecidableEq ι]
    (A : ι → G)
    (e : ι)
    (g : G) :
    Function.update (Function.update A e g) e (A e) = A := by
  funext i
  by_cases hie : i = e
  · subst i
    simp
  · simp [Function.update, hie]

/-- Updating the current value at the resampled coordinate does not change the
one-site partition function. -/
theorem finitePositiveWeightSingleSitePartition_update
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι)
    (g : G) :
    finitePositiveWeightSingleSitePartition weight
        (Function.update A e g) e =
      finitePositiveWeightSingleSitePartition weight A e := by
  classical
  unfold finitePositiveWeightSingleSitePartition
  apply Finset.sum_congr rfl
  intro h _hh
  congr 1
  funext i
  by_cases hie : i = e
  · subst i
    simp
  · simp [Function.update, hie]

/-- Exact detailed balance for a one-coordinate conditional resampling of an
arbitrary positive finite product weight. -/
theorem finitePositiveWeightSingleSite_detailedBalance
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι)
    (g : G) :
    weight A * finitePositiveWeightSingleSiteProbability weight A e g =
      weight (Function.update A e g) *
        finitePositiveWeightSingleSiteProbability weight
          (Function.update A e g) e (A e) := by
  unfold finitePositiveWeightSingleSiteProbability
  rw [finitePositiveWeightSingleSitePartition_update,
    finitePositiveWeightSingleSiteUpdate_roundTrip]
  ring

/-- Unnormalized weighted pairing for observables on a finite product space. -/
def finitePositiveWeightPairing
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f g : (ι → G) → ℝ) : ℝ :=
  ∑ A : ι → G, weight A * f A * g A

/-- The positive-weight pairing is symmetric. -/
theorem finitePositiveWeightPairing_symm
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f g : (ι → G) → ℝ) :
    finitePositiveWeightPairing weight f g =
      finitePositiveWeightPairing weight g f := by
  classical
  unfold finitePositiveWeightPairing
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- One-site conditional expectation is real-linear in the observable. -/
noncomputable def finitePositiveWeightSingleSiteExpectationLinearMap
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (e : ι) :
    ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ) where
  toFun := fun f A =>
    finitePositiveWeightSingleSiteExpectation weight f A e
  map_add' := by
    intro f g
    funext A
    classical
    unfold finitePositiveWeightSingleSiteExpectation
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _hh
    ring
  map_smul' := by
    intro c f
    funext A
    classical
    unfold finitePositiveWeightSingleSiteExpectation
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ g : G,
        finitePositiveWeightSingleSiteProbability weight A e g *
          (c * f (Function.update A e g))) =
          ∑ g : G,
            c *
              (finitePositiveWeightSingleSiteProbability weight A e g *
                f (Function.update A e g)) := by
            apply Finset.sum_congr rfl
            intro g _hg
            ring
      _ = c *
          ∑ g : G,
            finitePositiveWeightSingleSiteProbability weight A e g *
              f (Function.update A e g) := by
            rw [Finset.mul_sum]

@[simp] theorem finitePositiveWeightSingleSiteExpectationLinearMap_apply
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (e : ι)
    (f : (ι → G) → ℝ) :
    finitePositiveWeightSingleSiteExpectationLinearMap weight e f =
      finitePositiveWeightSingleSiteExpectation weight f · e :=
  rfl

/-- Forward weighted transition term for one exact coordinate resampling. -/
def finitePositiveWeightSingleSiteForwardTerm
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (e : ι)
    (f g : (ι → G) → ℝ)
    (x : (ι → G) × G) : ℝ :=
  weight x.1 *
    finitePositiveWeightSingleSiteProbability weight x.1 e x.2 *
    f (Function.update x.1 e x.2) * g x.1

/-- Backward weighted transition term for one exact coordinate resampling. -/
def finitePositiveWeightSingleSiteBackwardTerm
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (e : ι)
    (f g : (ι → G) → ℝ)
    (x : (ι → G) × G) : ℝ :=
  weight x.1 *
    finitePositiveWeightSingleSiteProbability weight x.1 e x.2 *
    f x.1 * g (Function.update x.1 e x.2)

/-- Pointwise detailed balance identifies a forward term with the backward
term after the involutive update exchange. -/
theorem finitePositiveWeightSingleSite_forwardTerm_eq_backwardTerm_swap
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (e : ι)
    (f g : (ι → G) → ℝ)
    (x : (ι → G) × G) :
    finitePositiveWeightSingleSiteForwardTerm weight e f g x =
      finitePositiveWeightSingleSiteBackwardTerm weight e f g
        (finitePositiveWeightSingleSiteUpdateSwapEquiv e x) := by
  rcases x with ⟨A, h⟩
  unfold finitePositiveWeightSingleSiteForwardTerm
    finitePositiveWeightSingleSiteBackwardTerm
    finitePositiveWeightSingleSiteUpdateSwapEquiv
  rw [finitePositiveWeightSingleSiteUpdate_roundTrip]
  rw [← finitePositiveWeightSingleSite_detailedBalance weight A e h]

/-- The total forward one-site transition sum equals the total backward sum. -/
theorem finitePositiveWeightSingleSite_forward_sum_eq_backward_sum
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (e : ι)
    (f g : (ι → G) → ℝ) :
    (∑ x : (ι → G) × G,
      finitePositiveWeightSingleSiteForwardTerm weight e f g x) =
      ∑ x : (ι → G) × G,
        finitePositiveWeightSingleSiteBackwardTerm weight e f g x := by
  calc
    (∑ x : (ι → G) × G,
      finitePositiveWeightSingleSiteForwardTerm weight e f g x) =
        ∑ x : (ι → G) × G,
          finitePositiveWeightSingleSiteBackwardTerm weight e f g
            (finitePositiveWeightSingleSiteUpdateSwapEquiv e x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact finitePositiveWeightSingleSite_forwardTerm_eq_backwardTerm_swap
        weight e f g x
    _ = ∑ x : (ι → G) × G,
        finitePositiveWeightSingleSiteBackwardTerm weight e f g x :=
      finite_sum_comp_equiv
        (finitePositiveWeightSingleSiteUpdateSwapEquiv e)
        (finitePositiveWeightSingleSiteBackwardTerm weight e f g)

/-- The forward transition sum is the weighted pairing with the one-site
conditional expectation in the first slot. -/
theorem finitePositiveWeightSingleSite_forward_sum_eq_pairing
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (e : ι)
    (f g : (ι → G) → ℝ) :
    (∑ x : (ι → G) × G,
      finitePositiveWeightSingleSiteForwardTerm weight e f g x) =
      finitePositiveWeightPairing weight
        (finitePositiveWeightSingleSiteExpectation weight f · e) g := by
  classical
  rw [Fintype.sum_prod_type]
  unfold finitePositiveWeightSingleSiteForwardTerm
    finitePositiveWeightPairing
    finitePositiveWeightSingleSiteExpectation
  apply Finset.sum_congr rfl
  intro A _hA
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _hh
  ring

/-- The backward transition sum is the weighted pairing with the one-site
conditional expectation in the second slot. -/
theorem finitePositiveWeightSingleSite_backward_sum_eq_pairing
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (e : ι)
    (f g : (ι → G) → ℝ) :
    (∑ x : (ι → G) × G,
      finitePositiveWeightSingleSiteBackwardTerm weight e f g x) =
      finitePositiveWeightPairing weight f
        (finitePositiveWeightSingleSiteExpectation weight g · e) := by
  classical
  rw [Fintype.sum_prod_type]
  unfold finitePositiveWeightSingleSiteBackwardTerm
    finitePositiveWeightPairing
    finitePositiveWeightSingleSiteExpectation
  apply Finset.sum_congr rfl
  intro A _hA
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _hh
  ring

/-- Exact one-site conditional expectation is symmetric for the unnormalized
positive-weight pairing. -/
theorem finitePositiveWeightSingleSiteExpectation_pairing_symm
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (e : ι)
    (f g : (ι → G) → ℝ) :
    finitePositiveWeightPairing weight
        (finitePositiveWeightSingleSiteExpectation weight f · e) g =
      finitePositiveWeightPairing weight f
        (finitePositiveWeightSingleSiteExpectation weight g · e) := by
  calc
    finitePositiveWeightPairing weight
        (finitePositiveWeightSingleSiteExpectation weight f · e) g =
      ∑ x : (ι → G) × G,
        finitePositiveWeightSingleSiteForwardTerm weight e f g x :=
      (finitePositiveWeightSingleSite_forward_sum_eq_pairing
        weight e f g).symm
    _ = ∑ x : (ι → G) × G,
        finitePositiveWeightSingleSiteBackwardTerm weight e f g x :=
      finitePositiveWeightSingleSite_forward_sum_eq_backward_sum
        weight e f g
    _ = finitePositiveWeightPairing weight f
        (finitePositiveWeightSingleSiteExpectation weight g · e) :=
      finitePositiveWeightSingleSite_backward_sum_eq_pairing
        weight e f g

/-- Uniform random-scan conditional expectation is real-linear. -/
noncomputable def finitePositiveWeightRandomScanLinearMap
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ) :
    ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ) where
  toFun := finitePositiveWeightRandomScanConditionalExpectation weight
  map_add' := by
    intro f g
    funext A
    classical
    unfold finitePositiveWeightRandomScanConditionalExpectation
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib, mul_add]
    apply congrArg
    apply Finset.sum_congr rfl
    intro e _he
    unfold finitePositiveWeightSingleSiteExpectation
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _hh
    ring
  map_smul' := by
    intro c f
    funext A
    classical
    unfold finitePositiveWeightRandomScanConditionalExpectation
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (Fintype.card ι : ℝ)⁻¹ *
          ∑ e : ι,
            finitePositiveWeightSingleSiteExpectation weight (c • f) A e =
        (Fintype.card ι : ℝ)⁻¹ *
          ∑ e : ι,
            c * finitePositiveWeightSingleSiteExpectation weight f A e := by
          apply congrArg
          apply Finset.sum_congr rfl
          intro e _he
          unfold finitePositiveWeightSingleSiteExpectation
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [← Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro h _hh
          ring
      _ = c *
          ((Fintype.card ι : ℝ)⁻¹ *
            ∑ e : ι,
              finitePositiveWeightSingleSiteExpectation weight f A e) := by
          ring

@[simp] theorem finitePositiveWeightRandomScanLinearMap_apply
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ) :
    finitePositiveWeightRandomScanLinearMap weight f =
      finitePositiveWeightRandomScanConditionalExpectation weight f :=
  rfl

/-- Uniform random scan is symmetric for the unnormalized positive-weight
pairing. -/
theorem finitePositiveWeightRandomScan_pairing_symm
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f g : (ι → G) → ℝ) :
    finitePositiveWeightPairing weight
        (finitePositiveWeightRandomScanConditionalExpectation weight f) g =
      finitePositiveWeightPairing weight f
        (finitePositiveWeightRandomScanConditionalExpectation weight g) := by
  classical
  unfold finitePositiveWeightRandomScanConditionalExpectation
    finitePositiveWeightPairing
  calc
    (∑ A : ι → G,
      weight A *
        ((Fintype.card ι : ℝ)⁻¹ *
          ∑ e : ι,
            finitePositiveWeightSingleSiteExpectation weight f A e) *
        g A) =
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ e : ι,
          finitePositiveWeightPairing weight
            (finitePositiveWeightSingleSiteExpectation weight f · e) g := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A _hA
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _he
      ring
    _ = (Fintype.card ι : ℝ)⁻¹ *
        ∑ e : ι,
          finitePositiveWeightPairing weight f
            (finitePositiveWeightSingleSiteExpectation weight g · e) := by
      apply congrArg
      apply Finset.sum_congr rfl
      intro e _he
      exact finitePositiveWeightSingleSiteExpectation_pairing_symm
        weight e f g
    _ = ∑ A : ι → G,
      weight A * f A *
        ((Fintype.card ι : ℝ)⁻¹ *
          ∑ e : ι,
            finitePositiveWeightSingleSiteExpectation weight g A e) := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A _hA
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _he
      ring

end

end MathlibAnalytic
end MGAP4D
