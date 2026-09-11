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

/-- The positive-weight pairing is linear in its first observable. -/
noncomputable def finitePositiveWeightPairingLeftLinearMap
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (g : (ι → G) → ℝ) :
    ((ι → G) → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun f => finitePositiveWeightPairing weight f g
  map_add' := by
    intro f h
    classical
    unfold finitePositiveWeightPairing
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro A _hA
    ring
  map_smul' := by
    intro c f
    classical
    unfold finitePositiveWeightPairing
    simp only [Pi.smul_apply, smul_eq_mul]
    change
      (∑ A : ι → G, weight A * (c * f A) * g A) =
        c * ∑ A : ι → G, weight A * f A * g A
    calc
      (∑ A : ι → G, weight A * (c * f A) * g A) =
          ∑ A : ι → G, c * (weight A * f A * g A) := by
        apply Finset.sum_congr rfl
        intro A _hA
        ring
      _ = c * ∑ A : ι → G, weight A * f A * g A := by
        rw [Finset.mul_sum]

@[simp] theorem finitePositiveWeightPairingLeftLinearMap_apply
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (g f : (ι → G) → ℝ) :
    finitePositiveWeightPairingLeftLinearMap weight g f =
      finitePositiveWeightPairing weight f g :=
  rfl

/-- The positive-weight pairing is linear in its second observable. -/
noncomputable def finitePositiveWeightPairingRightLinearMap
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ) :
    ((ι → G) → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun g => finitePositiveWeightPairing weight f g
  map_add' := by
    intro g h
    classical
    unfold finitePositiveWeightPairing
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro A _hA
    ring
  map_smul' := by
    intro c g
    classical
    unfold finitePositiveWeightPairing
    simp only [Pi.smul_apply, smul_eq_mul]
    change
      (∑ A : ι → G, weight A * f A * (c * g A)) =
        c * ∑ A : ι → G, weight A * f A * g A
    calc
      (∑ A : ι → G, weight A * f A * (c * g A)) =
          ∑ A : ι → G, c * (weight A * f A * g A) := by
        apply Finset.sum_congr rfl
        intro A _hA
        ring
      _ = c * ∑ A : ι → G, weight A * f A * g A := by
        rw [Finset.mul_sum]

@[simp] theorem finitePositiveWeightPairingRightLinearMap_apply
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f g : (ι → G) → ℝ) :
    finitePositiveWeightPairingRightLinearMap weight f g =
      finitePositiveWeightPairing weight f g :=
  rfl

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
      (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) :=
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
  change
    weight A * finitePositiveWeightSingleSiteProbability weight A e h *
        f (Function.update A e h) * g A =
      weight (Function.update A e h) *
        finitePositiveWeightSingleSiteProbability weight
          (Function.update A e h) e (A e) *
        f (Function.update A e h) *
        g (Function.update (Function.update A e h) e (A e))
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
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) g := by
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
        (fun A => finitePositiveWeightSingleSiteExpectation weight g A e) := by
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
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) g =
      finitePositiveWeightPairing weight f
        (fun A => finitePositiveWeightSingleSiteExpectation weight g A e) := by
  calc
    finitePositiveWeightPairing weight
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) g =
      ∑ x : (ι → G) × G,
        finitePositiveWeightSingleSiteForwardTerm weight e f g x :=
      (finitePositiveWeightSingleSite_forward_sum_eq_pairing
        weight e f g).symm
    _ = ∑ x : (ι → G) × G,
        finitePositiveWeightSingleSiteBackwardTerm weight e f g x :=
      finitePositiveWeightSingleSite_forward_sum_eq_backward_sum
        weight e f g
    _ = finitePositiveWeightPairing weight f
        (fun A => finitePositiveWeightSingleSiteExpectation weight g A e) :=
      finitePositiveWeightSingleSite_backward_sum_eq_pairing
        weight e f g

/-- Uniform random-scan conditional expectation is the normalized finite sum
of the exact one-site conditional-expectation linear maps. -/
noncomputable def finitePositiveWeightRandomScanLinearMap
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ) :
    ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ) :=
  (Fintype.card ι : ℝ)⁻¹ •
    ∑ e : ι, finitePositiveWeightSingleSiteExpectationLinearMap weight e

@[simp] theorem finitePositiveWeightRandomScanLinearMap_apply
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ) :
    finitePositiveWeightRandomScanLinearMap weight f =
      finitePositiveWeightRandomScanConditionalExpectation weight f := by
  ext A
  simp [finitePositiveWeightRandomScanLinearMap,
    finitePositiveWeightRandomScanConditionalExpectation]

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
  let leftPair := finitePositiveWeightPairingLeftLinearMap weight g
  let rightPair := finitePositiveWeightPairingRightLinearMap weight f
  calc
    finitePositiveWeightPairing weight
        (finitePositiveWeightRandomScanConditionalExpectation weight f) g =
      leftPair (finitePositiveWeightRandomScanLinearMap weight f) := by
        rw [finitePositiveWeightRandomScanLinearMap_apply]
        rfl
    _ = (Fintype.card ι : ℝ)⁻¹ *
        ∑ e : ι,
          finitePositiveWeightPairing weight
            (finitePositiveWeightSingleSiteExpectationLinearMap weight e f) g := by
      simp [leftPair, finitePositiveWeightRandomScanLinearMap]
    _ = (Fintype.card ι : ℝ)⁻¹ *
        ∑ e : ι,
          finitePositiveWeightPairing weight f
            (finitePositiveWeightSingleSiteExpectationLinearMap weight e g) := by
      apply congrArg
      apply Finset.sum_congr rfl
      intro e _he
      exact finitePositiveWeightSingleSiteExpectation_pairing_symm
        weight e f g
    _ = rightPair (finitePositiveWeightRandomScanLinearMap weight g) := by
      simp [rightPair, finitePositiveWeightRandomScanLinearMap]
    _ = finitePositiveWeightPairing weight f
        (finitePositiveWeightRandomScanConditionalExpectation weight g) := by
      rw [finitePositiveWeightRandomScanLinearMap_apply]
      rfl

end

end MathlibAnalytic
end MGAP4D
