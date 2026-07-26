import MGAP4D.MathlibAnalytic.ContinuousLinearMapPositivePowerJetCoefficientSemanticUniqueness
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set
open scoped Polynomial

namespace ContinuousLinearMap

universe u v

variable {α : Type u}
variable {M : Type v} [AddCommGroup M] [Module ℝ M]

/-- The monic linear denominator associated with the shifted resolvent
`(x + shift)⁻¹`. -/
def shiftedLinearPolynomial (shift : ℝ) : Polynomial ℝ :=
  Polynomial.X + Polynomial.C shift

@[simp] theorem shiftedLinearPolynomial_monic (shift : ℝ) :
    (shiftedLinearPolynomial shift).Monic := by
  exact Polynomial.monic_X_add_C shift

/-- Distinct real shifts give coprime monic linear denominator polynomials. -/
theorem shiftedLinearPolynomial_isCoprime
    {left right : ℝ}
    (hne : left ≠ right) :
    IsCoprime (shiftedLinearPolynomial left)
      (shiftedLinearPolynomial right) := by
  let delta : ℝ := left - right
  have hdelta : delta ≠ 0 := sub_ne_zero.mpr hne
  refine ⟨Polynomial.C delta⁻¹, Polynomial.C (-delta⁻¹), ?_⟩
  change
    Polynomial.C delta⁻¹ * (Polynomial.X + Polynomial.C left) +
        Polynomial.C (-delta⁻¹) *
          (Polynomial.X + Polynomial.C right) = 1
  rw [Polynomial.C_neg]
  calc
    Polynomial.C delta⁻¹ * (Polynomial.X + Polynomial.C left) +
        -Polynomial.C delta⁻¹ *
          (Polynomial.X + Polynomial.C right) =
      Polynomial.C delta⁻¹ *
        (Polynomial.C left - Polynomial.C right) := by ring
    _ = Polynomial.C delta⁻¹ * Polynomial.C delta := by
      rw [← Polynomial.C_sub]
      rfl
    _ = Polynomial.C (delta⁻¹ * delta) := by
      rw [Polynomial.C_mul]
    _ = 1 := by simp [hdelta]

/-- The rational function carrying one positive shifted-resolvent power. -/
noncomputable def shiftedInversePowerRatFunc
    (shift : ℝ)
    (order : ℕ) : RatFunc ℝ :=
  (algebraMap (Polynomial ℝ) (RatFunc ℝ)
      (shiftedLinearPolynomial shift))⁻¹ ^ (order + 1)

/-- Coefficients of finitely many distinct shifted inverse powers are unique.
The proof is the pinned Mathlib partial-fraction uniqueness theorem with
linear monic denominators and constant remainders. -/
theorem shiftedInversePowerRatFunc_coefficients_unique
    {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    (orderCap : ℕ)
    (hValueInjective : Function.Injective value)
    (left right : ι → Fin orderCap → ℝ)
    (hEquality :
      (∑ i, ∑ j,
        left i j • shiftedInversePowerRatFunc (value i) j.1) =
      ∑ i, ∑ j,
        right i j • shiftedInversePowerRatFunc (value i) j.1) :
    left = right := by
  classical
  let denominator : ι → Polynomial ℝ := fun i =>
    shiftedLinearPolynomial (value i)
  let denominatorInv : ι → RatFunc ℝ := fun i =>
    (algebraMap (Polynomial ℝ) (RatFunc ℝ) (denominator i))⁻¹
  let leftRemainder : (i : ι) → Fin orderCap → Polynomial ℝ :=
    fun i j => Polynomial.C (left i j)
  let rightRemainder : (i : ι) → Fin orderCap → Polynomial ℝ :=
    fun i j => Polynomial.C (right i j)
  have hMonic : ∀ i ∈ (Finset.univ : Finset ι),
      (denominator i).Monic := by
    intro i _
    exact shiftedLinearPolynomial_monic (value i)
  have hCoprime : Set.Pairwise (Finset.univ : Finset ι)
      (fun i j => IsCoprime (denominator i) (denominator j)) := by
    intro i _ j _ hij
    exact shiftedLinearPolynomial_isCoprime
      (fun hvalue => hij (hValueInjective hvalue))
  have hInverse : ∀ i ∈ (Finset.univ : Finset ι),
      denominatorInv i *
          algebraMap (Polynomial ℝ) (RatFunc ℝ) (denominator i) = 1 := by
    intro i _
    apply inv_mul_cancel₀
    apply map_ne_zero_of_injective
      (FaithfulSMul.algebraMap_injective
        (Polynomial ℝ) (RatFunc ℝ))
    exact (hMonic i (Finset.mem_univ i)).ne_zero
  have hLeftDegree : ∀ i ∈ (Finset.univ : Finset ι),
      ∀ j, (leftRemainder i j).degree < (denominator i).degree := by
    intro i _ j
    simp [leftRemainder, denominator, shiftedLinearPolynomial]
  have hRightDegree : ∀ i ∈ (Finset.univ : Finset ι),
      ∀ j, (rightRemainder i j).degree < (denominator i).degree := by
    intro i _ j
    simp [rightRemainder, denominator, shiftedLinearPolynomial]
  have hPartialFractionEquality :
      algebraMap (Polynomial ℝ) (RatFunc ℝ) 0 +
          ∑ i ∈ (Finset.univ : Finset ι), ∑ j,
            algebraMap (Polynomial ℝ) (RatFunc ℝ)
                (leftRemainder i j) *
              denominatorInv i ^ (j.1 + 1) =
        algebraMap (Polynomial ℝ) (RatFunc ℝ) 0 +
          ∑ i ∈ (Finset.univ : Finset ι), ∑ j,
            algebraMap (Polynomial ℝ) (RatFunc ℝ)
                (rightRemainder i j) *
              denominatorInv i ^ (j.1 + 1) := by
    simpa [leftRemainder, rightRemainder, denominatorInv,
      denominator, shiftedInversePowerRatFunc, Algebra.smul_def] using
      hEquality
  have hUnique :=
    Polynomial.quo_add_sum_rem_mul_pow_inverse_unique
      (R := ℝ) (K := RatFunc ℝ)
      (s := (Finset.univ : Finset ι))
      (g := denominator)
      (n := fun _ => orderCap)
      (gi := denominatorInv)
      (q₁ := 0) (q₂ := 0)
      (r₁ := leftRemainder) (r₂ := rightRemainder)
      hMonic hCoprime hInverse hLeftDegree hRightDegree
      hPartialFractionEquality
  funext i j
  have hCoefficient := congrFun
    (hUnique.2 i (Finset.mem_univ i)) j
  exact Polynomial.C_injective (by
    simpa [leftRemainder, rightRemainder] using hCoefficient)

/-- For finitely many distinct shifts and a common positive-power cap, all
shifted inverse powers are linearly independent as rational functions. -/
theorem shiftedInversePowerRatFunc_linearIndependent
    {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    (orderCap : ℕ)
    (hValueInjective : Function.Injective value) :
    LinearIndependent ℝ
      (fun p : ι × Fin orderCap =>
        shiftedInversePowerRatFunc (value p.1) p.2.1) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro left right hEquality p
  have hCoefficients := shiftedInversePowerRatFunc_coefficients_unique
    value orderCap hValueInjective
    (fun i j => left (i, j))
    (fun i j => right (i, j))
    (by simpa [Fintype.sum_prod_type] using hEquality)
  exact congrFun (congrFun hCoefficients p.1) p.2

/-- An injective real-linear rational functional calculus realizing a finite
family of shifted inverse powers inside a target module. -/
structure FiniteShiftedInversePowerLinearRealization
    (family : α → ℕ → M)
    (value : α → ℝ)
    (nodes : Finset α)
    (orderCap : ℕ) where
  valueInjectiveOnNodes : Set.InjOn value nodes
  calculus : RatFunc ℝ →ₗ[ℝ] M
  calculusInjective : Function.Injective calculus
  map_shiftedInversePower : ∀ (a : nodes) (j : Fin orderCap),
    calculus (shiftedInversePowerRatFunc (value a.1) j.1) =
      family a.1 j.1

/-- A faithful finite rational functional calculus transports the scalar
partial-fraction linear independence to its realized target family. -/
theorem FiniteShiftedInversePowerLinearRealization.linearIndependent
    {family : α → ℕ → M}
    {value : α → ℝ}
    {nodes : Finset α}
    {orderCap : ℕ}
    (D : FiniteShiftedInversePowerLinearRealization
      family value nodes orderCap) :
    LinearIndependent ℝ
      (fun p : nodes × Fin orderCap => family p.1.1 p.2.1) := by
  have hValueInjective : Function.Injective
      (fun a : nodes => value a.1) := by
    intro left right hvalue
    exact Subtype.ext
      (D.valueInjectiveOnNodes left.2 right.2 hvalue)
  have hRational := shiftedInversePowerRatFunc_linearIndependent
    (fun a : nodes => value a.1) orderCap hValueInjective
  have hMapped := hRational.map_injOn D.calculus
    D.calculusInjective.injOn
  simpa [Function.comp_def, D.map_shiftedInversePower] using hMapped

/-- A finite rational functional calculus specialized to the positive-power
operator family associated with one node-indexed operator family. -/
abbrev PositivePowerJetCoefficientMap.FiniteRationalFunctionalCalculusData
    {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (nodes : Finset α)
    (orderCap : ℕ) :=
  FiniteShiftedInversePowerLinearRealization
    (fun a order => positivePowerJetOperatorFamily A (a, order))
    value nodes orderCap

/-- If two finite coefficient maps are supported inside the node and order
window of a faithful rational functional calculus, their operator family is
linearly independent on exactly the union of those supports. -/
theorem PositivePowerJetCoefficientMap.areOperatorIndependentOnSupport_of_finiteRationalFunctionalCalculus
    {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (nodes : Finset α)
    (orderCap : ℕ)
    (D : PositivePowerJetCoefficientMap.FiniteRationalFunctionalCalculusData
      A value nodes orderCap)
    (left right : PositivePowerJetCoefficientMap α)
    (hNodes : ∀ p,
      p ∈ ((↑left.support : Set (α × ℕ)) ∪ ↑right.support) →
        p.1 ∈ nodes)
    (hOrders : ∀ p,
      p ∈ ((↑left.support : Set (α × ℕ)) ∪ ↑right.support) →
        p.2 < orderCap) :
    left.AreOperatorIndependentOnSupport right A := by
  let supportUnion : Set (α × ℕ) :=
    (↑left.support : Set (α × ℕ)) ∪ ↑right.support
  let embed : supportUnion → nodes × Fin orderCap := fun p =>
    (⟨p.1.1, hNodes p.1 p.2⟩,
      ⟨p.1.2, hOrders p.1 p.2⟩)
  have hEmbed : Function.Injective embed := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z : nodes × Fin orderCap => z.1.1) hpq
    · exact congrArg (fun z : nodes × Fin orderCap => z.2.1) hpq
  have hRestricted := D.linearIndependent.comp embed hEmbed
  unfold PositivePowerJetCoefficientMap.AreOperatorIndependentOnSupport
  unfold LinearIndepOn
  simpa [supportUnion, embed,
    PositivePowerJetCoefficientMap.FiniteRationalFunctionalCalculusData] using
    hRestricted

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
