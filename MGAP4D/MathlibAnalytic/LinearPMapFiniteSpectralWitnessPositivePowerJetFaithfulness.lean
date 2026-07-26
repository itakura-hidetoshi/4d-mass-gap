import MGAP4D.MathlibAnalytic.ContinuousLinearMapRationalFunctionalCalculusPositivePowerJetFaithfulness
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalContinuousRealResolvent
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

namespace LinearPMap

universe u

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A real resolvent acts diagonally on every non-pole eigenvector of its
self-adjoint generator. -/
theorem realResolvent_apply_eigenvector
    (A : E →ₗ.[ℝ] E)
    {mass lambda mu : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (x : A.domain)
    (hEigen : A x = mu • (x : E))
    (hmu : mu ≠ lambda) :
    A.realResolvent hSelf hlambda hgap (x : E) =
      (mu - lambda)⁻¹ • (x : E) := by
  let c : ℝ := (mu - lambda)⁻¹
  have hShift : A.realShift lambda (c • x) = (x : E) := by
    change A (c • x) - lambda • ((c • x : A.domain) : E) = (x : E)
    rw [map_smul, hEigen]
    change (c * mu) • (x : E) - (lambda * c) • (x : E) = (x : E)
    rw [← sub_smul]
    convert one_smul ℝ (x : E) using 1
    dsimp [c]
    field_simp [hmu]
  have hPreimage :
      (A.realShiftLinearEquiv hSelf hlambda hgap).symm (x : E) =
        c • x := by
    apply (A.realShiftLinearEquiv hSelf hlambda hgap).injective
    rw [LinearEquiv.apply_symm_apply]
    change (x : E) = A.realShift lambda (c • x)
    exact hShift.symm
  rw [A.realResolvent_apply, hPreimage]
  rfl

/-- Every positive power of a real resolvent acts diagonally on a generator
 eigenvector with the corresponding scalar inverse power. -/
theorem realResolvent_pow_apply_eigenvector
    (A : E →ₗ.[ℝ] E)
    {mass lambda mu : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (x : A.domain)
    (hEigen : A x = mu • (x : E))
    (hmu : mu ≠ lambda)
    (n : ℕ) :
    ((A.realResolvent hSelf hlambda hgap) ^ n) (x : E) =
      ((mu - lambda)⁻¹ ^ n) • (x : E) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      simp only [ContinuousLinearMap.mul_apply, ih, map_smul]
      rw [LinearPMap.realResolvent_apply_eigenvector
        A hSelf hlambda hgap x hEigen hmu]
      simp [pow_succ, smul_smul, mul_comm]

end LinearPMap

namespace ContinuousLinearMap

universe u

variable {α E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite spectral witnesses for one selected node-order window.  Each witness
vector diagonalizes every selected operator power, and the resulting scalar
coordinate functions are linearly independent. -/
structure PositivePowerJetCoefficientMap.FiniteSpectralWitnessData
    (A : α → E →L[ℝ] E)
    (nodes : Finset α)
    (orderCap : ℕ) where
  Witness : Type*
  [witnessFintype : Fintype Witness]
  witnessVector : Witness → E
  witnessVector_ne_zero : ∀ w, witnessVector w ≠ 0
  scalar : (nodes × Fin orderCap) → Witness → ℝ
  scalarLinearIndependent : LinearIndependent ℝ scalar
  operatorPower_apply_witness :
    ∀ (p : nodes × Fin orderCap) (w : Witness),
      positivePowerJetOperatorFamily A (p.1.1, p.2.1) (witnessVector w) =
        scalar p w • witnessVector w

attribute [instance]
  PositivePowerJetCoefficientMap.FiniteSpectralWitnessData.witnessFintype

/-- Finite scalar spectral separation implies linear independence of the
selected operator powers. -/
theorem PositivePowerJetCoefficientMap.FiniteSpectralWitnessData.linearIndependent
    {A : α → E →L[ℝ] E}
    {nodes : Finset α}
    {orderCap : ℕ}
    (D : PositivePowerJetCoefficientMap.FiniteSpectralWitnessData
      A nodes orderCap) :
    LinearIndependent ℝ
      (fun p : nodes × Fin orderCap =>
        positivePowerJetOperatorFamily A (p.1.1, p.2.1)) := by
  classical
  rw [Fintype.linearIndependent_iffₛ]
  intro left right hEquality p
  have hScalarEquality :
      (∑ q, left q • D.scalar q) =
        ∑ q, right q • D.scalar q := by
    funext w
    have hApply := congrArg
      (fun L : E →L[ℝ] E => L (D.witnessVector w)) hEquality
    simp_rw [Finset.sum_apply, Pi.smul_apply,
      D.operatorPower_apply_witness, smul_smul] at hApply
    rw [← Finset.sum_smul, ← Finset.sum_smul] at hApply
    exact smul_left_injective ℝ (D.witnessVector_ne_zero w) hApply
  exact (Fintype.linearIndependent_iffₛ.mp D.scalarLinearIndependent)
    left right hScalarEquality p

/-- If two coefficient maps fit the node-order window separated by finite
spectral witnesses, their operator family is independent on exactly the union
of their supports. -/
theorem PositivePowerJetCoefficientMap.areOperatorIndependentOnSupport_of_finiteSpectralWitness
    (A : α → E →L[ℝ] E)
    (nodes : Finset α)
    (orderCap : ℕ)
    (D : PositivePowerJetCoefficientMap.FiniteSpectralWitnessData
      A nodes orderCap)
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
  simpa [supportUnion, embed] using hRestricted

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
