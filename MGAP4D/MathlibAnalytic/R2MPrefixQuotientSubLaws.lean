import MGAP4D.MathlibAnalytic.R2MPrefixQuotientAddLaws

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Subtraction on the finite-prefix zero-distance quotient, defined as addition
with quotient negation. -/
def r2mPrefixQuotientSub
    (N : ℕ) :
    R2MPrefixZeroDistanceQuotient N →
      R2MPrefixZeroDistanceQuotient N →
        R2MPrefixZeroDistanceQuotient N :=
  fun q r => r2mPrefixQuotientAdd N q (r2mPrefixQuotientNeg N r)

/-- Left additive inverse law for quotient negation. -/
theorem r2m_prefix_quotient_neg_add
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientAdd N (r2mPrefixQuotientNeg N q) q =
      r2mPrefixQuotientZeroClass N := by
  rw [r2m_prefix_quotient_add_comm]
  exact r2m_prefix_quotient_add_neg N q

/-- Evaluation of quotient subtraction on representatives. -/
theorem r2m_prefix_quotient_sub_mk
    (N : ℕ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    r2mPrefixQuotientSub N
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N) x)
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N) y) =
      Quotient.mk (r2mPrefixZeroDistanceSetoid N)
        (concreteL2GraphPairPrefixEnergyBoundedSub x y) := by
  unfold r2mPrefixQuotientSub
  unfold r2mPrefixQuotientNeg
  unfold concreteL2GraphPairPrefixEnergyBoundedSub
  unfold concreteL2GraphPairPrefixEnergyBoundedNeg
  rw [r2m_prefix_quotient_smul_mk]
  rw [r2m_prefix_quotient_add_mk]

/-- Subtracting the quotient zero class is the identity. -/
theorem r2m_prefix_quotient_sub_zero
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSub N q (r2mPrefixQuotientZeroClass N) = q := by
  unfold r2mPrefixQuotientSub
  have hneg0 : r2mPrefixQuotientNeg N (r2mPrefixQuotientZeroClass N) =
      r2mPrefixQuotientZeroClass N := by
    unfold r2mPrefixQuotientNeg
    exact r2m_prefix_quotient_smul_zero_class_closed N (-1 : ℝ)
  rw [hneg0]
  exact r2m_prefix_quotient_add_zero N q

/-- Subtracting a quotient point from itself gives the zero class. -/
theorem r2m_prefix_quotient_sub_self
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSub N q q = r2mPrefixQuotientZeroClass N := by
  unfold r2mPrefixQuotientSub
  exact r2m_prefix_quotient_add_neg N q

/-- Quotient subtraction-law readiness package. -/
def r2mPrefixQuotientSubLawsReady : Prop :=
  r2mPrefixQuotientAddLawsReady ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientAdd N (r2mPrefixQuotientNeg N q) q =
      r2mPrefixQuotientZeroClass N) ∧
  (∀ (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    r2mPrefixQuotientSub N
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N) x)
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N) y) =
      Quotient.mk (r2mPrefixZeroDistanceSetoid N)
        (concreteL2GraphPairPrefixEnergyBoundedSub x y)) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSub N q (r2mPrefixQuotientZeroClass N) = q) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSub N q q = r2mPrefixQuotientZeroClass N)

/-- Quotient subtraction laws are ready. -/
theorem r2m_prefix_quotient_sub_laws_ready :
    r2mPrefixQuotientSubLawsReady := by
  exact ⟨
    r2m_prefix_quotient_add_laws_ready,
    r2m_prefix_quotient_neg_add,
    r2m_prefix_quotient_sub_mk,
    r2m_prefix_quotient_sub_zero,
    r2m_prefix_quotient_sub_self⟩

end

end MathlibAnalytic
end MGAP4D
