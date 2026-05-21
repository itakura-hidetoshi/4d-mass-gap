import MGAP4D.MathlibAnalytic.R2MPrefixQuotientAddOperation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Negation on the finite-prefix zero-distance quotient, induced by scalar
multiplication by `-1`. -/
def r2mPrefixQuotientNeg
    (N : ℕ) : R2MPrefixZeroDistanceQuotient N →
      R2MPrefixZeroDistanceQuotient N :=
  r2mPrefixQuotientSmul N (-1 : ℝ)

/-- Evaluation of quotient negation on a representative. -/
theorem r2m_prefix_quotient_neg_mk
    (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    r2mPrefixQuotientNeg N
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N) x) =
      Quotient.mk (r2mPrefixZeroDistanceSetoid N)
        (concreteL2GraphPairPrefixEnergyBoundedNeg x) := by
  unfold r2mPrefixQuotientNeg
  exact r2m_prefix_quotient_smul_mk N (-1 : ℝ) x

/-- Left zero law for quotient addition. -/
theorem r2m_prefix_quotient_zero_add
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientAdd N (r2mPrefixQuotientZeroClass N) q = q := by
  refine Quotient.inductionOn' q ?_
  intro x
  unfold r2mPrefixQuotientZeroClass
  rw [r2m_prefix_quotient_add_mk]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_zero_add_eq]

/-- Right zero law for quotient addition. -/
theorem r2m_prefix_quotient_add_zero
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientAdd N q (r2mPrefixQuotientZeroClass N) = q := by
  refine Quotient.inductionOn' q ?_
  intro x
  unfold r2mPrefixQuotientZeroClass
  rw [r2m_prefix_quotient_add_mk]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_add_comm x
    concreteL2GraphPairPrefixEnergyBoundedZero]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_zero_add_eq]

/-- Commutativity of quotient addition. -/
theorem r2m_prefix_quotient_add_comm
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientAdd N q r = r2mPrefixQuotientAdd N r q := by
  refine Quotient.inductionOn' q ?_
  intro x
  refine Quotient.inductionOn' r ?_
  intro y
  rw [r2m_prefix_quotient_add_mk]
  rw [r2m_prefix_quotient_add_mk]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_add_comm x y]

/-- Associativity of quotient addition. -/
theorem r2m_prefix_quotient_add_assoc
    (N : ℕ) (q r s : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientAdd N (r2mPrefixQuotientAdd N q r) s =
      r2mPrefixQuotientAdd N q (r2mPrefixQuotientAdd N r s) := by
  refine Quotient.inductionOn' q ?_
  intro x
  refine Quotient.inductionOn' r ?_
  intro y
  refine Quotient.inductionOn' s ?_
  intro z
  rw [r2m_prefix_quotient_add_mk]
  rw [r2m_prefix_quotient_add_mk]
  rw [r2m_prefix_quotient_add_mk]
  rw [r2m_prefix_quotient_add_mk]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_add_assoc]

/-- Additive inverse law for quotient negation. -/
theorem r2m_prefix_quotient_add_neg
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientAdd N q (r2mPrefixQuotientNeg N q) =
      r2mPrefixQuotientZeroClass N := by
  refine Quotient.inductionOn' q ?_
  intro x
  unfold r2mPrefixQuotientNeg
  unfold r2mPrefixQuotientZeroClass
  rw [r2m_prefix_quotient_smul_mk]
  rw [r2m_prefix_quotient_add_mk]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_add_neg_eq_zero]

/-- Quotient additive-law readiness package. -/
def r2mPrefixQuotientAddLawsReady : Prop :=
  r2mPrefixQuotientAddOperationReady ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientAdd N (r2mPrefixQuotientZeroClass N) q = q) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientAdd N q (r2mPrefixQuotientZeroClass N) = q) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientAdd N q r = r2mPrefixQuotientAdd N r q) ∧
  (∀ (N : ℕ) (q r s : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientAdd N (r2mPrefixQuotientAdd N q r) s =
      r2mPrefixQuotientAdd N q (r2mPrefixQuotientAdd N r s)) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientAdd N q (r2mPrefixQuotientNeg N q) =
      r2mPrefixQuotientZeroClass N)

/-- Quotient addition laws are ready. -/
theorem r2m_prefix_quotient_add_laws_ready :
    r2mPrefixQuotientAddLawsReady := by
  exact ⟨
    r2m_prefix_quotient_add_operation_ready,
    r2m_prefix_quotient_zero_add,
    r2m_prefix_quotient_add_zero,
    r2m_prefix_quotient_add_comm,
    r2m_prefix_quotient_add_assoc,
    r2m_prefix_quotient_add_neg⟩

end

end MathlibAnalytic
end MGAP4D
