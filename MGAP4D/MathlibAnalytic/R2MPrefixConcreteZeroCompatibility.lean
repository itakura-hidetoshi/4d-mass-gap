import MGAP4D.MathlibAnalytic.R2MPrefixQuotientSmulOperation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Concrete scalar multiplication sends the `l2` zero sequence to zero. -/
theorem concrete_l2_real_smul_zero_eq
    (c : ℝ) :
    concreteL2RealSmul c concreteL2RealZero = concreteL2RealZero := by
  apply Subtype.ext
  funext n
  simp [concreteL2RealSmul, concreteL2RealZero]

/-- Concrete graph-pair scalar multiplication sends the zero pair to zero. -/
theorem concrete_l2_graph_pair_smul_zero_eq
    (c : ℝ) :
    concreteL2GraphPairSmul c concreteL2GraphPairZero = concreteL2GraphPairZero := by
  apply Prod.ext
  · exact concrete_l2_real_smul_zero_eq c
  · exact concrete_l2_real_smul_zero_eq c

/-- Bounded-prefix scalar multiplication sends the bounded zero element to zero. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_smul_zero_eq
    (c : ℝ) :
    concreteL2GraphPairPrefixEnergyBoundedSmul c
        concreteL2GraphPairPrefixEnergyBoundedZero =
      concreteL2GraphPairPrefixEnergyBoundedZero := by
  apply Subtype.ext
  exact concrete_l2_graph_pair_smul_zero_eq c

/-- Bounded-prefix negation sends zero to zero. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_neg_zero_eq :
    concreteL2GraphPairPrefixEnergyBoundedNeg
        concreteL2GraphPairPrefixEnergyBoundedZero =
      concreteL2GraphPairPrefixEnergyBoundedZero := by
  unfold concreteL2GraphPairPrefixEnergyBoundedNeg
  exact concrete_l2_graph_pair_prefix_energy_bounded_smul_zero_eq (-1 : ℝ)

/-- Concrete graph-pair addition has zero as a right identity. -/
theorem concrete_l2_graph_pair_add_zero_eq
    (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairAdd p concreteL2GraphPairZero = p := by
  apply Prod.ext
  · apply Subtype.ext
    funext n
    exact concrete_l2_real_add_zero_ext p.1 n
  · apply Subtype.ext
    funext n
    exact concrete_l2_real_add_zero_ext p.2 n

/-- Bounded-prefix addition has zero as a right identity. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_add_zero_eq
    (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedAdd x
        concreteL2GraphPairPrefixEnergyBoundedZero = x := by
  apply Subtype.ext
  exact concrete_l2_graph_pair_add_zero_eq x.1

/-- Bounded-prefix subtraction by zero is the original element. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_sub_zero_eq
    (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedSub x
        concreteL2GraphPairPrefixEnergyBoundedZero = x := by
  unfold concreteL2GraphPairPrefixEnergyBoundedSub
  rw [concrete_l2_graph_pair_prefix_energy_bounded_neg_zero_eq]
  exact concrete_l2_graph_pair_prefix_energy_bounded_add_zero_eq x

/-- The pseudo-distance from a point to the bounded zero is its seminorm
candidate. -/
theorem r2m_prefix_pseudo_distance_zero_right_eq_seminorm
    (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    r2mPrefixPseudoDistance N x concreteL2GraphPairPrefixEnergyBoundedZero =
      concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x := by
  unfold r2mPrefixPseudoDistance
  rw [concrete_l2_graph_pair_prefix_energy_bounded_sub_zero_eq]

/-- The missing smul-zero pseudo-distance compatibility bridge. -/
theorem r2m_prefix_smul_zero_pseudo_distance_compatibility
    (N : ℕ) (c : ℝ)
    (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    r2mPrefixPseudoDistance N
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x)
        concreteL2GraphPairPrefixEnergyBoundedZero =
      r2mPrefixPseudoDistance N
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x)
        (concreteL2GraphPairPrefixEnergyBoundedSmul c
          concreteL2GraphPairPrefixEnergyBoundedZero) := by
  rw [concrete_l2_graph_pair_prefix_energy_bounded_smul_zero_eq]

/-- Concrete zero compatibility readiness package. -/
def r2mPrefixConcreteZeroCompatibilityReady : Prop :=
  r2mPrefixQuotientSmulOperationReady ∧
  (∀ (c : ℝ),
    concreteL2GraphPairPrefixEnergyBoundedSmul c
        concreteL2GraphPairPrefixEnergyBoundedZero =
      concreteL2GraphPairPrefixEnergyBoundedZero) ∧
  (∀ (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    concreteL2GraphPairPrefixEnergyBoundedSub x
        concreteL2GraphPairPrefixEnergyBoundedZero = x) ∧
  (∀ (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    r2mPrefixPseudoDistance N x concreteL2GraphPairPrefixEnergyBoundedZero =
      concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x) ∧
  (∀ (N : ℕ) (c : ℝ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    r2mPrefixPseudoDistance N
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x)
        concreteL2GraphPairPrefixEnergyBoundedZero =
      r2mPrefixPseudoDistance N
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x)
        (concreteL2GraphPairPrefixEnergyBoundedSmul c
          concreteL2GraphPairPrefixEnergyBoundedZero))

/-- The concrete zero compatibility bridge is ready. -/
theorem r2m_prefix_concrete_zero_compatibility_ready :
    r2mPrefixConcreteZeroCompatibilityReady := by
  exact ⟨
    r2m_prefix_quotient_smul_operation_ready,
    concrete_l2_graph_pair_prefix_energy_bounded_smul_zero_eq,
    concrete_l2_graph_pair_prefix_energy_bounded_sub_zero_eq,
    r2m_prefix_pseudo_distance_zero_right_eq_seminorm,
    r2m_prefix_smul_zero_pseudo_distance_compatibility⟩

end

end MathlibAnalytic
end MGAP4D
