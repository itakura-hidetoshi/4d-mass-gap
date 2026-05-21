import MGAP4D.MathlibAnalytic.R2MPrefixConcreteZeroCompatibility

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Concrete `l2` addition is commutative. -/
theorem concrete_l2_real_add_comm
    (x y : ConcreteL2RealSequence) :
    concreteL2RealAdd x y = concreteL2RealAdd y x := by
  apply Subtype.ext
  funext n
  simp [concreteL2RealAdd]
  ring

/-- Concrete `l2` addition is associative. -/
theorem concrete_l2_real_add_assoc
    (x y z : ConcreteL2RealSequence) :
    concreteL2RealAdd (concreteL2RealAdd x y) z =
      concreteL2RealAdd x (concreteL2RealAdd y z) := by
  apply Subtype.ext
  funext n
  simp [concreteL2RealAdd]
  ring

/-- Concrete `l2` addition has zero as a left identity. -/
theorem concrete_l2_real_zero_add_eq
    (x : ConcreteL2RealSequence) :
    concreteL2RealAdd concreteL2RealZero x = x := by
  apply Subtype.ext
  funext n
  simp [concreteL2RealAdd, concreteL2RealZero]

/-- Concrete `l2` addition with the explicit scalar negation cancels. -/
theorem concrete_l2_real_add_neg_eq_zero
    (x : ConcreteL2RealSequence) :
    concreteL2RealAdd x (concreteL2RealSmul (-1 : ℝ) x) =
      concreteL2RealZero := by
  apply Subtype.ext
  funext n
  simp [concreteL2RealAdd, concreteL2RealSmul, concreteL2RealZero]

/-- Concrete graph-pair addition is commutative. -/
theorem concrete_l2_graph_pair_add_comm
    (p q : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairAdd p q = concreteL2GraphPairAdd q p := by
  apply Prod.ext
  · exact concrete_l2_real_add_comm p.1 q.1
  · exact concrete_l2_real_add_comm p.2 q.2

/-- Concrete graph-pair addition is associative. -/
theorem concrete_l2_graph_pair_add_assoc
    (p q r : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairAdd (concreteL2GraphPairAdd p q) r =
      concreteL2GraphPairAdd p (concreteL2GraphPairAdd q r) := by
  apply Prod.ext
  · exact concrete_l2_real_add_assoc p.1 q.1 r.1
  · exact concrete_l2_real_add_assoc p.2 q.2 r.2

/-- Concrete graph-pair addition has zero as a left identity. -/
theorem concrete_l2_graph_pair_zero_add_eq
    (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairAdd concreteL2GraphPairZero p = p := by
  apply Prod.ext
  · exact concrete_l2_real_zero_add_eq p.1
  · exact concrete_l2_real_zero_add_eq p.2

/-- Concrete graph-pair addition cancels against explicit scalar negation. -/
theorem concrete_l2_graph_pair_add_neg_eq_zero
    (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairAdd p (concreteL2GraphPairSmul (-1 : ℝ) p) =
      concreteL2GraphPairZero := by
  apply Prod.ext
  · exact concrete_l2_real_add_neg_eq_zero p.1
  · exact concrete_l2_real_add_neg_eq_zero p.2

/-- Bounded-prefix addition is commutative. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_add_comm
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedAdd x y =
      concreteL2GraphPairPrefixEnergyBoundedAdd y x := by
  apply Subtype.ext
  exact concrete_l2_graph_pair_add_comm x.1 y.1

/-- Bounded-prefix addition is associative. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_add_assoc
    (x y z : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedAdd
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) z =
      concreteL2GraphPairPrefixEnergyBoundedAdd x
        (concreteL2GraphPairPrefixEnergyBoundedAdd y z) := by
  apply Subtype.ext
  exact concrete_l2_graph_pair_add_assoc x.1 y.1 z.1

/-- Bounded-prefix addition has zero as a left identity. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_zero_add_eq
    (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedAdd
        concreteL2GraphPairPrefixEnergyBoundedZero x = x := by
  apply Subtype.ext
  exact concrete_l2_graph_pair_zero_add_eq x.1

/-- Bounded-prefix addition cancels against bounded negation. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_add_neg_eq_zero
    (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedAdd x
        (concreteL2GraphPairPrefixEnergyBoundedNeg x) =
      concreteL2GraphPairPrefixEnergyBoundedZero := by
  apply Subtype.ext
  unfold concreteL2GraphPairPrefixEnergyBoundedNeg
  exact concrete_l2_graph_pair_add_neg_eq_zero x.1

/-- Concrete additive algebra readiness package for the bounded-prefix carrier. -/
def r2mPrefixConcreteAddAlgebraReady : Prop :=
  r2mPrefixConcreteZeroCompatibilityReady ∧
  (∀ x y : ConcreteL2GraphPairPrefixEnergyBoundedElement,
    concreteL2GraphPairPrefixEnergyBoundedAdd x y =
      concreteL2GraphPairPrefixEnergyBoundedAdd y x) ∧
  (∀ x y z : ConcreteL2GraphPairPrefixEnergyBoundedElement,
    concreteL2GraphPairPrefixEnergyBoundedAdd
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) z =
      concreteL2GraphPairPrefixEnergyBoundedAdd x
        (concreteL2GraphPairPrefixEnergyBoundedAdd y z)) ∧
  (∀ x : ConcreteL2GraphPairPrefixEnergyBoundedElement,
    concreteL2GraphPairPrefixEnergyBoundedAdd
        concreteL2GraphPairPrefixEnergyBoundedZero x = x) ∧
  (∀ x : ConcreteL2GraphPairPrefixEnergyBoundedElement,
    concreteL2GraphPairPrefixEnergyBoundedAdd x
        (concreteL2GraphPairPrefixEnergyBoundedNeg x) =
      concreteL2GraphPairPrefixEnergyBoundedZero)

/-- The concrete additive algebra surface is ready. -/
theorem r2m_prefix_concrete_add_algebra_ready :
    r2mPrefixConcreteAddAlgebraReady := by
  exact ⟨
    r2m_prefix_concrete_zero_compatibility_ready,
    concrete_l2_graph_pair_prefix_energy_bounded_add_comm,
    concrete_l2_graph_pair_prefix_energy_bounded_add_assoc,
    concrete_l2_graph_pair_prefix_energy_bounded_zero_add_eq,
    concrete_l2_graph_pair_prefix_energy_bounded_add_neg_eq_zero⟩

end

end MathlibAnalytic
end MGAP4D
