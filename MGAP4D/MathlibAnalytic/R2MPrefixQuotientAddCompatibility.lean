import MGAP4D.MathlibAnalytic.R2MPrefixQuotientSmulZeroLocus

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Pointwise concrete `l2` subtraction distributes over addition:
`(x+y)-(x'+y') = (x-x')+(y-y')`. -/
theorem concrete_l2_real_sub_add_sub_eq
    (x y x' y' : ConcreteL2RealSequence) :
    concreteL2RealAdd (concreteL2RealAdd x y)
        (concreteL2RealSmul (-1 : ℝ) (concreteL2RealAdd x' y')) =
      concreteL2RealAdd
        (concreteL2RealAdd x (concreteL2RealSmul (-1 : ℝ) x'))
        (concreteL2RealAdd y (concreteL2RealSmul (-1 : ℝ) y')) := by
  apply Subtype.ext
  funext n
  simp [concreteL2RealAdd, concreteL2RealSmul]
  ring

/-- Graph-pair subtraction distributes over addition. -/
theorem concrete_l2_graph_pair_sub_add_sub_eq
    (x y x' y' : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairAdd (concreteL2GraphPairAdd x y)
        (concreteL2GraphPairSmul (-1 : ℝ) (concreteL2GraphPairAdd x' y')) =
      concreteL2GraphPairAdd
        (concreteL2GraphPairAdd x (concreteL2GraphPairSmul (-1 : ℝ) x'))
        (concreteL2GraphPairAdd y (concreteL2GraphPairSmul (-1 : ℝ) y')) := by
  apply Prod.ext
  · exact concrete_l2_real_sub_add_sub_eq x.1 y.1 x'.1 y'.1
  · exact concrete_l2_real_sub_add_sub_eq x.2 y.2 x'.2 y'.2

/-- Bounded-prefix subtraction distributes over addition. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_sub_add_sub_eq
    (x y x' y' : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedSub
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y)
        (concreteL2GraphPairPrefixEnergyBoundedAdd x' y') =
      concreteL2GraphPairPrefixEnergyBoundedAdd
        (concreteL2GraphPairPrefixEnergyBoundedSub x x')
        (concreteL2GraphPairPrefixEnergyBoundedSub y y') := by
  apply Subtype.ext
  unfold concreteL2GraphPairPrefixEnergyBoundedSub
  unfold concreteL2GraphPairPrefixEnergyBoundedNeg
  exact concrete_l2_graph_pair_sub_add_sub_eq x.1 y.1 x'.1 y'.1

/-- Pseudo-distance of sums is bounded by the sum of pseudo-distances. -/
theorem r2m_prefix_pseudo_distance_add_add_le
    (N : ℕ)
    (x y x' y' : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    r2mPrefixPseudoDistance N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y)
        (concreteL2GraphPairPrefixEnergyBoundedAdd x' y') ≤
      r2mPrefixPseudoDistance N x x' + r2mPrefixPseudoDistance N y y' := by
  unfold r2mPrefixPseudoDistance
  rw [concrete_l2_graph_pair_prefix_energy_bounded_sub_add_sub_eq]
  exact r2m_prefix_triangle_inequality N
    (concreteL2GraphPairPrefixEnergyBoundedSub x x')
    (concreteL2GraphPairPrefixEnergyBoundedSub y y')

/-- Addition preserves the finite-prefix zero-distance relation. -/
theorem r2m_prefix_zero_distance_add_compat
    (N : ℕ)
    {x x' y y' : ConcreteL2GraphPairPrefixEnergyBoundedElement}
    (hxx' : r2mPrefixZeroDistanceRel N x x')
    (hyy' : r2mPrefixZeroDistanceRel N y y') :
    r2mPrefixZeroDistanceRel N
      (concreteL2GraphPairPrefixEnergyBoundedAdd x y)
      (concreteL2GraphPairPrefixEnergyBoundedAdd x' y') := by
  unfold r2mPrefixZeroDistanceRel at hxx' hyy' ⊢
  have hle := r2m_prefix_pseudo_distance_add_add_le N x y x' y'
  have hnonneg := r2m_prefix_pseudo_distance_nonneg N
    (concreteL2GraphPairPrefixEnergyBoundedAdd x y)
    (concreteL2GraphPairPrefixEnergyBoundedAdd x' y')
  have hupper :
      r2mPrefixPseudoDistance N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y)
        (concreteL2GraphPairPrefixEnergyBoundedAdd x' y') ≤ 0 := by
    simpa [hxx', hyy'] using hle
  exact le_antisymm hupper hnonneg

/-- The quotient addition well-definedness obligation is discharged. -/
def r2mPrefixQuotientAddCompatibilityReady : Prop :=
  r2mPrefixQuotientAdditiveCompatibilityBoundaryHeld ∧
  r2mPrefixQuotientAddWellDefinedObligation ∧
  (∀ (N : ℕ)
      (x y x' y' : ConcreteL2GraphPairPrefixEnergyBoundedElement),
    r2mPrefixPseudoDistance N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y)
        (concreteL2GraphPairPrefixEnergyBoundedAdd x' y') ≤
      r2mPrefixPseudoDistance N x x' + r2mPrefixPseudoDistance N y y')

/-- Additive compatibility for the zero-distance quotient is ready. -/
theorem r2m_prefix_quotient_add_compatibility_ready :
    r2mPrefixQuotientAddCompatibilityReady := by
  exact ⟨
    r2m_prefix_quotient_additive_compatibility_boundary_held,
    r2m_prefix_zero_distance_add_compat,
    r2m_prefix_pseudo_distance_add_add_le⟩

end

end MathlibAnalytic
end MGAP4D
