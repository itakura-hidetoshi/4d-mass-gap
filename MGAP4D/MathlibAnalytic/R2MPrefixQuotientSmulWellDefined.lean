import MGAP4D.MathlibAnalytic.R2MPrefixQuotientAddWellDefined

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Quadratic scaling for finite-prefix differences.  This is the scalar
compatibility calculation needed before installing scalar multiplication on the
zero-distance quotient. -/
theorem r2m_prefix_quadratic_sub_smul_eq
    (N : ℕ) (c : ℝ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedSub
          (concreteL2GraphPairPrefixEnergyBoundedSmul c x)
          (concreteL2GraphPairPrefixEnergyBoundedSmul c y)) =
      c ^ 2 *
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
          (concreteL2GraphPairPrefixEnergyBoundedSub x y) := by
  rw [r2m_prefix_quadratic_sub_expansion]
  rw [r2m_prefix_quadratic_sub_expansion]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_quadratic_smul_eq]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_quadratic_smul_eq]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_smul_left]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_smul_right]
  ring

/-- Scalar multiplication preserves the finite-prefix zero-distance relation. -/
theorem r2m_prefix_zero_distance_smul
    (N : ℕ) (c : ℝ)
    {x x' : ConcreteL2GraphPairPrefixEnergyBoundedElement}
    (hxx' : r2mPrefixZeroDistanceRel N x x') :
    r2mPrefixZeroDistanceRel N
      (concreteL2GraphPairPrefixEnergyBoundedSmul c x)
      (concreteL2GraphPairPrefixEnergyBoundedSmul c x') := by
  unfold r2mPrefixZeroDistanceRel at hxx' ⊢
  have hq :
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
          (concreteL2GraphPairPrefixEnergyBoundedSub x x') = 0 := by
    have hsquare :=
      concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_sq N
        (concreteL2GraphPairPrefixEnergyBoundedSub x x')
    unfold r2mPrefixPseudoDistance at hxx'
    rw [← hsquare, hxx']
    ring
  unfold r2mPrefixPseudoDistance
  unfold concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate
  rw [r2m_prefix_quadratic_sub_smul_eq]
  rw [hq]
  rw [mul_zero]
  exact Real.sqrt_zero

/-- Scalar well-definedness obligation is closed. -/
def r2mPrefixQuotientSmulWellDefinedReady : Prop :=
  r2mPrefixQuotientAddSmulWellDefinedBoundaryHeld ∧
  r2mPrefixQuotientSmulWellDefinedObligation

/-- The zero-distance relation is compatible with scalar multiplication. -/
theorem r2m_prefix_quotient_smul_well_defined_ready :
    r2mPrefixQuotientSmulWellDefinedReady := by
  exact ⟨
    r2m_prefix_quotient_add_smul_well_defined_boundary_held,
    r2m_prefix_zero_distance_smul⟩

/-- Boundary marker: scalar compatibility is closed; additive compatibility is
still kept as the next explicit algebraic obligation. -/
def r2mPrefixQuotientAddWellDefinedBoundaryHeld : Prop :=
  r2mPrefixQuotientSmulWellDefinedReady ∧
  True

theorem r2m_prefix_quotient_add_well_defined_boundary_held :
    r2mPrefixQuotientAddWellDefinedBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_smul_well_defined_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
