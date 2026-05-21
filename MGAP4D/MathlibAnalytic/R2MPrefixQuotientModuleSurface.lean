import MGAP4D.MathlibAnalytic.R2MPrefixQuotientScalarAlgebraSurface

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Concrete `l2` scalar multiplication distributes over addition. -/
theorem concrete_l2_real_smul_add
    (c : ℝ) (x y : ConcreteL2RealSequence) :
    concreteL2RealSmul c (concreteL2RealAdd x y) =
      concreteL2RealAdd (concreteL2RealSmul c x) (concreteL2RealSmul c y) := by
  apply Subtype.ext
  funext n
  simp [concreteL2RealSmul, concreteL2RealAdd]
  ring

/-- Concrete `l2` scalar addition acts pointwise as the sum of scalar actions. -/
theorem concrete_l2_real_add_smul
    (a b : ℝ) (x : ConcreteL2RealSequence) :
    concreteL2RealSmul (a + b) x =
      concreteL2RealAdd (concreteL2RealSmul a x) (concreteL2RealSmul b x) := by
  apply Subtype.ext
  funext n
  simp [concreteL2RealSmul, concreteL2RealAdd]
  ring

/-- Concrete graph-pair scalar multiplication distributes over addition. -/
theorem concrete_l2_graph_pair_smul_add
    (c : ℝ) (p q : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairSmul c (concreteL2GraphPairAdd p q) =
      concreteL2GraphPairAdd
        (concreteL2GraphPairSmul c p)
        (concreteL2GraphPairSmul c q) := by
  apply Prod.ext
  · exact concrete_l2_real_smul_add c p.1 q.1
  · exact concrete_l2_real_smul_add c p.2 q.2

/-- Concrete graph-pair scalar addition acts as the sum of scalar actions. -/
theorem concrete_l2_graph_pair_add_smul
    (a b : ℝ) (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairSmul (a + b) p =
      concreteL2GraphPairAdd
        (concreteL2GraphPairSmul a p)
        (concreteL2GraphPairSmul b p) := by
  apply Prod.ext
  · exact concrete_l2_real_add_smul a b p.1
  · exact concrete_l2_real_add_smul a b p.2

/-- Bounded-prefix scalar multiplication distributes over bounded addition. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_smul_add
    (c : ℝ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedSmul c
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) =
      concreteL2GraphPairPrefixEnergyBoundedAdd
        (concreteL2GraphPairPrefixEnergyBoundedSmul c x)
        (concreteL2GraphPairPrefixEnergyBoundedSmul c y) := by
  apply Subtype.ext
  exact concrete_l2_graph_pair_smul_add c x.1 y.1

/-- Bounded-prefix scalar addition acts as the sum of bounded scalar actions. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_add_smul
    (a b : ℝ)
    (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedSmul (a + b) x =
      concreteL2GraphPairPrefixEnergyBoundedAdd
        (concreteL2GraphPairPrefixEnergyBoundedSmul a x)
        (concreteL2GraphPairPrefixEnergyBoundedSmul b x) := by
  apply Subtype.ext
  exact concrete_l2_graph_pair_add_smul a b x.1

/-- Quotient scalar multiplication distributes over quotient addition. -/
theorem r2m_prefix_quotient_smul_add
    (N : ℕ) (c : ℝ)
    (q r : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSmul N c (r2mPrefixQuotientAdd N q r) =
      r2mPrefixQuotientAdd N
        (r2mPrefixQuotientSmul N c q)
        (r2mPrefixQuotientSmul N c r) := by
  refine Quotient.inductionOn' q ?_
  intro x
  refine Quotient.inductionOn' r ?_
  intro y
  rw [r2m_prefix_quotient_add_mk]
  rw [r2m_prefix_quotient_smul_mk]
  rw [r2m_prefix_quotient_smul_mk]
  rw [r2m_prefix_quotient_smul_mk]
  rw [r2m_prefix_quotient_add_mk]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_smul_add]

/-- Quotient scalar addition acts as the sum of quotient scalar actions. -/
theorem r2m_prefix_quotient_add_smul
    (N : ℕ) (a b : ℝ)
    (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSmul N (a + b) q =
      r2mPrefixQuotientAdd N
        (r2mPrefixQuotientSmul N a q)
        (r2mPrefixQuotientSmul N b q) := by
  refine Quotient.inductionOn' q ?_
  intro x
  rw [r2m_prefix_quotient_smul_mk]
  rw [r2m_prefix_quotient_smul_mk]
  rw [r2m_prefix_quotient_smul_mk]
  rw [r2m_prefix_quotient_add_mk]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_add_smul]

/-- Pre-typeclass module surface: quotient addition and scalar multiplication
satisfy the scalar identity, scalar associativity, and both distributive laws.
This deliberately records the structure before installing a global `Module`
instance. -/
def r2mPrefixQuotientModuleSurfaceReady : Prop :=
  r2mPrefixQuotientScalarAlgebraSurfaceReady ∧
  (∀ (N : ℕ) (c : ℝ) (q r : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSmul N c (r2mPrefixQuotientAdd N q r) =
      r2mPrefixQuotientAdd N
        (r2mPrefixQuotientSmul N c q)
        (r2mPrefixQuotientSmul N c r)) ∧
  (∀ (N : ℕ) (a b : ℝ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSmul N (a + b) q =
      r2mPrefixQuotientAdd N
        (r2mPrefixQuotientSmul N a q)
        (r2mPrefixQuotientSmul N b q))

/-- The quotient module surface is ready. -/
theorem r2m_prefix_quotient_module_surface_ready :
    r2mPrefixQuotientModuleSurfaceReady := by
  exact ⟨
    r2m_prefix_quotient_scalar_algebra_surface_ready,
    r2m_prefix_quotient_smul_add,
    r2m_prefix_quotient_add_smul⟩

/-- Boundary marker: the quotient now has a normed additive group surface,
scalar algebra laws, and distributive module laws.  Full `Module`/`NormedSpace`
instance promotion is intentionally deferred to a separate, audit-visible step. -/
def r2mPrefixQuotientModuleBoundaryHeld : Prop :=
  r2mPrefixQuotientModuleSurfaceReady ∧
  True

theorem r2m_prefix_quotient_module_boundary_held :
    r2mPrefixQuotientModuleBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_module_surface_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
