import MGAP4D.MathlibAnalytic.R2MPrefixQuotientNormedAddCommGroupSurface
import MGAP4D.MathlibAnalytic.R2MPrefixQuotientSmulSeminormLawClosure

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Concrete `l2` scalar multiplication by one is the identity. -/
theorem concrete_l2_real_one_smul
    (x : ConcreteL2RealSequence) :
    concreteL2RealSmul (1 : ℝ) x = x := by
  apply Subtype.ext
  funext n
  simp [concreteL2RealSmul]

/-- Concrete `l2` scalar multiplication is associative. -/
theorem concrete_l2_real_smul_smul
    (a b : ℝ) (x : ConcreteL2RealSequence) :
    concreteL2RealSmul a (concreteL2RealSmul b x) =
      concreteL2RealSmul (a * b) x := by
  apply Subtype.ext
  funext n
  simp [concreteL2RealSmul]
  ring

/-- Concrete graph-pair scalar multiplication by one is the identity. -/
theorem concrete_l2_graph_pair_one_smul
    (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairSmul (1 : ℝ) p = p := by
  apply Prod.ext
  · exact concrete_l2_real_one_smul p.1
  · exact concrete_l2_real_one_smul p.2

/-- Concrete graph-pair scalar multiplication is associative. -/
theorem concrete_l2_graph_pair_smul_smul
    (a b : ℝ) (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairSmul a (concreteL2GraphPairSmul b p) =
      concreteL2GraphPairSmul (a * b) p := by
  apply Prod.ext
  · exact concrete_l2_real_smul_smul a b p.1
  · exact concrete_l2_real_smul_smul a b p.2

/-- Bounded-prefix scalar multiplication by one is the identity. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_one_smul
    (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedSmul (1 : ℝ) x = x := by
  apply Subtype.ext
  exact concrete_l2_graph_pair_one_smul x.1

/-- Bounded-prefix scalar multiplication is associative. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_smul_smul
    (a b : ℝ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedSmul a
        (concreteL2GraphPairPrefixEnergyBoundedSmul b x) =
      concreteL2GraphPairPrefixEnergyBoundedSmul (a * b) x := by
  apply Subtype.ext
  exact concrete_l2_graph_pair_smul_smul a b x.1

/-- Quotient scalar multiplication by one is the identity. -/
theorem r2m_prefix_quotient_one_smul
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSmul N (1 : ℝ) q = q := by
  refine Quotient.inductionOn' q ?_
  intro x
  rw [r2m_prefix_quotient_smul_mk]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_one_smul]

/-- Quotient scalar multiplication is associative. -/
theorem r2m_prefix_quotient_smul_smul
    (N : ℕ) (a b : ℝ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSmul N a (r2mPrefixQuotientSmul N b q) =
      r2mPrefixQuotientSmul N (a * b) q := by
  refine Quotient.inductionOn' q ?_
  intro x
  rw [r2m_prefix_quotient_smul_mk]
  rw [r2m_prefix_quotient_smul_mk]
  rw [r2m_prefix_quotient_smul_mk]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_smul_smul]

/-- Mathlib-style alias for absolute homogeneity of the quotient norm-like
seminorm. -/
theorem r2m_prefix_quotient_norm_smul
    (N : ℕ) (c : ℝ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSmul N c q) =
      |c| * r2mPrefixQuotientSeminorm N q := by
  exact r2m_prefix_quotient_seminorm_smul_abs_closed N c q

/-- Pre-typeclass scalar algebra surface: scalar multiplication on the quotient
has the identity and associativity laws, and its seminorm is absolutely
homogeneous. -/
def r2mPrefixQuotientScalarAlgebraSurfaceReady : Prop :=
  r2mPrefixQuotientNormedAddCommGroupSurfaceReady ∧
  r2mPrefixQuotientSmulSeminormLawClosed ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSmul N (1 : ℝ) q = q) ∧
  (∀ (N : ℕ) (a b : ℝ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSmul N a (r2mPrefixQuotientSmul N b q) =
      r2mPrefixQuotientSmul N (a * b) q) ∧
  (∀ (N : ℕ) (c : ℝ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSmul N c q) =
      |c| * r2mPrefixQuotientSeminorm N q)

/-- The quotient scalar algebra surface is ready. -/
theorem r2m_prefix_quotient_scalar_algebra_surface_ready :
    r2mPrefixQuotientScalarAlgebraSurfaceReady := by
  exact ⟨
    r2m_prefix_quotient_normed_add_comm_group_surface_ready,
    r2m_prefix_quotient_smul_seminorm_law_closed,
    r2m_prefix_quotient_one_smul,
    r2m_prefix_quotient_smul_smul,
    r2m_prefix_quotient_norm_smul⟩

/-- Boundary marker: the quotient now has a normed additive group surface plus
scalar identity/associativity and absolute seminorm homogeneity.  Full
`Module`/`NormedSpace` instance promotion is intentionally deferred. -/
def r2mPrefixQuotientNormedSpaceBoundaryHeld : Prop :=
  r2mPrefixQuotientScalarAlgebraSurfaceReady ∧
  True

theorem r2m_prefix_quotient_normed_space_boundary_held :
    r2mPrefixQuotientNormedSpaceBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_scalar_algebra_surface_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
