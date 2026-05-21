import MGAP4D.MathlibAnalytic.R2MPrefixQuotientModuleSurface

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Concrete `l2` scalar multiplication by zero sends every sequence to zero. -/
theorem concrete_l2_real_zero_smul
    (x : ConcreteL2RealSequence) :
    concreteL2RealSmul (0 : ℝ) x = concreteL2RealZero := by
  apply Subtype.ext
  funext n
  simp [concreteL2RealSmul, concreteL2RealZero]

/-- Concrete graph-pair scalar multiplication by zero sends every pair to zero. -/
theorem concrete_l2_graph_pair_zero_smul
    (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairSmul (0 : ℝ) p = concreteL2GraphPairZero := by
  apply Prod.ext
  · exact concrete_l2_real_zero_smul p.1
  · exact concrete_l2_real_zero_smul p.2

/-- Bounded-prefix scalar multiplication by zero sends every bounded element to
bounded zero. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_zero_smul
    (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedSmul (0 : ℝ) x =
      concreteL2GraphPairPrefixEnergyBoundedZero := by
  apply Subtype.ext
  exact concrete_l2_graph_pair_zero_smul x.1

/-- Quotient scalar multiplication by zero sends every class to the zero class. -/
theorem r2m_prefix_quotient_zero_smul
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSmul N (0 : ℝ) q =
      r2mPrefixQuotientZeroClass N := by
  refine Quotient.inductionOn' q ?_
  intro x
  unfold r2mPrefixQuotientZeroClass
  rw [r2m_prefix_quotient_smul_mk]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_zero_smul]

/-- Quotient scalar multiplication sends the zero class to the zero class. -/
theorem r2m_prefix_quotient_smul_zero
    (N : ℕ) (c : ℝ) :
    r2mPrefixQuotientSmul N c (r2mPrefixQuotientZeroClass N) =
      r2mPrefixQuotientZeroClass N := by
  unfold r2mPrefixQuotientZeroClass
  rw [r2m_prefix_quotient_smul_mk]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_smul_zero_eq]

/-- Full pre-typeclass module surface: all scalar identity, scalar associativity,
zero, and distributivity laws have been proved explicitly on the quotient. -/
def r2mPrefixQuotientFullModuleSurfaceReady : Prop :=
  r2mPrefixQuotientModuleSurfaceReady ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSmul N (0 : ℝ) q =
      r2mPrefixQuotientZeroClass N) ∧
  (∀ (N : ℕ) (c : ℝ),
    r2mPrefixQuotientSmul N c (r2mPrefixQuotientZeroClass N) =
      r2mPrefixQuotientZeroClass N)

/-- The full quotient module theorem surface is ready. -/
theorem r2m_prefix_quotient_full_module_surface_ready :
    r2mPrefixQuotientFullModuleSurfaceReady := by
  exact ⟨
    r2m_prefix_quotient_module_surface_ready,
    r2m_prefix_quotient_zero_smul,
    r2m_prefix_quotient_smul_zero⟩

/-- Boundary marker: the quotient now has the full theorem surface expected of a
real module, while actual typeclass promotion remains a separate explicit
instance step. -/
def r2mPrefixQuotientFullModuleBoundaryHeld : Prop :=
  r2mPrefixQuotientFullModuleSurfaceReady ∧
  True

theorem r2m_prefix_quotient_full_module_boundary_held :
    r2mPrefixQuotientFullModuleBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_full_module_surface_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
