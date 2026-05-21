import MGAP4D.MathlibAnalytic.R2MPrefixPseudoMetric

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Zero-distance relation induced by the finite-prefix pseudo-distance. -/
def r2mPrefixZeroDistanceRel
    (N : ℕ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) : Prop :=
  r2mPrefixPseudoDistance N x y = 0

/-- Reflexivity of the zero-distance relation. -/
theorem r2m_prefix_zero_distance_refl
    (N : ℕ) :
    Reflexive (r2mPrefixZeroDistanceRel N) := by
  intro x
  unfold r2mPrefixZeroDistanceRel
  exact r2m_prefix_pseudo_distance_self N x

/-- Symmetry of the zero-distance relation. -/
theorem r2m_prefix_zero_distance_symm
    (N : ℕ) :
    Symmetric (r2mPrefixZeroDistanceRel N) := by
  intro x y hxy
  unfold r2mPrefixZeroDistanceRel at hxy ⊢
  rw [← r2m_prefix_pseudo_distance_symm N x y]
  exact hxy

/-- Transitivity of the zero-distance relation, from pseudo-distance triangle
and nonnegativity. -/
theorem r2m_prefix_zero_distance_trans
    (N : ℕ) :
    Transitive (r2mPrefixZeroDistanceRel N) := by
  intro x y z hxy hyz
  unfold r2mPrefixZeroDistanceRel at hxy hyz ⊢
  have htri := r2m_prefix_pseudo_distance_triangle N x y z
  have hnonneg := r2m_prefix_pseudo_distance_nonneg N x z
  have hupper : r2mPrefixPseudoDistance N x z ≤ 0 := by
    simpa [hxy, hyz] using htri
  exact le_antisymm hupper hnonneg

/-- The zero-distance relation is an equivalence relation. -/
theorem r2m_prefix_zero_distance_equivalence
    (N : ℕ) :
    Equivalence (r2mPrefixZeroDistanceRel N) := by
  exact ⟨
    r2m_prefix_zero_distance_refl N,
    r2m_prefix_zero_distance_symm N,
    r2m_prefix_zero_distance_trans N⟩

/-- Mathlib `Setoid` associated to the finite-prefix zero-distance relation. -/
def r2mPrefixZeroDistanceSetoid
    (N : ℕ) : Setoid ConcreteL2GraphPairPrefixEnergyBoundedElement where
  r := r2mPrefixZeroDistanceRel N
  iseqv := r2m_prefix_zero_distance_equivalence N

/-- The quotient carrier obtained by identifying finite-prefix zero-distance
points.  This is only the quotient carrier surface; norm/seminorm transport is
kept for the next file. -/
def R2MPrefixZeroDistanceQuotient (N : ℕ) : Type :=
  Quotient (r2mPrefixZeroDistanceSetoid N)

/-- The quotient carrier is inhabited by the class of the bounded zero element. -/
theorem r2m_prefix_zero_distance_quotient_nonempty
    (N : ℕ) :
    Nonempty (R2MPrefixZeroDistanceQuotient N) := by
  unfold R2MPrefixZeroDistanceQuotient
  exact ⟨Quotient.mk (r2mPrefixZeroDistanceSetoid N)
    concreteL2GraphPairPrefixEnergyBoundedZero⟩

/-- Quotient readiness package for the zero-distance finite-prefix relation. -/
def r2mPrefixZeroDistanceQuotientReady : Prop :=
  r2mPrefixPseudoMetricReady ∧
  (∀ N : ℕ, Equivalence (r2mPrefixZeroDistanceRel N)) ∧
  (∀ N : ℕ, Nonempty (R2MPrefixZeroDistanceQuotient N))

/-- The zero-distance quotient surface is now available. -/
theorem r2m_prefix_zero_distance_quotient_ready :
    r2mPrefixZeroDistanceQuotientReady := by
  exact ⟨
    r2m_prefix_pseudo_metric_ready,
    r2m_prefix_zero_distance_equivalence,
    r2m_prefix_zero_distance_quotient_nonempty⟩

/-- Boundary marker: the next step is transporting the seminorm candidate to
this quotient. -/
def r2mPrefixZeroDistanceNormTransportBoundaryHeld : Prop :=
  r2mPrefixZeroDistanceQuotientReady ∧
  True

theorem r2m_prefix_zero_distance_norm_transport_boundary_held :
    r2mPrefixZeroDistanceNormTransportBoundaryHeld := by
  exact ⟨r2m_prefix_zero_distance_quotient_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
