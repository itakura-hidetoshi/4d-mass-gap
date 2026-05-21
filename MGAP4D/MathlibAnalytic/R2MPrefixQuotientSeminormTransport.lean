import MGAP4D.MathlibAnalytic.R2MPrefixZeroDistanceQuotient

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- If two representatives are at zero finite-prefix pseudo-distance, then
their distances to the basepoint are equal.  This is the well-definedness
lemma for transporting the seminorm candidate to the quotient. -/
theorem r2m_prefix_pseudo_distance_basepoint_eq_of_zero_distance
    (N : ℕ)
    {x y : ConcreteL2GraphPairPrefixEnergyBoundedElement}
    (hxy : r2mPrefixZeroDistanceRel N x y) :
    r2mPrefixPseudoDistance N x concreteL2GraphPairPrefixEnergyBoundedZero =
      r2mPrefixPseudoDistance N y concreteL2GraphPairPrefixEnergyBoundedZero := by
  unfold r2mPrefixZeroDistanceRel at hxy
  apply le_antisymm
  · have htri := r2m_prefix_pseudo_distance_triangle N x y
      concreteL2GraphPairPrefixEnergyBoundedZero
    simpa [hxy] using htri
  · have hyx : r2mPrefixPseudoDistance N y x = 0 := by
      rw [← r2m_prefix_pseudo_distance_symm N x y]
      exact hxy
    have htri := r2m_prefix_pseudo_distance_triangle N y x
      concreteL2GraphPairPrefixEnergyBoundedZero
    simpa [hyx] using htri

/-- The quotient seminorm candidate induced by the finite-prefix pseudo-distance.
It maps a zero-distance quotient class to the distance of any representative
from the bounded zero element. -/
def r2mPrefixQuotientSeminorm
    (N : ℕ) : R2MPrefixZeroDistanceQuotient N → ℝ :=
  fun q =>
    Quotient.liftOn' q
      (fun x : ConcreteL2GraphPairPrefixEnergyBoundedElement =>
        r2mPrefixPseudoDistance N x concreteL2GraphPairPrefixEnergyBoundedZero)
      (fun x y hxy =>
        r2m_prefix_pseudo_distance_basepoint_eq_of_zero_distance N hxy)

/-- Evaluation of the quotient seminorm candidate on a concrete representative. -/
theorem r2m_prefix_quotient_seminorm_mk
    (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    r2mPrefixQuotientSeminorm N
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N) x) =
      r2mPrefixPseudoDistance N x concreteL2GraphPairPrefixEnergyBoundedZero := by
  rfl

/-- Nonnegativity of the quotient seminorm candidate. -/
theorem r2m_prefix_quotient_seminorm_nonneg
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    0 ≤ r2mPrefixQuotientSeminorm N q := by
  unfold r2mPrefixQuotientSeminorm
  refine Quotient.inductionOn' q ?_
  intro x
  exact r2m_prefix_pseudo_distance_nonneg N x
    concreteL2GraphPairPrefixEnergyBoundedZero

/-- The quotient seminorm candidate vanishes at the zero class. -/
theorem r2m_prefix_quotient_seminorm_zero_class
    (N : ℕ) :
    r2mPrefixQuotientSeminorm N
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N)
          concreteL2GraphPairPrefixEnergyBoundedZero) = 0 := by
  rw [r2m_prefix_quotient_seminorm_mk]
  exact r2m_prefix_pseudo_distance_self N
    concreteL2GraphPairPrefixEnergyBoundedZero

/-- Readiness package for transporting the finite-prefix seminorm candidate to
the zero-distance quotient as a well-defined nonnegative function.  Algebraic
operations on the quotient are intentionally deferred to the next layer. -/
def r2mPrefixQuotientSeminormTransportReady : Prop :=
  r2mPrefixZeroDistanceQuotientReady ∧
  (∀ (N : ℕ)
      {x y : ConcreteL2GraphPairPrefixEnergyBoundedElement},
    r2mPrefixZeroDistanceRel N x y →
      r2mPrefixPseudoDistance N x concreteL2GraphPairPrefixEnergyBoundedZero =
        r2mPrefixPseudoDistance N y concreteL2GraphPairPrefixEnergyBoundedZero) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    0 ≤ r2mPrefixQuotientSeminorm N q) ∧
  (∀ N : ℕ,
    r2mPrefixQuotientSeminorm N
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N)
          concreteL2GraphPairPrefixEnergyBoundedZero) = 0)

/-- The quotient seminorm transport surface is ready. -/
theorem r2m_prefix_quotient_seminorm_transport_ready :
    r2mPrefixQuotientSeminormTransportReady := by
  exact ⟨
    r2m_prefix_zero_distance_quotient_ready,
    fun N {x y} hxy =>
      r2m_prefix_pseudo_distance_basepoint_eq_of_zero_distance N hxy,
    r2m_prefix_quotient_seminorm_nonneg,
    r2m_prefix_quotient_seminorm_zero_class⟩

/-- Boundary marker: the quotient carrier now has a well-defined nonnegative
seminorm-candidate function, but add/smul operations on the quotient and full
seminorm laws are intentionally kept for the next layer. -/
def r2mPrefixQuotientSeminormLawBoundaryHeld : Prop :=
  r2mPrefixQuotientSeminormTransportReady ∧
  True

theorem r2m_prefix_quotient_seminorm_law_boundary_held :
    r2mPrefixQuotientSeminormLawBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_seminorm_transport_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
