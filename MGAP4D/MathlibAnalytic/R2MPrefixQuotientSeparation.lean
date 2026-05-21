import MGAP4D.MathlibAnalytic.R2MPrefixQuotientSeminormTransport

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The distinguished zero class in the finite-prefix zero-distance quotient. -/
def r2mPrefixQuotientZeroClass
    (N : ℕ) : R2MPrefixZeroDistanceQuotient N :=
  Quotient.mk (r2mPrefixZeroDistanceSetoid N)
    concreteL2GraphPairPrefixEnergyBoundedZero

/-- The quotient seminorm candidate vanishes at the distinguished zero class. -/
theorem r2m_prefix_quotient_seminorm_zero_class'
    (N : ℕ) :
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientZeroClass N) = 0 := by
  unfold r2mPrefixQuotientZeroClass
  exact r2m_prefix_quotient_seminorm_zero_class N

/-- A representative whose pseudo-distance to zero is zero is exactly the zero
class in the zero-distance quotient. -/
theorem r2m_prefix_quotient_mk_eq_zero_class_of_pseudo_distance_zero
    (N : ℕ) (x : ConcreteL2GraphPairPrefixEnergyBoundedElement)
    (hx : r2mPrefixPseudoDistance N x concreteL2GraphPairPrefixEnergyBoundedZero = 0) :
    Quotient.mk (r2mPrefixZeroDistanceSetoid N) x =
      r2mPrefixQuotientZeroClass N := by
  unfold r2mPrefixQuotientZeroClass
  apply Quotient.sound
  change r2mPrefixPseudoDistance N x concreteL2GraphPairPrefixEnergyBoundedZero = 0
  exact hx

/-- Definiteness after quotienting: the transported quotient seminorm candidate
is zero exactly on the distinguished zero class. -/
theorem r2m_prefix_quotient_seminorm_eq_zero_iff
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSeminorm N q = 0 ↔
      q = r2mPrefixQuotientZeroClass N := by
  refine Quotient.inductionOn' q ?_
  intro x
  constructor
  · intro hx
    rw [r2m_prefix_quotient_seminorm_mk] at hx
    exact r2m_prefix_quotient_mk_eq_zero_class_of_pseudo_distance_zero N x hx
  · intro hx
    rw [hx]
    exact r2m_prefix_quotient_seminorm_zero_class' N

/-- Separation readiness for the quotient seminorm candidate.  This is the
first genuinely quotient-level separation statement: the pseudo-kernel has been
collapsed, so zero seminorm now means zero class. -/
def r2mPrefixQuotientSeparationReady : Prop :=
  r2mPrefixQuotientSeminormTransportReady ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSeminorm N q = 0 ↔
      q = r2mPrefixQuotientZeroClass N)

/-- The quotient separation surface is ready. -/
theorem r2m_prefix_quotient_separation_ready :
    r2mPrefixQuotientSeparationReady := by
  exact ⟨
    r2m_prefix_quotient_seminorm_transport_ready,
    r2m_prefix_quotient_seminorm_eq_zero_iff⟩

/-- Boundary marker: quotient separation is closed, while quotient add/smul and
full seminorm laws remain the next layer. -/
def r2mPrefixQuotientAddSmulBoundaryHeld : Prop :=
  r2mPrefixQuotientSeparationReady ∧
  True

theorem r2m_prefix_quotient_add_smul_boundary_held :
    r2mPrefixQuotientAddSmulBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_separation_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
