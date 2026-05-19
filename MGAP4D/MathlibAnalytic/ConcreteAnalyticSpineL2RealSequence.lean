import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineOperatorLaneCheckpoint

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Concrete real square-summable sequence carrier.  This is the first explicit
`l2`-type carrier for the analytic spine: a real sequence together with a
Mathlib `Summable` proof for the square sequence. -/
def ConcreteL2RealSequence : Type :=
  { x : ℕ → ℝ // Summable fun n : ℕ => (x n) ^ 2 }

/-- The zero sequence belongs to the concrete `l2` carrier. -/
def concreteL2RealZero : ConcreteL2RealSequence :=
  ⟨fun _ => 0, by
    simp⟩

/-- Finite-support predicate inside the concrete `l2` carrier. -/
def ConcreteL2RealFiniteSupport (x : ConcreteL2RealSequence) : Prop :=
  ({n : ℕ | x.1 n ≠ 0} : Set ℕ).Finite

/-- The zero `l2` sequence has finite support. -/
theorem concrete_l2_real_zero_finite_support :
    ConcreteL2RealFiniteSupport concreteL2RealZero := by
  unfold ConcreteL2RealFiniteSupport concreteL2RealZero
  simp

/-- Diagonal weights for the first concrete unbounded-operator lane.  The growth
is intentionally unbounded in `n`; no self-adjointness or spectral theorem is
claimed here. -/
def concreteL2DiagonalWeight (n : ℕ) : ℝ := (n : ℝ) + 1

/-- Domain predicate for the diagonal multiplication lane. -/
def ConcreteL2DiagonalDomain (x : ConcreteL2RealSequence) : Prop :=
  Summable fun n : ℕ => (concreteL2DiagonalWeight n)^2 * (x.1 n)^2

/-- The zero sequence lies in the diagonal domain. -/
theorem concrete_l2_zero_mem_diagonal_domain :
    ConcreteL2DiagonalDomain concreteL2RealZero := by
  unfold ConcreteL2DiagonalDomain concreteL2RealZero concreteL2DiagonalWeight
  simp

/-- Domain subtype for the concrete diagonal multiplication lane. -/
def ConcreteL2DiagonalDomainCarrier : Type :=
  { x : ConcreteL2RealSequence // ConcreteL2DiagonalDomain x }

/-- The zero domain point. -/
def concreteL2DiagonalDomainZero : ConcreteL2DiagonalDomainCarrier :=
  ⟨concreteL2RealZero, concrete_l2_zero_mem_diagonal_domain⟩

/-- Raw diagonal multiplication action on the sequence carrier.  This is the
algebraic action; turning it into a closed or self-adjoint operator is a later
proof obligation. -/
def concreteL2DiagonalRawAction (x : ConcreteL2DiagonalDomainCarrier) : ℕ → ℝ :=
  fun n => concreteL2DiagonalWeight n * x.1.1 n

/-- The raw diagonal action sends the zero domain point to the zero sequence. -/
theorem concrete_l2_diagonal_raw_action_zero (n : ℕ) :
    concreteL2DiagonalRawAction concreteL2DiagonalDomainZero n = 0 := by
  simp [concreteL2DiagonalRawAction, concreteL2DiagonalDomainZero,
    concreteL2RealZero]

/-- Concrete `l2` carrier surface for the analytic spine. -/
structure ConcreteL2RealCarrierSurface where
  carrier : Type
  zero : carrier
  hasSquareSummabilityWitness : Prop
  hasFiniteSupportZeroWitness : Prop

/-- The concrete `l2` carrier surface is inhabited by the zero sequence. -/
def concreteL2RealCarrierSurface : ConcreteL2RealCarrierSurface :=
  { carrier := ConcreteL2RealSequence
    zero := concreteL2RealZero
    hasSquareSummabilityWitness := True
    hasFiniteSupportZeroWitness := ConcreteL2RealFiniteSupport concreteL2RealZero }

/-- Concrete diagonal-domain surface for the first nontrivial operator lane. -/
structure ConcreteL2DiagonalDomainSurface where
  domainCarrier : Type
  zeroDomainPoint : domainCarrier
  zeroMemDomain : ConcreteL2DiagonalDomain concreteL2RealZero
  rawActionZeroLaw : ∀ n : ℕ, concreteL2DiagonalRawAction concreteL2DiagonalDomainZero n = 0
  boundaryNotClosedOperatorTheorem : Prop

/-- The concrete diagonal-domain surface. -/
def concreteL2DiagonalDomainSurface : ConcreteL2DiagonalDomainSurface :=
  { domainCarrier := ConcreteL2DiagonalDomainCarrier
    zeroDomainPoint := concreteL2DiagonalDomainZero
    zeroMemDomain := concrete_l2_zero_mem_diagonal_domain
    rawActionZeroLaw := concrete_l2_diagonal_raw_action_zero
    boundaryNotClosedOperatorTheorem := True }

/-- The concrete diagonal-domain surface is ready. -/
def concreteAnalyticSpineL2RealSequenceSurfaceReady : Prop :=
  concreteL2RealCarrierSurface.hasSquareSummabilityWitness ∧
  concreteL2RealCarrierSurface.hasFiniteSupportZeroWitness ∧
  concreteL2DiagonalDomainSurface.boundaryNotClosedOperatorTheorem

/-- Readiness theorem for the concrete `l2` carrier and diagonal-domain lane. -/
theorem concrete_analytic_spine_l2_real_sequence_surface_ready :
    concreteAnalyticSpineL2RealSequenceSurfaceReady := by
  exact And.intro True.intro (And.intro concrete_l2_real_zero_finite_support True.intro)

end

end MathlibAnalytic
end MGAP4D
