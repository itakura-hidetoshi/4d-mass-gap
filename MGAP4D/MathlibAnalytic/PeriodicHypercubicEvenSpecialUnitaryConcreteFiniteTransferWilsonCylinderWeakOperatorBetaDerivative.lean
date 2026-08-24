import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderBetaDerivative
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter Set
open scoped InnerProductSpace Topology

noncomputable section

/-- Weak operator derivative carrier for the physical one-slice Hilbert space.
The scalar family `coeff beta f g` is interpreted as the matrix coefficient of
an operator family, while `D` is a genuine continuous linear operator proposed
as its derivative.  This formulation is deliberately weaker than strong or
operator-norm differentiability and therefore matches exactly the information
proved by differentiating every physical matrix coefficient. -/
def periodicHypercubicEvenSpecialUnitaryHasWeakPhysicalOperatorDerivAt
    (H N : ℕ)
    (coeff : ℝ →
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N → ℝ)
    (D : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)
    (beta : ℝ) : Prop :=
  ∀ f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N,
    HasDerivAt
      (fun beta' : ℝ => coeff beta' f g)
      (inner ℝ (D f) g)
      beta

/-- The operator represented by the beta derivative is minus the complete
Wilson cylinder-action insertion operator. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDerivativeOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  -periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
    H N hN beta hbeta

/-- At nonnegative beta the canonical endpoint coefficient family is literally
the matrix-coefficient family of the genuine physical positive-half transfer
operator.  This is the identification that turns the total scalar beta-family
used for differentiation into a weak operator family on the physical Hilbert
space. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude_eq_physicalTransferCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude
        H N beta f g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta f) g :=
  periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude_eq_physicalTransfer_inner
    H N hN beta hbeta f g

/-- Weak-operator beta derivative of the finite-volume physical positive-half
transfer family at every strictly positive beta.

The coefficient family is the canonical literal endpoint amplitude, which is
already equal to the physical transfer matrix coefficient for every
nonnegative beta.  Its derivative is represented by the genuine continuous
linear operator `- O_cyl,beta`.  No strong-operator or operator-norm limit is
asserted here. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransfer_hasWeakOperatorDerivAt_beta
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 < beta) :
    periodicHypercubicEvenSpecialUnitaryHasWeakPhysicalOperatorDerivAt
      H N
      (fun beta' f g =>
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude
          H N beta' f g)
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDerivativeOperator
        H N hN beta hbeta.le)
      beta := by
  intro f g
  have h :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude_hasDerivAt_beta_eq_neg_physicalWilsonActionInsertion
      H N hN beta hbeta f g
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDerivativeOperator]
    using h

/-- Expanded matrix-coefficient form of the weak operator derivative.  This is
the operator-level packaging of the beta-variation identity: for every pair of
physical states, the derivative is the matrix coefficient of one and the same
continuous linear operator. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransfer_weakDerivativeCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    HasDerivAt
      (fun beta' : ℝ =>
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude
          H N beta' f g)
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDerivativeOperator
          H N hN beta hbeta.le f) g)
      beta :=
  periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransfer_hasWeakOperatorDerivAt_beta
    H N hN beta hbeta f g

end

end MathlibAnalytic
end MGAP4D
