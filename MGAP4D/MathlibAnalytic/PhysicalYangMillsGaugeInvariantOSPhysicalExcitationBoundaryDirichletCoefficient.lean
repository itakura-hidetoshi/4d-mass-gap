import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableCenteredPhysicalExcitationOperator
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableCenteredBoundaryDirichletRate
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance physicalExcitationDirichletSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance physicalExcitationDirichletSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalExcitationDirichletSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalExcitationDirichletSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalExcitationDirichletSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalExcitationDirichletSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

set_option maxHeartbeats 800000

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Intrinsic finite Wilson Dirichlet coefficient read directly from the actual
completed one-step transfer on the finite physical excitation Hilbert space.

This is not a prescribed mass or decay constant.  It is definitionally the
squared norm defect of the theorem-generated physical excitation operator. -/
noncomputable def physicalExcitationDirichletCoefficient
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) : ℝ :=
  1 - ‖A.physicalExcitationOneStepOperator n‖ ^ 2

/-- The physical-excitation definition is exactly #1514's intrinsic centered
Dirichlet coefficient because #1516 proves equality of the two operator norms. -/
@[simp] theorem physicalExcitationDirichletCoefficient_eq_centeredTransferFactor
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.physicalExcitationDirichletCoefficient n =
      1 - (A.centeredTransferFactor n) ^ 2 := by
  unfold physicalExcitationDirichletCoefficient
  rw [A.physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor]

/-- The physical Dirichlet coefficient is strictly positive exactly when the
actual completed one-step excitation transfer is a strict contraction. -/
theorem physicalExcitationDirichletCoefficient_pos_iff_opNorm_lt_one
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    0 < A.physicalExcitationDirichletCoefficient n ↔
      ‖A.physicalExcitationOneStepOperator n‖ < 1 := by
  unfold physicalExcitationDirichletCoefficient
  have hnorm : 0 ≤ ‖A.physicalExcitationOneStepOperator n‖ :=
    norm_nonneg (A.physicalExcitationOneStepOperator n)
  constructor <;> intro h <;> nlinarith

/-- A unit upper bound on the intrinsic centered transfer norm makes the actual
physical excitation Dirichlet coefficient nonnegative. -/
theorem physicalExcitationDirichletCoefficient_nonneg_of_centeredTransferFactor_le_one
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (h : A.centeredTransferFactor n ≤ 1) :
    0 ≤ A.physicalExcitationDirichletCoefficient n := by
  rw [A.physicalExcitationDirichletCoefficient_eq_centeredTransferFactor]
  have h0 := A.centeredTransferFactor_nonneg n
  nlinarith

/-- #1514's literal compact-Haar shared-boundary Poincare inequality has
coefficient exactly `1 - ||T_n^exc||^2`, where `T_n^exc` is the actual completed
finite physical excitation transfer constructed in #1516. -/
theorem centered_boundaryDirichlet_poincare_physicalExcitationCoefficient
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let Fc := Pn.vacuumCenteredCarrier F
    A.physicalExcitationDirichletCoefficient n *
        (∫ b,
          ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc b‖ ^ 2
          ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) ≤
      physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredBoundaryDirichletEnergyMassFree
        S D halfExtent N hN beta hbeta Q E R hInvariant n F := by
  dsimp only
  rw [A.physicalExcitationDirichletCoefficient_eq_centeredTransferFactor]
  exact A.centered_boundaryDirichlet_poincare n F

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate

set_option maxHeartbeats 800000

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Positive-rate data make every actual finite physical excitation Dirichlet
coefficient nonnegative. -/
theorem physicalExcitationDirichletCoefficient_nonneg
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    0 ≤ A.boundedAnalysis.physicalExcitationDirichletCoefficient n :=
  A.boundedAnalysis.physicalExcitationDirichletCoefficient_nonneg_of_centeredTransferFactor_le_one
    n (A.transferFactor_le_one n)

/-- At every finite scale, the hard strict-gap statement can be phrased without
an auxiliary rate: it is exactly positivity of the actual compact-Haar
Dirichlet coefficient, equivalently strict contraction of the completed
physical excitation transfer. -/
theorem physicalExcitationDirichletCoefficient_pos_iff
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    0 < A.boundedAnalysis.physicalExcitationDirichletCoefficient n ↔
      ‖A.boundedAnalysis.physicalExcitationOneStepOperator n‖ < 1 :=
  A.boundedAnalysis.physicalExcitationDirichletCoefficient_pos_iff_opNorm_lt_one n

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableCenteredOneStepOperatorDerivedRateCertificate

end MathlibAnalytic
end MGAP4D

end