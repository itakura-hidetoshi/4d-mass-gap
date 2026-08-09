import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryHilbertSchmidtAdjointTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableBoundaryL2DerivedTransferRate
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableWilsonHSAdjointTransferSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableWilsonHSAdjointTransferSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableWilsonHSAdjointTransferSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableWilsonHSAdjointTransferSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableWilsonHSAdjointTransferSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableWilsonHSAdjointTransferSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The only remaining structural input needed to turn the theorem-generated
actual Wilson Hilbert--Schmidt operator `A_n† A_n` into the realizable boundary
transfer family is its exact intertwining with one genuine lattice-time Wilson
OS translation.

Neither the boundary operator nor its norm is supplied as data: both are fixed
by the compact-Haar Wilson kernel. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableWilsonHilbertSchmidtAdjointTransferCertificate
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  boundaryMoment_memLp :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      MemLp
        (fun b =>
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F b)
        2
        (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)
  adjointTransfer_intertwining :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAdjointTransfer
          (halfExtent n) N hN (beta n) (hbeta n)
          (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
            (Pn.vacuumCenteredCarrier F)
            (boundaryMoment_memLp n (Pn.vacuumCenteredCarrier F))) =
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          (R.realizableCarrierTranslation hInvariant n 1
            (Pn.vacuumCenteredCarrier F))
          (boundaryMoment_memLp n
            (R.realizableCarrierTranslation hInvariant n 1
              (Pn.vacuumCenteredCarrier F)))

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableWilsonHilbertSchmidtAdjointTransferCertificate

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

/-- The actual compact-Haar Wilson kernel canonically supplies the boundary
transfer family of #1506 once the single intertwining identity is proved. -/
noncomputable def toBoundaryL2TransferFamily
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableWilsonHilbertSchmidtAdjointTransferCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableBoundaryL2TransferFamily
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  boundaryMoment_memLp := A.boundaryMoment_memLp
  boundaryTransfer := fun n =>
    periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAdjointTransfer
      (halfExtent n) N hN (beta n) (hbeta n)
  boundaryMoment_intertwining := by
    intro n F
    exact A.adjointTransfer_intertwining n F

/-- Consequently the finite factor used by the corrected mass-gap spine is
exactly the operator norm of the theorem-generated Wilson `A_n† A_n`. -/
theorem transferFactor_eq_actual_adjointTransfer_opNorm
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableWilsonHilbertSchmidtAdjointTransferCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    A.toBoundaryL2TransferFamily.transferFactor n =
      ‖periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAdjointTransfer
        (halfExtent n) N hN (beta n) (hbeta n)‖ :=
  rfl

/-- The actual-kernel certificate therefore also canonically produces the
realizable one-step Wilson gap certificate with no prescribed rate. -/
noncomputable def toRealizableOneStepGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableWilsonHilbertSchmidtAdjointTransferCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant
        A.toBoundaryL2TransferFamily.transferFactor :=
  A.toBoundaryL2TransferFamily.toRealizableOneStepGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableWilsonHilbertSchmidtAdjointTransferCertificate

end MathlibAnalytic
end MGAP4D

end
