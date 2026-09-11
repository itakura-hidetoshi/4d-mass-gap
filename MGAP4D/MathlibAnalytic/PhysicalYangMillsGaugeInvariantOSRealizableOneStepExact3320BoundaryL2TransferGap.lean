import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableOneStepExact3320BoundaryMomentGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2TransferGap
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableOneStepBoundaryL2TransferSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableOneStepBoundaryL2TransferSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableOneStepBoundaryL2TransferSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableOneStepBoundaryL2TransferSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableOneStepBoundaryL2TransferSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableOneStepBoundaryL2TransferSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Exact one-lattice-step gap data localized to a bounded operator on the
actual shared-boundary `L²` Hilbert space.

The quantitative input is now one operator-norm estimate per lattice scale,

`‖Kₙ‖ ≤ exp (-(33/20) aₙ)`,

plus the exact intertwining of `Kₙ` with the realizable one-step Wilson OS
translation on boundary Gram moments.  The carrier-wise integrated boundary
moment inequality is theorem-generated below by `ContinuousLinearMap.le_opNorm`
and the exact `L²` norm-square identity. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2TransferGapCertificate
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
  boundaryTransfer :
    (n : ℕ) →
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N
  boundaryMoment_intertwining :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      boundaryTransfer n
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
  boundaryTransfer_opNorm_le :
    ∀ n : ℕ,
      ‖boundaryTransfer n‖ ≤ physicalYangMillsExact3320OneStepNormFactor S n

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2TransferGapCertificate

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

/-- The exact one-step boundary-transfer operator estimate generates the
carrier-wise integrated boundary Gram-moment decay of the realizable Wilson OS
route. -/
theorem oneStep_centered_boundaryMoment_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    (∫ b,
      ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        (R.realizableCarrierTranslation hInvariant n 1
          (Pn.vacuumCenteredCarrier F)) b‖ ^ 2
      ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) ≤
    (physicalYangMillsExact3320OneStepNormFactor S n) ^ 2 *
      ∫ b,
        ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          (Pn.vacuumCenteredCarrier F) b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let F0 : Pn.Carrier := Pn.vacuumCenteredCarrier F
  let F1 : Pn.Carrier :=
    R.realizableCarrierTranslation hInvariant n 1 F0
  let v0 :=
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F0
      (A.boundaryMoment_memLp n F0)
  let v1 :=
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F1
      (A.boundaryMoment_memLp n F1)
  let K := A.boundaryTransfer n
  have hintertwining : K v0 = v1 := by
    simpa [Pn, F0, F1, v0, v1, K] using
      A.boundaryMoment_intertwining n F
  have hnorm :
      ‖v1‖ ≤ physicalYangMillsExact3320OneStepNormFactor S n * ‖v0‖ := by
    calc
      ‖v1‖ = ‖K v0‖ := by rw [← hintertwining]
      _ ≤ ‖K‖ * ‖v0‖ := K.le_opNorm v0
      _ ≤ physicalYangMillsExact3320OneStepNormFactor S n * ‖v0‖ :=
        mul_le_mul_of_nonneg_right
          (A.boundaryTransfer_opNorm_le n) (norm_nonneg v0)
  have hfactor : 0 ≤ physicalYangMillsExact3320OneStepNormFactor S n :=
    (physicalYangMillsExact3320OneStepNormFactor_pos S n).le
  have hsq :
      ‖v1‖ ^ 2 ≤
        (physicalYangMillsExact3320OneStepNormFactor S n) ^ 2 * ‖v0‖ ^ 2 := by
    nlinarith [norm_nonneg v1, norm_nonneg v0]
  rw [← physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2_norm_sq
    S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F1
    (A.boundaryMoment_memLp n F1)]
  rw [← physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2_norm_sq
    S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F0
    (A.boundaryMoment_memLp n F0)]
  exact hsq

/-- Package the operator-theoretic one-step input as the boundary-moment
certificate introduced in the preceding localization stage. -/
noncomputable def toBoundaryMomentGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  oneStep_centered_boundaryMoment_le := A.oneStep_centered_boundaryMoment_le

/-- A shared-boundary `L²` one-step transfer estimate therefore reconstructs
the literal full finite Wilson Gibbs reflected-integral certificate. -/
noncomputable def toFiniteIntegralGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320FiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant :=
  A.toBoundaryMomentGapCertificate.toFiniteIntegralGapCertificate

/-- A shared-boundary `L²` one-step transfer estimate therefore reconstructs
the exact centered one-step OS norm certificate and all downstream discrete and
continuum gap machinery. -/
noncomputable def toOneStepExact3320GapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant :=
  A.toBoundaryMomentGapCertificate.toOneStepExact3320GapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2TransferGapCertificate

end MathlibAnalytic
end MGAP4D

end
