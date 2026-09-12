import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryL2SpatialSlicePair
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundarySpatialSlicePairL2
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance osBoundaryTransferSpatialPairSideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance osBoundaryTransferSpatialPairSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryTransferSpatialPairSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryTransferSpatialPairSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryTransferSpatialPairSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryTransferSpatialPairSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryTransferSpatialPairSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Conjugate a bounded operator on the actual shared-boundary Haar `L²`
carrier to the ordered primary/antipodal spatial-slice pair coordinates.

The two coordinate maps are inverse linear isometries coming from the exact
measure-preserving boundary coordinate equivalence. -/
noncomputable def periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
    (H N : ℕ)
    (K : PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N).toContinuousLinearMap.comp
    (K.comp
      (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N).toContinuousLinearMap)

@[simp] theorem periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair_apply
    (H N : ℕ)
    (K : PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair H N K f =
      periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N
        (K
          (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N f)) := by
  rfl

/-- Conjugation by the exact boundary/pair `L²` isometries cannot increase the
operator norm. -/
theorem periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair_opNorm_le
    (H N : ℕ)
    (K : PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N) :
    ‖periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair H N K‖ ≤ ‖K‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg K)
  intro f
  change
    ‖periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N
      (K
        (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N f))‖ ≤
      ‖K‖ * ‖f‖
  rw [(periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N).norm_map]
  calc
    ‖K (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N f)‖ ≤
        ‖K‖ *
          ‖periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N f‖ :=
      K.le_opNorm _
    _ = ‖K‖ * ‖f‖ := by
      rw [(periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N).norm_map]

/-- Conjugating to endpoint-pair coordinates and then conjugating back recovers
the original boundary operator pointwise. -/
theorem periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair_recover
    (H N : ℕ)
    (K : PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N) :
    periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N
        (periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair H N K
          (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N f)) =
      K f := by
  rw [periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair_apply]
  rw [periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundary_leftInverse]
  rw [periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundary_leftInverse]

/-- The reverse operator-norm inequality follows from the explicit inverse
coordinate transport. -/
theorem periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair_opNorm_ge
    (H N : ℕ)
    (K : PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N) :
    ‖K‖ ≤ ‖periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair H N K‖ := by
  let Kp := periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair H N K
  apply ContinuousLinearMap.opNorm_le_bound K (norm_nonneg Kp)
  intro f
  calc
    ‖K f‖ =
        ‖periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N
          (Kp
            (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N f))‖ := by
      rw [periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair_recover H N K f]
    _ = ‖Kp
          (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N f)‖ :=
      (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N).norm_map _
    _ ≤ ‖Kp‖ *
        ‖periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N f‖ :=
      Kp.le_opNorm _
    _ = ‖Kp‖ * ‖f‖ := by
      rw [(periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N).norm_map]

/-- Exact operator-norm invariance under the boundary/two-endpoint coordinate
change. -/
theorem periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair_opNorm
    (H N : ℕ)
    (K : PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N) :
    ‖periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair H N K‖ = ‖K‖ :=
  le_antisymm
    (periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair_opNorm_le H N K)
    (periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair_opNorm_ge H N K)

/-- The already-canonical Wilson boundary moment, rewritten with the transfer-side
name for the same product-Haar endpoint-pair carrier. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentTransferSpatialSlicePairL2
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (hF : MemLp
      (fun b =>
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b)
      2
      (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 (halfExtent n) N :=
  periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry (halfExtent n) N
    (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
      S D halfExtent N hN beta hbeta B hInvariant n F hF)

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}

/-- The boundary transfer from an abstract gap certificate, rewritten on the
actual ordered spatial-endpoint pair carrier. -/
noncomputable def spatialSlicePairTransfer
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 (halfExtent n) N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 (halfExtent n) N :=
  periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair
    (halfExtent n) N (Q.boundaryTransfer n t)

/-- Coordinate transport preserves the boundary-transfer operator norm exactly. -/
@[simp] theorem spatialSlicePairTransfer_opNorm
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal) :
    ‖Q.spatialSlicePairTransfer n t‖ = ‖Q.boundaryTransfer n t‖ :=
  periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair_opNorm
    (halfExtent n) N (Q.boundaryTransfer n t)

/-- Hence the existing boundary-transfer contraction is inherited verbatim on
the ordered spatial-endpoint pair carrier. -/
theorem spatialSlicePairTransfer_opNorm_le
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal) :
    ‖Q.spatialSlicePairTransfer n t‖ ≤
      Real.sqrt (Q.quadraticDecayFactor t) := by
  rw [Q.spatialSlicePairTransfer_opNorm n t]
  exact Q.boundaryTransfer_opNorm_le n t

/-- The original boundary-moment intertwining identity transports exactly to
the transfer-side two-spatial-endpoint coordinates. -/
theorem spatialSlicePairTransfer_boundaryMoment_intertwining
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    let Tn := C.toPositiveTimeObservableContractionSemigroup n
    Q.spatialSlicePairTransfer n t
        (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentTransferSpatialSlicePairL2
          S D halfExtent N hN beta hbeta B hInvariant n
          (Pn.vacuumCenteredCarrier F)
          (Q.boundaryMoment_memLp n (Pn.vacuumCenteredCarrier F))) =
      physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentTransferSpatialSlicePairL2
        S D halfExtent N hN beta hbeta B hInvariant n
        (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F))
        (Q.boundaryMoment_memLp n
          (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F))) := by
  dsimp only
  unfold spatialSlicePairTransfer
  unfold physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentTransferSpatialSlicePairL2
  rw [periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair_apply]
  rw [periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundary_leftInverse]
  rw [Q.boundaryMoment_intertwining n t F]

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate

/-- Audit-visible statement that the shared-boundary transfer language moves to
the two-spatial-endpoint carrier with no loss in operator norm. -/
structure PhysicalYangMillsOSBoundaryTransferSpatialSlicePairPackage
    (H N : ℕ) : Prop where
  normInvariant :
    ∀ K : PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N,
      ‖periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair H N K‖ = ‖K‖

/-- Construct the boundary-transfer coordinate-change package. -/
theorem physicalYangMillsOSBoundaryTransferSpatialSlicePairPackage
    (H N : ℕ) :
    PhysicalYangMillsOSBoundaryTransferSpatialSlicePairPackage H N :=
  { normInvariant :=
      periodicHypercubicEvenBoundaryL2OperatorToSpatialSlicePair_opNorm H N }

end MathlibAnalytic
end MGAP4D

end
