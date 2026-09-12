import MGAP4D.MathlibAnalytic.HilbertBasisLinearIsometryEmbedding
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCommonProductPhysicalAmbientCarrier
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Hilbert-basis data sufficient to realize the theorem-generated interacting
boundary common product inside the continuum physical OS Hilbert space.

Compared with `PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier`,
this structure does **not** store a linear isometry.  It stores only:

* a Hilbert basis of the interacting common-product `L²`;
* a Hilbert basis of the continuum physical OS Hilbert space;
* one distinguished basis index for each canonical vacuum;
* an embedding of source basis indices into target basis indices which sends
  the source vacuum index to the target vacuum index.

The actual vacuum-preserving linear isometry is theorem-generated from these
pure Hilbert-dimension data by `HilbertBasisLinearIsometryEmbedding`. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertBasisCarrierData
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (P : D.OSPreHilbertData) where
  SourceIndex : Type
  TargetIndex : Type
  sourceBasis :
    HilbertBasis SourceIndex ℝ
      (PhysicalYangMillsEvenPeriodicWilsonInteractingBoundaryCommonHilbert
        halfExtent N hN beta hbeta)
  targetBasis : HilbertBasis TargetIndex ℝ P.PhysicalHilbert
  sourceVacuumIndex : SourceIndex
  targetVacuumIndex : TargetIndex
  sourceBasis_vacuum :
    sourceBasis sourceVacuumIndex =
      physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
        halfExtent N hN beta hbeta
  targetBasis_vacuum : targetBasis targetVacuumIndex = P.vacuum
  indexEmbedding : SourceIndex ↪ TargetIndex
  indexEmbedding_vacuum :
    indexEmbedding sourceVacuumIndex = targetVacuumIndex

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertBasisCarrierData

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {P : D.OSPreHilbertData}

/-- The common-product-to-physical linear isometry generated canonically from
the Hilbert-basis index embedding. -/
noncomputable def commonEmbed
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertBasisCarrierData
      halfExtent N hN beta hbeta P) :
    PhysicalYangMillsEvenPeriodicWilsonInteractingBoundaryCommonHilbert
        halfExtent N hN beta hbeta →ₗᵢ[ℝ]
      P.PhysicalHilbert :=
  hilbertBasisLinearIsometryOfEmbedding
    J.sourceBasis J.targetBasis J.indexEmbedding

/-- The theorem-generated Hilbert-basis isometry preserves the distinguished
common vacuum exactly. -/
@[simp] theorem commonEmbed_vacuum
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertBasisCarrierData
      halfExtent N hN beta hbeta P) :
    J.commonEmbed
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
          halfExtent N hN beta hbeta) =
      P.vacuum := by
  exact
    hilbertBasisLinearIsometryOfEmbedding_distinguished
      J.sourceBasis J.targetBasis J.indexEmbedding
      J.sourceVacuumIndex J.targetVacuumIndex
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
        halfExtent N hN beta hbeta)
      P.vacuum
      J.sourceBasis_vacuum J.targetBasis_vacuum J.indexEmbedding_vacuum

/-- Hilbert-basis dimension data theorem-generate the complete single
common-product physical carrier required by #1591.

All finite Wilson scale embeddings and finite-vacuum preservation are therefore
generated further downstream by the existing #1591 constructor. -/
noncomputable def toCommonProductPhysicalCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertBasisCarrierData
      halfExtent N hN beta hbeta P) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier
      halfExtent N hN beta hbeta P where
  commonEmbed := J.commonEmbed
  commonEmbed_vacuum := J.commonEmbed_vacuum

@[simp] theorem toCommonProductPhysicalCarrier_commonEmbed
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertBasisCarrierData
      halfExtent N hN beta hbeta P) :
    J.toCommonProductPhysicalCarrier.commonEmbed = J.commonEmbed :=
  rfl

/-- In particular, the entire family-valued mass-free finite-to-continuum
ambient carrier of #1578 is generated from the Hilbert-basis embedding data and
the canonical-sign coherent Wilson pullback. -/
noncomputable def toMassFreeAmbientCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertBasisCarrierData
      halfExtent N hN beta hbeta P)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
      (B := Q.vacuumNormalized.toWeakStarBridge)
      (hInvariant := hInvariant) P :=
  J.toCommonProductPhysicalCarrier.toMassFreeAmbientCarrier Q hInvariant

end PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertBasisCarrierData

end

end MathlibAnalytic
end MGAP4D
