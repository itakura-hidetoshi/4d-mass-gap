import MGAP4D.MathlibAnalytic.DistinguishedVectorHilbertCardinal
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCommonProductHilbertDimensionPhysicalCarrier
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

/-- The final kinematic common-product carrier datum after eliminating the
model-facing linear isometry, Hilbert bases, basis indices, and explicit basis
index embedding.

Only one proposition remains: the Hilbert dimension of the theorem-generated
interacting common-product `L²` does not exceed that of the normalized
continuum physical OS Hilbert space.  From this cardinal inequality Mathlib
constructs an index embedding; the generic distinguished-vector theorem then
constructs the vacuum-preserving Hilbert isometry. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertCardinalCarrierData
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (P : D.OSPreHilbertData)
    (hP : P.IsNormalized) : Prop where
  hilbertDimension_le :
    DistinguishedVectorHilbertDimensionLE
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
        halfExtent N hN beta hbeta)
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum_norm
        halfExtent N hN beta hbeta)
      P.vacuum (P.norm_vacuum hP)

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertCardinalCarrierData

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
    {hP : P.IsNormalized}

/-- The basis-index embedding used in #1595 is theorem-generated from the
single Hilbert-cardinal inequality. -/
noncomputable def toHilbertDimensionCarrierData
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertCardinalCarrierData
      halfExtent N hN beta hbeta P hP) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertDimensionCarrierData
      halfExtent N hN beta hbeta P hP where
  indexEmbedding :=
    embeddingOfLiftedCardinalLE J.hilbertDimension_le

/-- The common-product-to-continuum physical linear isometry generated from the
Hilbert-cardinal inequality. -/
noncomputable def commonEmbed
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertCardinalCarrierData
      halfExtent N hN beta hbeta P hP) :
    PhysicalYangMillsEvenPeriodicWilsonInteractingBoundaryCommonHilbert
        halfExtent N hN beta hbeta →ₗᵢ[ℝ]
      P.PhysicalHilbert :=
  distinguishedVectorLinearIsometryOfDimensionLE
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
      halfExtent N hN beta hbeta)
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum_norm
      halfExtent N hN beta hbeta)
    P.vacuum (P.norm_vacuum hP)
    J.hilbertDimension_le

/-- The cardinally generated common embedding preserves the common/physical
vacuum exactly. -/
@[simp] theorem commonEmbed_vacuum
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertCardinalCarrierData
      halfExtent N hN beta hbeta P hP) :
    J.commonEmbed
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
          halfExtent N hN beta hbeta) =
      P.vacuum := by
  exact distinguishedVectorLinearIsometryOfDimensionLE_apply
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
      halfExtent N hN beta hbeta)
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum_norm
      halfExtent N hN beta hbeta)
    P.vacuum (P.norm_vacuum hP)
    J.hilbertDimension_le

/-- The Hilbert-cardinal inequality generates the complete single
common-product physical carrier of #1591. -/
noncomputable def toCommonProductPhysicalCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertCardinalCarrierData
      halfExtent N hN beta hbeta P hP) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier
      halfExtent N hN beta hbeta P where
  commonEmbed := J.commonEmbed
  commonEmbed_vacuum := J.commonEmbed_vacuum

/-- Consequently the complete family-valued mass-free finite-to-continuum
ambient carrier is theorem-generated from one Hilbert-dimension inequality plus
the already canonical-sign Wilson pullback. -/
noncomputable def toMassFreeAmbientCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertCardinalCarrierData
      halfExtent N hN beta hbeta P hP)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
      (B := Q.vacuumNormalized.toWeakStarBridge)
      (hInvariant := hInvariant) P :=
  J.toCommonProductPhysicalCarrier.toMassFreeAmbientCarrier Q hInvariant

end PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertCardinalCarrierData

end

end MathlibAnalytic
end MGAP4D
