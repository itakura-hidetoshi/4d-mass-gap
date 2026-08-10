import MGAP4D.MathlibAnalytic.DistinguishedVectorHilbertBasis
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCommonProductHilbertBasisPhysicalCarrier
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace ENNReal

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

/-- The canonical constant-one vector in the interacting infinite-product
boundary carrier is normalized exactly because that product measure is a
probability measure. -/
@[simp] theorem physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum_norm
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n) :
    ‖physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
      halfExtent N hN beta hbeta‖ = 1 := by
  unfold physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
  rw [Lp.norm_const'
    (p := (2 : ENNReal))
    (μ := physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct
      halfExtent N hN beta hbeta)
    (c := (1 : ℝ)) (by norm_num) (by norm_num)]
  simp [measureReal_def]

/-- The minimal Hilbert-dimension datum left after theorem-generating both
vacuum-containing Hilbert bases.

The source and target bases themselves are no longer model-facing data:
Mathlib extends each normalized vacuum singleton to a Hilbert basis.  Nor is a
vacuum-index compatibility field needed: any index embedding is automatically
retargeted by a target transposition.

Thus the only remaining kinematic carrier input is an embedding between the two
selected Hilbert-basis index types, i.e. an explicit witness of the appropriate
Hilbert-dimension inequality. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertDimensionCarrierData
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (P : D.OSPreHilbertData)
    (hP : P.IsNormalized) where
  indexEmbedding :
    (distinguishedVectorHilbertBasis
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
        halfExtent N hN beta hbeta)
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum_norm
        halfExtent N hN beta hbeta)).Index ↪
    (distinguishedVectorHilbertBasis P.vacuum (P.norm_vacuum hP)).Index

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertDimensionCarrierData

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

/-- The common-product-to-continuum physical isometry theorem-generated from
nothing beyond the Hilbert-basis index embedding. -/
noncomputable def commonEmbed
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertDimensionCarrierData
      halfExtent N hN beta hbeta P hP) :
    PhysicalYangMillsEvenPeriodicWilsonInteractingBoundaryCommonHilbert
        halfExtent N hN beta hbeta →ₗᵢ[ℝ]
      P.PhysicalHilbert :=
  distinguishedVectorLinearIsometryOfIndexEmbedding
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
      halfExtent N hN beta hbeta)
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum_norm
      halfExtent N hN beta hbeta)
    P.vacuum (P.norm_vacuum hP) J.indexEmbedding

/-- The dimension-generated common embedding preserves the physical vacuum
exactly; the index retargeting is internal to the generic construction. -/
@[simp] theorem commonEmbed_vacuum
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertDimensionCarrierData
      halfExtent N hN beta hbeta P hP) :
    J.commonEmbed
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
          halfExtent N hN beta hbeta) =
      P.vacuum := by
  exact distinguishedVectorLinearIsometryOfIndexEmbedding_apply
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
      halfExtent N hN beta hbeta)
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum_norm
      halfExtent N hN beta hbeta)
    P.vacuum (P.norm_vacuum hP) J.indexEmbedding

/-- A Hilbert-dimension embedding therefore generates the full single
common-product physical carrier of #1591. -/
noncomputable def toCommonProductPhysicalCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertDimensionCarrierData
      halfExtent N hN beta hbeta P hP) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier
      halfExtent N hN beta hbeta P where
  commonEmbed := J.commonEmbed
  commonEmbed_vacuum := J.commonEmbed_vacuum

/-- Consequently the complete family-valued mass-free ambient carrier used by
the reverse-mass lane is theorem-generated from the dimension embedding plus
the already canonical-sign Wilson pullback. -/
noncomputable def toMassFreeAmbientCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertDimensionCarrierData
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

end PhysicalYangMillsEvenPeriodicWilsonOSCommonProductHilbertDimensionCarrierData

end

end MathlibAnalytic
end MGAP4D
