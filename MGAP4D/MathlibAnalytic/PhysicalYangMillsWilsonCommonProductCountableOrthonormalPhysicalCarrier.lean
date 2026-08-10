import MGAP4D.MathlibAnalytic.CountableHilbertBasisOrthonormalEmbedding
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

/-- A concrete sufficient condition for the common-product-to-continuum
physical carrier.

Instead of an abstract Hilbert-cardinal inequality, it asks for two directly
interpretable facts:

1. the theorem-generated Hilbert basis containing the common-product vacuum has
   a countable index type;
2. the continuum physical OS Hilbert space contains a countable orthonormal
   family whose zeroth vector is its vacuum.

The generic countable-orthonormal construction then gives the required
vacuum-preserving Hilbert isometry directly, without choosing a target Hilbert
basis and without any mass, gap, decay, coercivity, or spectral input. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonProductCountableOrthonormalCarrierData
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (P : D.OSPreHilbertData) where
  sourceBasisIndexCountable :
    Countable
      (distinguishedVectorHilbertBasis
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
          halfExtent N hN beta hbeta)
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum_norm
          halfExtent N hN beta hbeta)).Index
  continuumOrthonormal : ℕ → P.PhysicalHilbert
  continuumOrthonormal_orthonormal : Orthonormal ℝ continuumOrthonormal
  continuumOrthonormal_zero : continuumOrthonormal 0 = P.vacuum

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonProductCountableOrthonormalCarrierData

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

/-- The common-product-to-continuum physical isometry generated directly from
source basis countability and a vacuum-based countable continuum orthonormal
family. -/
noncomputable def commonEmbed
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductCountableOrthonormalCarrierData
      halfExtent N hN beta hbeta P) :
    PhysicalYangMillsEvenPeriodicWilsonInteractingBoundaryCommonHilbert
        halfExtent N hN beta hbeta →ₗᵢ[ℝ]
      P.PhysicalHilbert := by
  letI := J.sourceBasisIndexCountable
  exact
    distinguishedVectorLinearIsometryOfCountableOrthonormal
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
        halfExtent N hN beta hbeta)
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum_norm
        halfExtent N hN beta hbeta)
      J.continuumOrthonormal J.continuumOrthonormal_orthonormal

/-- The generated isometry sends the common interacting product vacuum exactly
to the continuum physical OS vacuum. -/
@[simp] theorem commonEmbed_vacuum
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductCountableOrthonormalCarrierData
      halfExtent N hN beta hbeta P) :
    J.commonEmbed
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
          halfExtent N hN beta hbeta) =
      P.vacuum := by
  letI := J.sourceBasisIndexCountable
  rw [commonEmbed,
    distinguishedVectorLinearIsometryOfCountableOrthonormal_apply]
  exact J.continuumOrthonormal_zero

/-- The countable-orthonormal criterion theorem-generates the complete single
common-product physical carrier of #1591. -/
noncomputable def toCommonProductPhysicalCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductCountableOrthonormalCarrierData
      halfExtent N hN beta hbeta P) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier
      halfExtent N hN beta hbeta P where
  commonEmbed := J.commonEmbed
  commonEmbed_vacuum := J.commonEmbed_vacuum

/-- Consequently the whole family-valued mass-free ambient carrier used by the
reverse-mass lane is generated from the countable-orthonormal criterion and the
already canonical-sign finite Wilson pullback. -/
noncomputable def toMassFreeAmbientCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductCountableOrthonormalCarrierData
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

end PhysicalYangMillsEvenPeriodicWilsonOSCommonProductCountableOrthonormalCarrierData

end

end MathlibAnalytic
end MGAP4D
