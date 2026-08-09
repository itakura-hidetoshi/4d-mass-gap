import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonPositiveHalfCanonicalSign
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonMassFreeAmbientTwoStepRecovery
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

/-- The theorem-generated interacting boundary-product common Hilbert space for
all finite Wilson scales. -/
abbrev PhysicalYangMillsEvenPeriodicWilsonInteractingBoundaryCommonHilbert
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n) :=
  Lp ℝ 2
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct
      halfExtent N hN beta hbeta)

/-- A single model-facing realization of the theorem-generated interacting
boundary common carrier inside a physical continuum OS Hilbert space.

This is strictly smaller than the family-valued mass-free ambient hypothesis of
`PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier`: there is only one
isometric map, from the common product `L²`, and it is required to identify only
the distinguished common vacuum with the continuum vacuum.  All scale-wise
finite embeddings and their vacuum laws are generated downstream. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (P : D.OSPreHilbertData) where
  commonEmbed :
    PhysicalYangMillsEvenPeriodicWilsonInteractingBoundaryCommonHilbert
        halfExtent N hN beta hbeta →ₗᵢ[ℝ]
      P.PhysicalHilbert
  commonEmbed_vacuum :
    commonEmbed
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
          halfExtent N hN beta hbeta) =
      P.vacuum

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier

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

/-- Compose the canonical-sign finite Wilson common-carrier isometry with the
single common-product-to-physical isometry. -/
noncomputable def finitePhysicalLinearIsometry
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier
      halfExtent N hN beta hbeta P)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta
          Q.vacuumNormalized.toWeakStarBridge hInvariant n →ₗᵢ[ℝ]
      P.PhysicalHilbert :=
  J.commonEmbed.comp
    (Q.vacuumNormalized.physicalHilbertInteractingBoundaryCommonLinearIsometry
      hInvariant n)

@[simp] theorem finitePhysicalLinearIsometry_norm
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier
      halfExtent N hN beta hbeta P)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta
        Q.vacuumNormalized.toWeakStarBridge hInvariant n) :
    ‖J.finitePhysicalLinearIsometry Q hInvariant n phi‖ = ‖phi‖ :=
  LinearIsometry.norm_map _ phi

/-- Scale-wise finite-vacuum preservation is no longer an independent input:
it follows from canonical sign normalization, the common-product vacuum theorem,
and the single physical common-carrier vacuum law. -/
theorem finitePhysicalLinearIsometry_vacuum
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier
      halfExtent N hN beta hbeta P)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    J.finitePhysicalLinearIsometry Q hInvariant n
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
          S D halfExtent N hN beta hbeta
            Q.vacuumNormalized.toWeakStarBridge hInvariant n) =
      P.vacuum := by
  change
    J.commonEmbed
        (Q.vacuumNormalized.physicalHilbertInteractingBoundaryCommonLinearIsometry
          hInvariant n
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
            S D halfExtent N hN beta hbeta
              Q.vacuumNormalized.toWeakStarBridge hInvariant n)) =
      P.vacuum
  rw [Q.vacuumNormalized_commonEmbedding_vacuum hInvariant n]
  exact J.commonEmbed_vacuum

/-- The single common-product physical realization theorem-generates the entire
family-valued mass-free ambient carrier required by the two-step reverse-mass
lane.

In particular, neither a scale-wise family of physical embeddings nor a
scale-wise family of vacuum compatibility hypotheses remains model-facing. -/
noncomputable def toMassFreeAmbientCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier
      halfExtent N hN beta hbeta P)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
      (B := Q.vacuumNormalized.toWeakStarBridge)
      (hInvariant := hInvariant) P where
  embed n :=
    (J.finitePhysicalLinearIsometry Q hInvariant n).toContinuousLinearMap
  embed_norm n phi :=
    J.finitePhysicalLinearIsometry_norm Q hInvariant n phi
  embed_vacuum n :=
    J.finitePhysicalLinearIsometry_vacuum Q hInvariant n

@[simp] theorem toMassFreeAmbientCarrier_embed
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier
      halfExtent N hN beta hbeta P)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta
        Q.vacuumNormalized.toWeakStarBridge hInvariant n) :
    J.toMassFreeAmbientCarrier Q hInvariant |>.embed n phi =
      J.commonEmbed
        (Q.vacuumNormalized.physicalHilbertInteractingBoundaryCommonLinearIsometry
          hInvariant n phi) :=
  rfl

end PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier

end

end MathlibAnalytic
end MGAP4D
