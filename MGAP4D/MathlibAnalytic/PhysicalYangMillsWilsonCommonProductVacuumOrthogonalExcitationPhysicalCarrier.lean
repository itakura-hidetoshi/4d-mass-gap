import MGAP4D.MathlibAnalytic.SeparableHilbertVacuumOrthogonalSequenceIsometry
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCommonProductHilbertDimensionPhysicalCarrier
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCommonProductPhysicalAmbientCarrier
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.SeparableMeasure
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

/-- The kinematic common-product carrier reduced to concrete continuum Hilbert
geometry.

Instead of storing a common-product-to-physical linear isometry, Hilbert bases,
a basis-index embedding, or even an abstract Hilbert-cardinal inequality, the
model supplies only a countable orthonormal excitation sequence in the
continuum physical OS Hilbert space which is orthogonal to the normalized
vacuum.

The interacting Wilson common-product `L²` is separable, hence every one of its
Hilbert bases has countable index type.  The target vacuum together with this
orthonormal excitation sequence extends by Mathlib to a target Hilbert basis.
Consequently the required vacuum-preserving common-product isometry is generated
internally. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonProductVacuumOrthogonalExcitationCarrierData
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (P : D.OSPreHilbertData)
    (hP : P.IsNormalized) where
  excitation : ℕ → P.PhysicalHilbert
  excitation_orthonormal : Orthonormal ℝ excitation
  vacuum_orthogonal_excitation :
    ∀ n, ⟪P.vacuum, excitation n⟫_ℝ = 0

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonProductVacuumOrthogonalExcitationCarrierData

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

/-- The actual interacting common-product `L²` is separable.  The coordinate
space is a countable product of finite-dimensional compact second-countable
boundary configuration spaces.  We expose the Mathlib instance chain
explicitly:

`SecondCountable + Borel → CountablyGenerated`,
`CountablyGenerated + SFinite → IsSeparable μ`,
`IsSeparable μ → SecondCountable (Lp ℝ 2 μ)`.

The infinite-product Wilson boundary law is a probability measure, hence
s-finite. -/
noncomputable local instance commonProductSeparableSpace :
    TopologicalSpace.SeparableSpace
      (PhysicalYangMillsEvenPeriodicWilsonInteractingBoundaryCommonHilbert
        halfExtent N hN beta hbeta) := by
  letI : SecondCountableTopology
      (∀ n : ℕ,
        PhysicalYangMillsEvenPeriodicWilsonInteractingBoundaryScaleConfiguration
          halfExtent N n) := by
    infer_instance
  letI : BorelSpace
      (∀ n : ℕ,
        PhysicalYangMillsEvenPeriodicWilsonInteractingBoundaryScaleConfiguration
          halfExtent N n) := by
    infer_instance
  letI : MeasurableSpace.CountablyGenerated
      (∀ n : ℕ,
        PhysicalYangMillsEvenPeriodicWilsonInteractingBoundaryScaleConfiguration
          halfExtent N n) :=
    BorelSpace.countablyGenerated
  letI : SFinite
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct
        halfExtent N hN beta hbeta) := by
    infer_instance
  letI : IsSeparable
      (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct
        halfExtent N hN beta hbeta) := by
    infer_instance
  letI : SecondCountableTopology
      (PhysicalYangMillsEvenPeriodicWilsonInteractingBoundaryCommonHilbert
        halfExtent N hN beta hbeta) := by
    infer_instance
  infer_instance

/-- The common-product-to-continuum physical linear isometry generated from the
source separability theorem and the continuum vacuum-orthogonal orthonormal
excitation sequence. -/
noncomputable def commonEmbed
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductVacuumOrthogonalExcitationCarrierData
      halfExtent N hN beta hbeta P hP) :
    PhysicalYangMillsEvenPeriodicWilsonInteractingBoundaryCommonHilbert
        halfExtent N hN beta hbeta →ₗᵢ[ℝ]
      P.PhysicalHilbert :=
  distinguishedVectorLinearIsometryOfSeparableVacuumOrthogonalSequence
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
      halfExtent N hN beta hbeta)
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum_norm
      halfExtent N hN beta hbeta)
    P.vacuum (P.norm_vacuum hP)
    J.excitation J.excitation_orthonormal J.vacuum_orthogonal_excitation

/-- The generated common embedding identifies the canonical common-product
vacuum exactly with the normalized continuum physical vacuum. -/
@[simp] theorem commonEmbed_vacuum
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductVacuumOrthogonalExcitationCarrierData
      halfExtent N hN beta hbeta P hP) :
    J.commonEmbed
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
          halfExtent N hN beta hbeta) =
      P.vacuum := by
  exact distinguishedVectorLinearIsometryOfSeparableVacuumOrthogonalSequence_apply
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
      halfExtent N hN beta hbeta)
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum_norm
      halfExtent N hN beta hbeta)
    P.vacuum (P.norm_vacuum hP)
    J.excitation J.excitation_orthonormal J.vacuum_orthogonal_excitation

/-- The vacuum-orthogonal excitation sequence theorem-generates the complete
single common-product physical carrier introduced in #1591. -/
noncomputable def toCommonProductPhysicalCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductVacuumOrthogonalExcitationCarrierData
      halfExtent N hN beta hbeta P hP) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier
      halfExtent N hN beta hbeta P where
  commonEmbed := J.commonEmbed
  commonEmbed_vacuum := J.commonEmbed_vacuum

/-- Consequently the complete family-valued mass-free finite-to-continuum
ambient carrier is theorem-generated from the continuum vacuum-orthogonal
orthonormal excitation sequence together with the already canonical-sign Wilson
pullback. -/
noncomputable def toMassFreeAmbientCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductVacuumOrthogonalExcitationCarrierData
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

end PhysicalYangMillsEvenPeriodicWilsonOSCommonProductVacuumOrthogonalExcitationCarrierData

end

end MathlibAnalytic
end MGAP4D
