import MGAP4D.MathlibAnalytic.InfiniteLinearIndependentCompletionNotFiniteDimensional
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCommonProductInfiniteDimensionalPhysicalCarrier

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The remaining common-product kinematic carrier reduced from an abstract
infinite-dimensionality proposition to actual positive-time OS observable
classes.

The model supplies a countable family of positive-time gauge-invariant
continuum observables whose classes in the separated Osterwalder--Schrader
quotient are linearly independent.  Mathlib then forces the separated quotient,
and hence its Hilbert completion, to be non-finite-dimensional. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSeparatedLinearIndependentPhysicalCarrierData
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (P : D.OSPreHilbertData)
    (hP : P.IsNormalized) where
  observable : ℕ → P.Carrier
  osClass_linearIndependent :
    LinearIndependent ℝ (fun n => P.osClass (observable n))

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSeparatedLinearIndependentPhysicalCarrierData

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

/-- The countable independent OS quotient classes force the separated
pre-Hilbert space itself to be non-finite-dimensional. -/
theorem separated_not_finiteDimensional
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSeparatedLinearIndependentPhysicalCarrierData
      halfExtent N hN beta hbeta P hP) :
    ¬ FiniteDimensional ℝ P.Separated :=
  not_finiteDimensional_of_nat_linearIndependent
    (fun n => P.osClass (J.observable n)) J.osClass_linearIndependent

/-- The canonical completion embedding transfers that non-finite-dimensionality
to the actual continuum physical OS Hilbert carrier. -/
theorem physicalHilbert_not_finiteDimensional
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSeparatedLinearIndependentPhysicalCarrierData
      halfExtent N hN beta hbeta P hP) :
    ¬ FiniteDimensional ℝ P.PhysicalHilbert := by
  change ¬ FiniteDimensional ℝ (UniformSpace.Completion P.Separated)
  exact completion_not_finiteDimensional_of_not_finiteDimensional
    J.separated_not_finiteDimensional

/-- The independent actual OS observable classes theorem-generate the single
infinite-dimensional physical Hilbert datum of #1599. -/
noncomputable def toInfiniteDimensionalPhysicalCarrierData
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSeparatedLinearIndependentPhysicalCarrierData
      halfExtent N hN beta hbeta P hP) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductInfiniteDimensionalPhysicalCarrierData
      halfExtent N hN beta hbeta P hP where
  physicalHilbert_not_finiteDimensional :=
    J.physicalHilbert_not_finiteDimensional

/-- Consequently the complete common-product physical carrier is generated
from the linearly independent separated OS observable classes. -/
noncomputable def toCommonProductPhysicalCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSeparatedLinearIndependentPhysicalCarrierData
      halfExtent N hN beta hbeta P hP) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier
      halfExtent N hN beta hbeta P :=
  J.toInfiniteDimensionalPhysicalCarrierData.toCommonProductPhysicalCarrier

/-- The generated common-product embedding still sends the canonical Wilson
common-product vacuum exactly to the normalized continuum physical vacuum. -/
@[simp] theorem toCommonProductPhysicalCarrier_commonEmbed_vacuum
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSeparatedLinearIndependentPhysicalCarrierData
      halfExtent N hN beta hbeta P hP) :
    J.toCommonProductPhysicalCarrier.commonEmbed
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
          halfExtent N hN beta hbeta) =
      P.vacuum := by
  exact J.toCommonProductPhysicalCarrier.commonEmbed_vacuum

/-- Thus the full family-valued mass-free finite-to-continuum ambient carrier is
theorem-generated from an actual countable independent family of separated OS
positive-time observable classes together with the already canonical-sign
Wilson pullback. -/
noncomputable def toMassFreeAmbientCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSeparatedLinearIndependentPhysicalCarrierData
      halfExtent N hN beta hbeta P hP)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
      (B := Q.vacuumNormalized.toWeakStarBridge)
      (hInvariant := hInvariant) P :=
  J.toInfiniteDimensionalPhysicalCarrierData.toMassFreeAmbientCarrier Q hInvariant

end PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSeparatedLinearIndependentPhysicalCarrierData

end

end MathlibAnalytic
end MGAP4D
