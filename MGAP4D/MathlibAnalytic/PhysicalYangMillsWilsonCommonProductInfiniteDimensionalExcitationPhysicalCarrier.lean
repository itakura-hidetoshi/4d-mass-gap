import MGAP4D.MathlibAnalytic.InfiniteDimensionalHilbertOrthonormalSequence
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCommonProductVacuumOrthogonalExcitationPhysicalCarrier
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalCore
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

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

/-- The remaining common-product kinematic carrier input reduced from an
explicit continuum orthonormal excitation sequence to the single geometric
statement that the vacuum-orthogonal physical Hilbert sector is not
finite-dimensional.

Mathlib then theorem-generates an `ℕ`-indexed orthonormal sequence inside the
vacuum-orthogonal subspace.  Coercion to the ambient physical Hilbert space
preserves orthonormality, and subtype membership gives exact vacuum
orthogonality. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonProductInfiniteDimensionalExcitationCarrierData
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (P : D.OSPreHilbertData)
    (hP : P.IsNormalized) where
  vacuumOrthogonal_not_finiteDimensional :
    ¬ FiniteDimensional ℝ P.VacuumOrthogonalHilbert

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonProductInfiniteDimensionalExcitationCarrierData

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

/-- The theorem-generated orthonormal sequence in the complete
vacuum-orthogonal Hilbert subspace. -/
noncomputable def vacuumOrthogonalExcitation
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductInfiniteDimensionalExcitationCarrierData
      halfExtent N hN beta hbeta P hP) :
    ℕ → P.VacuumOrthogonalHilbert :=
  orthonormalNatSequenceOfNotFiniteDimensional
    J.vacuumOrthogonal_not_finiteDimensional

/-- The generated sequence is orthonormal inside the vacuum-orthogonal
subspace. -/
theorem vacuumOrthogonalExcitation_orthonormal
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductInfiniteDimensionalExcitationCarrierData
      halfExtent N hN beta hbeta P hP) :
    Orthonormal ℝ J.vacuumOrthogonalExcitation :=
  orthonormalNatSequenceOfNotFiniteDimensional_orthonormal
    J.vacuumOrthogonal_not_finiteDimensional

/-- Coerce the generated excitation sequence to the ambient continuum physical
Hilbert space. -/
noncomputable def excitation
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductInfiniteDimensionalExcitationCarrierData
      halfExtent N hN beta hbeta P hP) :
    ℕ → P.PhysicalHilbert :=
  fun n => (J.vacuumOrthogonalExcitation n : P.PhysicalHilbert)

/-- Subtype coercion preserves the generated orthonormal family. -/
theorem excitation_orthonormal
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductInfiniteDimensionalExcitationCarrierData
      halfExtent N hN beta hbeta P hP) :
    Orthonormal ℝ J.excitation := by
  have hSub := J.vacuumOrthogonalExcitation_orthonormal
  constructor
  · intro n
    simpa [excitation] using hSub.norm_eq_one n
  · intro m n hmn
    simpa [excitation] using hSub.inner_eq_zero hmn

/-- Every generated ambient excitation vector is exactly orthogonal to the
normalized physical vacuum because it was selected inside
`P.vacuumOrthogonal`. -/
theorem vacuum_orthogonal_excitation
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductInfiniteDimensionalExcitationCarrierData
      halfExtent N hN beta hbeta P hP)
    (n : ℕ) :
    ⟪P.vacuum, J.excitation n⟫_ℝ = 0 := by
  exact
    (P.mem_vacuumOrthogonal_iff (J.excitation n)).mp
      (J.vacuumOrthogonalExcitation n).property

/-- Non-finite-dimensionality of the vacuum-orthogonal sector therefore
constructs exactly the continuum excitation-sequence datum required by #1598. -/
noncomputable def toVacuumOrthogonalExcitationCarrierData
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductInfiniteDimensionalExcitationCarrierData
      halfExtent N hN beta hbeta P hP) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductVacuumOrthogonalExcitationCarrierData
      halfExtent N hN beta hbeta P hP where
  excitation := J.excitation
  excitation_orthonormal := J.excitation_orthonormal
  vacuum_orthogonal_excitation := J.vacuum_orthogonal_excitation

/-- Hence the complete common-product-to-continuum physical carrier is generated
from the single non-finite-dimensionality proposition. -/
noncomputable def toCommonProductPhysicalCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductInfiniteDimensionalExcitationCarrierData
      halfExtent N hN beta hbeta P hP) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier
      halfExtent N hN beta hbeta P :=
  J.toVacuumOrthogonalExcitationCarrierData.toCommonProductPhysicalCarrier

/-- And the family-valued mass-free ambient carrier follows with no new mass,
gap, decay, coercivity, spectral, or moving-time input. -/
noncomputable def toMassFreeAmbientCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductInfiniteDimensionalExcitationCarrierData
      halfExtent N hN beta hbeta P hP)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
      (B := Q.vacuumNormalized.toWeakStarBridge)
      (hInvariant := hInvariant) P :=
  J.toVacuumOrthogonalExcitationCarrierData.toMassFreeAmbientCarrier Q hInvariant

end PhysicalYangMillsEvenPeriodicWilsonOSCommonProductInfiniteDimensionalExcitationCarrierData

end

end MathlibAnalytic
end MGAP4D
