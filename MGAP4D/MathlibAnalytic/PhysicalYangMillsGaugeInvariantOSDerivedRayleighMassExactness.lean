import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedRayleighMassAttainment

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Proof-relevant exact-gap data for the actual OS Yang--Mills Hamiltonian.

The value is deliberately not numerically fixed.  An instance must provide both
sides that mathematically characterize the bottom of the non-vacuum spectrum:
a uniform Rayleigh lower bound and an actual nonzero vacuum-orthogonal state
attaining that same Rayleigh value. -/
structure PhysicalYangMillsExactMassData
    (T : P.StronglyContinuousPhysicalSemigroup) where
  value : ℝ
  state : T.closedRightHamiltonian.domain
  state_ne_zero : (state : P.PhysicalHilbert) ≠ 0
  state_orthogonal : inner ℝ (state : P.PhysicalHilbert) P.vacuum = 0
  rayleigh_attained : T.physicalYangMillsClosedRayleighQuotient state = value
  rayleigh_lower_bound :
    ∀ phi : T.closedRightHamiltonian.domain,
      (phi : P.PhysicalHilbert) ≠ 0 →
      inner ℝ (phi : P.PhysicalHilbert) P.vacuum = 0 →
      value * ‖(phi : P.PhysicalHilbert)‖ ^ 2 ≤
        inner ℝ (T.closedRightHamiltonian phi)
          (phi : P.PhysicalHilbert)

namespace PhysicalYangMillsExactMassData

/-- Exact mass is a theorem-generated projection of actual spectral data, not a
field of the certificate. -/
theorem physicalYangMillsMass_eq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (A : T.PhysicalYangMillsExactMassData) :
    T.physicalYangMillsMass = A.value := by
  exact T.physicalYangMillsMass_eq_of_uniformRayleighLowerBound_of_attained
    A.state A.state_ne_zero A.state_orthogonal A.rayleigh_attained
    A.rayleigh_lower_bound

/-- Positivity of the attained exact value follows automatically whenever the
actual variational Yang--Mills mass has already been proved positive. -/
theorem value_pos_of_physicalYangMillsMass_pos
    (T : P.StronglyContinuousPhysicalSemigroup)
    (A : T.PhysicalYangMillsExactMassData)
    (hmass : 0 < T.physicalYangMillsMass) :
    0 < A.value := by
  simpa [A.physicalYangMillsMass_eq T] using hmass

end PhysicalYangMillsExactMassData

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
