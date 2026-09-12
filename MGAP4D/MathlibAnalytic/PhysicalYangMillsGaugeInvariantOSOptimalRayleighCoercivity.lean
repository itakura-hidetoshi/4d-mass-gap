import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedRayleighMassAttainment
import Mathlib.Tactic

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

/-- All coercivity constants valid on the actual nonzero vacuum-orthogonal
domain of the graph-closed OS Yang--Mills Hamiltonian.

This set is intrinsic to the constructed physical Hamiltonian.  It contains no
prescribed mass value and no finite-volume normalization constant. -/
def physicalYangMillsRayleighLowerBoundSet
    (T : P.StronglyContinuousPhysicalSemigroup) : Set ℝ :=
  {m : ℝ |
    ∀ psi : T.closedRightHamiltonian.domain,
      (psi : P.PhysicalHilbert) ≠ 0 →
      inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0 →
      m * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
        inner ℝ (T.closedRightHamiltonian psi)
          (psi : P.PhysicalHilbert)}

/-- The variationally defined physical Yang--Mills mass is itself a valid
coercivity constant on the actual excitation domain. -/
theorem physicalYangMillsMass_mem_rayleighLowerBoundSet
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.physicalYangMillsMass ∈ T.physicalYangMillsRayleighLowerBoundSet := by
  intro psi hpsi horthogonal
  exact T.physicalYangMillsMass_mul_norm_sq_le_inner
    psi hpsi horthogonal

/-- Every actual Rayleigh coercivity constant lies below the variational mass,
provided the physical excitation sector contains one genuine nonzero closed-
domain state. -/
theorem rayleighLowerBound_le_physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    {m : ℝ}
    (hm : m ∈ T.physicalYangMillsRayleighLowerBoundSet) :
    m ≤ T.physicalYangMillsMass := by
  exact T.uniformRayleighLowerBound_le_physicalYangMillsMass W hm

/-- The physical Yang--Mills mass is the **greatest** coercivity constant valid
on the actual non-vacuum Hamiltonian domain.

This is the order-theoretic form appropriate for deriving a numerical mass from
Wilson dynamics: the model should generate and optimize admissible coercivity
constants; the target number is not inserted into the definition. -/
theorem physicalYangMillsMass_isGreatest_rayleighLowerBoundSet
    (T : P.StronglyContinuousPhysicalSemigroup)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    IsGreatest T.physicalYangMillsRayleighLowerBoundSet
      T.physicalYangMillsMass := by
  refine ⟨T.physicalYangMillsMass_mem_rayleighLowerBoundSet, ?_⟩
  intro m hm
  exact T.rayleighLowerBound_le_physicalYangMillsMass W hm

/-- Any independently constructed greatest coercivity constant on the actual OS
Yang--Mills excitation domain is therefore *equal* to the variational physical
mass.

This is the normalization-free endpoint for a future exact `33/20` theorem:
first compute the optimal constant from the complete Wilson/continuum
construction, then use uniqueness of the greatest element here. -/
theorem physicalYangMillsMass_eq_of_isGreatest_rayleighLowerBoundSet
    (T : P.StronglyContinuousPhysicalSemigroup)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    {m : ℝ}
    (hm : IsGreatest T.physicalYangMillsRayleighLowerBoundSet m) :
    T.physicalYangMillsMass = m := by
  have hmassGreatest :=
    T.physicalYangMillsMass_isGreatest_rayleighLowerBoundSet W
  exact le_antisymm
    (hm.2 hmassGreatest.1)
    (hmassGreatest.2 hm.1)

/-- Proof-relevant carrier for a model-derived optimal coercivity value.  The
value is not assumed to be the physical mass; equality is a theorem below. -/
structure PhysicalYangMillsOptimalRayleighCoercivityData
    (T : P.StronglyContinuousPhysicalSemigroup) where
  value : ℝ
  greatest : IsGreatest T.physicalYangMillsRayleighLowerBoundSet value

namespace PhysicalYangMillsOptimalRayleighCoercivityData

/-- Model-derived optimal coercivity identifies the actual variational mass. -/
theorem physicalYangMillsMass_eq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (A : T.PhysicalYangMillsOptimalRayleighCoercivityData) :
    T.physicalYangMillsMass = A.value := by
  exact T.physicalYangMillsMass_eq_of_isGreatest_rayleighLowerBoundSet
    W A.greatest

end PhysicalYangMillsOptimalRayleighCoercivityData

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
