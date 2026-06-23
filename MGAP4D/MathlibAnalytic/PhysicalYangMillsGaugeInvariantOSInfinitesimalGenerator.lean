import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSStrongContinuity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The right difference quotient of the physical Euclidean-time semigroup. -/
def rightDifferenceQuotient
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (t : NNReal) : P.PhysicalHilbert :=
  (t : ℝ)⁻¹ • (T.toPhysicalSemigroup.operator t psi - psi)

/-- A vector has right infinitesimal-generator value `eta` when its semigroup
right difference quotient converges to `eta` as positive time tends to zero. -/
def HasRightGeneratorValue
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi eta : P.PhysicalHilbert) : Prop :=
  Tendsto (fun t : NNReal => T.rightDifferenceQuotient psi t)
    (nhdsWithin 0 (Ioi 0)) (nhds eta)

/-- The right infinitesimal-generator value is unique. -/
theorem hasRightGeneratorValue_unique
    (T : P.StronglyContinuousPhysicalSemigroup)
    {psi eta zeta : P.PhysicalHilbert}
    (heta : T.HasRightGeneratorValue psi eta)
    (hzeta : T.HasRightGeneratorValue psi zeta) :
    eta = zeta :=
  tendsto_nhds_unique heta hzeta

@[simp] theorem rightDifferenceQuotient_zero
    (T : P.StronglyContinuousPhysicalSemigroup) (t : NNReal) :
    T.rightDifferenceQuotient 0 t = 0 := by
  simp [rightDifferenceQuotient]

@[simp] theorem rightDifferenceQuotient_add
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi phi : P.PhysicalHilbert) (t : NNReal) :
    T.rightDifferenceQuotient (psi + phi) t =
      T.rightDifferenceQuotient psi t +
        T.rightDifferenceQuotient phi t := by
  simp only [rightDifferenceQuotient, map_add]
  module

@[simp] theorem rightDifferenceQuotient_smul
    (T : P.StronglyContinuousPhysicalSemigroup)
    (r : ℝ) (psi : P.PhysicalHilbert) (t : NNReal) :
    T.rightDifferenceQuotient (r • psi) t =
      r • T.rightDifferenceQuotient psi t := by
  simp only [rightDifferenceQuotient, map_smul]
  module

/-- The zero vector has generator value zero. -/
theorem hasRightGeneratorValue_zero
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.HasRightGeneratorValue 0 0 := by
  simpa only [HasRightGeneratorValue, rightDifferenceQuotient_zero] using
    (tendsto_const_nhds :
      Tendsto (fun _ : NNReal => (0 : P.PhysicalHilbert))
        (nhdsWithin 0 (Ioi 0)) (nhds 0))

/-- Generator values are additive. -/
theorem HasRightGeneratorValue.add
    (T : P.StronglyContinuousPhysicalSemigroup)
    {psi phi eta zeta : P.PhysicalHilbert}
    (heta : T.HasRightGeneratorValue psi eta)
    (hzeta : T.HasRightGeneratorValue phi zeta) :
    T.HasRightGeneratorValue (psi + phi) (eta + zeta) := by
  unfold HasRightGeneratorValue at heta hzeta ⊢
  simpa only [rightDifferenceQuotient_add] using heta.add hzeta

/-- Generator values respect real scalar multiplication. -/
theorem HasRightGeneratorValue.smul
    (T : P.StronglyContinuousPhysicalSemigroup)
    {psi eta : P.PhysicalHilbert}
    (r : ℝ) (heta : T.HasRightGeneratorValue psi eta) :
    T.HasRightGeneratorValue (r • psi) (r • eta) := by
  unfold HasRightGeneratorValue at heta ⊢
  simpa only [rightDifferenceQuotient_smul] using
    (tendsto_const_nhds.smul heta :
      Tendsto (fun t : NNReal => r • T.rightDifferenceQuotient psi t)
        (nhdsWithin 0 (Ioi 0)) (nhds (r • eta)))

/-- The vectors admitting a right generator value form a real linear subspace. -/
noncomputable def rightGeneratorDomain
    (T : P.StronglyContinuousPhysicalSemigroup) :
    Submodule ℝ P.PhysicalHilbert where
  carrier := {psi | ∃ eta, T.HasRightGeneratorValue psi eta}
  zero_mem' := ⟨0, T.hasRightGeneratorValue_zero⟩
  add_mem' := by
    rintro psi phi ⟨eta, heta⟩ ⟨zeta, hzeta⟩
    exact ⟨eta + zeta, heta.add T hzeta⟩
  smul_mem' := by
    rintro r psi ⟨eta, heta⟩
    exact ⟨r • eta, heta.smul T r⟩

/-- The canonical infinitesimal generator on its right-generator domain. -/
noncomputable def rightGenerator
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.rightGeneratorDomain →ₗ[ℝ] P.PhysicalHilbert where
  toFun := fun psi => Classical.choose psi.property
  map_add' := by
    intro psi phi
    apply T.hasRightGeneratorValue_unique
      (Classical.choose_spec (psi + phi).property)
    exact
      (Classical.choose_spec psi.property).add T
        (Classical.choose_spec phi.property)
  map_smul' := by
    intro r psi
    apply T.hasRightGeneratorValue_unique
      (Classical.choose_spec (r • psi).property)
    exact (Classical.choose_spec psi.property).smul T r

/-- The generator selected on the domain has the defining right-limit value. -/
theorem rightGenerator_hasRightGeneratorValue
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.rightGeneratorDomain) :
    T.HasRightGeneratorValue psi (T.rightGenerator psi) :=
  Classical.choose_spec psi.property

@[simp] theorem rightDifferenceQuotient_vacuum
    (T : P.StronglyContinuousPhysicalSemigroup) (t : NNReal) :
    T.rightDifferenceQuotient P.vacuum t = 0 := by
  simp [rightDifferenceQuotient, T.toPhysicalSemigroup.fixes_vacuum]

/-- The fixed physical vacuum has infinitesimal-generator value zero. -/
theorem hasRightGeneratorValue_vacuum_zero
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.HasRightGeneratorValue P.vacuum 0 := by
  simpa only [HasRightGeneratorValue, rightDifferenceQuotient_vacuum] using
    (tendsto_const_nhds :
      Tendsto (fun _ : NNReal => (0 : P.PhysicalHilbert))
        (nhdsWithin 0 (Ioi 0)) (nhds 0))

/-- The physical vacuum belongs to the infinitesimal-generator domain. -/
theorem vacuum_mem_rightGeneratorDomain
    (T : P.StronglyContinuousPhysicalSemigroup) :
    P.vacuum ∈ T.rightGeneratorDomain :=
  ⟨0, T.hasRightGeneratorValue_vacuum_zero⟩

/-- The infinitesimal generator annihilates the physical vacuum. -/
@[simp] theorem rightGenerator_vacuum
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.rightGenerator ⟨P.vacuum, T.vacuum_mem_rightGeneratorDomain⟩ = 0 := by
  apply T.hasRightGeneratorValue_unique
    (T.rightGenerator_hasRightGeneratorValue
      ⟨P.vacuum, T.vacuum_mem_rightGeneratorDomain⟩)
  exact T.hasRightGeneratorValue_vacuum_zero

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
