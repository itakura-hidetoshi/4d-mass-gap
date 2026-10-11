import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalAllLinkPairHaarConstantCollapse
import Mathlib.Tactic

/-!
# P4-Q2-CL: exact original Wilson bounded-core Riesz kernel and full-L² obstruction

CK proved that vanishing literal original Wilson Haar reference energy on the
ACTUAL bounded strongly measurable concrete core forces pair-Haar-a.e.
constancy. This module upgrades that conclusion to an exact equality of
SUBMODULES in the ORIGINAL physical joint L² Hilbert space:

  ker(A_W) ⊓ range(bounded Wilson core → physical joint L²) = constant line.

It first proves the selected bounded concrete observable and its actual
physical L² class agree a.e.; the constant line itself lies in the
bounded-core image. An equivalent original-core zero-energy criterion,
strict nonconstant-core positivity, and an exact full-kernel obstruction
then follow from CK together with the existing continuous extension.

IMPORTANT: density of the bounded core in general joint L² does NOT imply
density of its intersection with ker(A_W). The obstruction is precisely a
hypothetical physical joint L² zero-energy vector that has NO bounded-core
representative. No full-space ker(A_W)=constants, positive reverse
coercivity, spectral-gap or continuum mass-gap theorem is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Core" =>
  p4Q2BP_originalBoundedStronglyMeasurableCore H N
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "muPhys" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta
local notation "T" =>
  p4Q2BR_originalCoreToPhysicalL2Linear H N hN beta hbeta
local notation "Img" => LinearMap.range T
local notation "V" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    H N hN beta hbeta
local notation "W" =>
  p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta
local notation "Q" =>
  p4Q2BX_originalFullJointQuadratic H N hN beta hbeta
local notation "Qcore" =>
  p4Q2BP_originalCoreReference H N hN beta hbeta

/-- The original concrete Wilson bounded core represents the SAME function
in its original physical Hilbert L² quotient, pairwise a.e. under muPhys. -/
theorem p4Q2CL_originalBoundedCoreToPhysical_coeFn
    (F : Core) :
    ((T F : J) : Joint → ℝ) =ᵐ[muPhys] (F.1 : Joint → ℝ) := by
  change
    (((p4Q2BR_originalCore_memLp H N hN beta hbeta F).toLp F.1 : J) :
      Joint → ℝ) =ᵐ[muPhys] (F.1 : Joint → ℝ)
  exact MemLp.coeFn_toLp (p4Q2BR_originalCore_memLp H N hN beta hbeta F)

/-- The original full-space quadratic extension agrees with the literal
Wilson bounded-core energy for ANY concrete representative F, not just
for BV's canonical chosen representative. -/
theorem p4Q2CL_originalFullQuadratic_eq_literalCore
    (F : Core) :
    Q (T F) = Qcore F := by
  let x : Img := ⟨T F, LinearMap.mem_range.mpr ⟨F, rfl⟩⟩
  have hq := p4Q2BX_originalFullJointQuadratic_on_range
    H N hN beta hbeta x
  have hrep : T (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x) =
      T F := by
    simpa [x] using p4Q2BV_originalCoreRepresentative_spec H N hN beta hbeta x
  have hcongr :=
    p4Q2BS_originalCoreReference_congr_physicalL2
      H N hN beta hbeta
      (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x)
      F hrep
  calc
    Q (T F) = Q (x : J) := rfl
    _ = Qcore (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x) := hq
    _ = Qcore F := hcongr

/-- CK's representative-level theorem becomes a real physical Hilbert
subspace membership statement for every bounded-core Riesz zero mode. -/
theorem p4Q2CL_originalRieszCoreKernel_mem_constantLine
    (x : Img) (hx : W (x : J) = 0) :
    (x : J) ∈ V := by
  let F : Core := p4Q2BV_originalCoreRepresentative H N hN beta hbeta x
  have hQzero : Qcore F = 0 := by
    have hzero :=
      (p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero
        H N hN beta hbeta (x : J)).2 hx
    rw [p4Q2BX_originalFullJointQuadratic_on_range] at hzero
    exact hzero
  obtain ⟨c, hc⟩ :=
    p4Q2CK_originalCoreZero_physicalJoint_aeConst
      H N hN beta hbeta F hQzero
  have hL2Rep :
      (T F : J) = (x : J) :=
    p4Q2BV_originalCoreRepresentative_spec H N hN beta hbeta x
  have hrepresented :
      ((x : J) : Joint → ℝ) =ᵐ[muPhys] (fun _ => c) := by
    have h := (p4Q2CL_originalBoundedCoreToPhysical_coeFn
      H N hN beta hbeta F).trans hc
    rw [hL2Rep] at h
    exact h
  have hEzero :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_ae_const
      H N hN beta hbeta (x : J)).2 ⟨c, hrepresented⟩
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_mem_constantLine
      H N hN beta hbeta (x : J)).1 hEzero

/-- The canonical constant-one vector of the ACTUAL physical Wilson joint
Hilbert space is in the range of its concrete bounded observable core. -/
theorem p4Q2CL_originalJointConstantOne_mem_boundedCoreRange :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
        H N hN beta hbeta 1 ∈ Img := by
  let F : Core :=
    ⟨fun _ : Joint => (1 : ℝ), ⟨stronglyMeasurable_const,
      ⟨1, by intro z; simp⟩⟩⟩
  have hrep :
      (T F : J) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
          H N hN beta hbeta 1 := by
    apply Lp.ext
    exact (p4Q2CL_originalBoundedCoreToPhysical_coeFn
      H N hN beta hbeta F).trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2_coeFn
        H N hN beta hbeta 1).symm
  exact LinearMap.mem_range.mpr ⟨F, hrep⟩

/-- The entire genuine original Wilson physical constant LINE, not only
its unit generator, consists of bounded core image classes. -/
theorem p4Q2CL_originalJointConstantLine_le_boundedCoreRange :
    V ≤ Img := by
  intro x hx
  change x ∈
    (ℝ ∙ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
      H N hN beta hbeta 1) at hx
  rcases Submodule.mem_span_singleton.mp hx with ⟨c, hc⟩
  rw [← hc]
  exact (LinearMap.range T).smul_mem c
    (p4Q2CL_originalJointConstantOne_mem_boundedCoreRange H N hN beta hbeta)

/-- On the ORIGINAL bounded Wilson concrete core, the literal reference
energy vanishes if and only if the represented physical joint L² vector
belongs to the ACTUAL constant-line subspace. -/
theorem p4Q2CL_originalCoreReference_zero_iff_constantLine
    (F : Core) :
    Qcore F = 0 ↔ T F ∈ V := by
  have hbridge :=
    p4Q2CL_originalFullQuadratic_eq_literalCore H N hN beta hbeta F
  constructor
  · intro hzero
    have hQ : Q (T F) = 0 := hbridge.trans hzero
    have hw : W (T F) = 0 :=
      (p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero
        H N hN beta hbeta (T F)).1 hQ
    let x : Img := ⟨T F, LinearMap.mem_range.mpr ⟨F, rfl⟩⟩
    exact p4Q2CL_originalRieszCoreKernel_mem_constantLine
      H N hN beta hbeta x hw
  · intro hc
    have hw : W (T F) = 0 :=
      p4Q2CC_originalWilsonRiesz_zero_of_mem_constantLine
        H N hN beta hbeta (T F) hc
    have hQ : Q (T F) = 0 :=
      (p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero
        H N hN beta hbeta (T F)).2 hw
    exact hbridge.symm.trans hQ

/-- CK + the actual physical quotient: a strictly nonconstant bounded
original Wilson observable has STRICTLY POSITIVE literal Haar reference.
No uniform positive coefficient is claimed. -/
theorem p4Q2CL_originalCoreReference_strict_of_not_constantAE
    (F : Core)
    (hnot : ¬ ∃ c : ℝ, (F.1 : Joint → ℝ) =ᵐ[muPair] (fun _ => c)) :
    0 < Qcore F := by
  have hqne : Qcore F ≠ 0 := by
    intro heq
    exact hnot (p4Q2CK_originalCoreZero_pairHaar_aeConst
      H N hN beta hbeta F heq)
  have hnonneg : 0 ≤ Qcore F :=
    p4Q2BQ_originalCoreReference_nonneg H N hN beta hbeta F
  rcases lt_or_eq_of_le hnonneg with hpos | heq
  · exact hpos
  · exact False.elim (hqne heq.symm)

/-- The exact qualitative original Wilson Riesz kernel on the genuine
BOUNDED-CORE IMAGE is the physical constant-line sector, as a submodule
equality inside the original joint Hilbert L². -/
theorem p4Q2CL_originalRieszKernel_inf_boundedCoreRange_eq_constantLine :
    (W : J →ₗ[ℝ] J).ker ⊓ Img = V := by
  apply le_antisymm
  · intro x hx
    have hw : W x = 0 := LinearMap.mem_ker.mp hx.1
    exact p4Q2CL_originalRieszCoreKernel_mem_constantLine
      H N hN beta hbeta ⟨x, hx.2⟩ hw
  · intro x hx
    exact ⟨p4Q2BZ_jointConstantLine_le_originalRiesz_ker
      H N hN beta hbeta hx,
      p4Q2CL_originalJointConstantLine_le_boundedCoreRange
        H N hN beta hbeta hx⟩

/-- No nonconstant physical Wilson zero mode may have an original bounded
concrete representative. This isolates the precise genuinely unbounded
full-L² obstruction that CK alone cannot exclude. -/
theorem p4Q2CL_nonconstantRieszKernel_not_in_boundedCoreRange
    (x : J) (hx : W x = 0) (hnot : x ∉ V) :
    x ∉ Img := by
  intro hxRange
  exact hnot (p4Q2CL_originalRieszCoreKernel_mem_constantLine
    H N hN beta hbeta ⟨x, hxRange⟩ hx)

/-- An exact, unconditional criterion for the remaining kernel equality:
every full physical Riesz zero mode would have to admit a bounded concrete
representative. Density of ALL bounded cores is NOT this condition. -/
theorem p4Q2CL_originalRieszKernel_eq_constantLine_iff_ker_le_boundedRange :
    (W : J →ₗ[ℝ] J).ker = V ↔
      (W : J →ₗ[ℝ] J).ker ≤ Img := by
  constructor
  · intro hker
    rw [hker]
    exact p4Q2CL_originalJointConstantLine_le_boundedCoreRange
      H N hN beta hbeta
  · intro hbounded
    apply le_antisymm ?_
      (p4Q2BZ_jointConstantLine_le_originalRiesz_ker H N hN beta hbeta)
    intro x hx
    have hw : W x = 0 := LinearMap.mem_ker.mp hx
    exact p4Q2CL_originalRieszCoreKernel_mem_constantLine
      H N hN beta hbeta ⟨x, hbounded hx⟩ hw

/-- If there IS an extra full physical L² kernel direction, that direction
must be genuinely outside the original bounded observable core image. This
does not infer such a direction exists. -/
theorem p4Q2CL_originalRieszKernel_ne_constantLine_has_nonbounded_witness
    (hneq : (W : J →ₗ[ℝ] J).ker ≠ V) :
    ∃ x : J, W x = 0 ∧ x ∉ V ∧ x ∉ Img := by
  obtain ⟨x, hnot, hq⟩ :=
    p4Q2CC_originalWilsonKernel_ne_constantLine_has_zero_witness
      H N hN beta hbeta hneq
  have hw : W x = 0 :=
    (p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero
      H N hN beta hbeta x).1 hq
  exact ⟨x, hw, hnot,
    p4Q2CL_nonconstantRieszKernel_not_in_boundedCoreRange
      H N hN beta hbeta x hw hnot⟩

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
