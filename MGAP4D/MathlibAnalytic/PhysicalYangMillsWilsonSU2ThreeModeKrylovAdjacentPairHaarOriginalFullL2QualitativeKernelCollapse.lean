import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullPhysicalL2MarkovContraction
import Mathlib.Tactic

/-!
# P4-Q2-CO: full physical L² qualitative kernel collapse for the ORIGINAL Wilson Haar reference

CL proved the genuine Wilson Riesz kernel equals the intrinsic constant line
when intersected with the bounded concrete core image. CM proved the LITERAL
original mass-weighted Wilson Haar quadratic reference is Markovian on its
bounded core. CN established that its symmetric 1-Lipschitz truncation
extends continuously to EVERY ORIGINAL physical Wilson joint L² vector
and preserves zero energy / the Riesz kernel.

We now close both qualitative obstructions, without a reverse Poincare
coefficient or a continuum-limit claim:

1. For arbitrary physical joint L² vector x, symmetric clipping T_M(x)
   has an ACTUAL bounded strongly measurable Wilson concrete representative:
   the literal pointwise clipping of the strongly measurable Lp representative.
   This equality is proved in the original physical Lp quotient.
2. If W x = 0, every clipped T_n x therefore belongs to BOTH the bounded
   core image and the Riesz kernel, hence to CL's intrinsic constant line.
3. Countably many such a.e. constant truncations glue on the genuine
   physical joint probability space. Fix one common a.e. sample z₀; for any
   other sample z in the common full-measure set, choose finite n larger
   than BOTH |x z| and |x z₀|. The clips coincide with x at both samples,
   so x z = x z₀. This avoids assuming L²-convergence of clipping or
   extending arbitrary exceptional-point representatives.
4. Use the EXISTING physical twelve-color qualitative constancy theorem
   to conclude the FULL original physical Hilbert-space submodule identity

       ker(A_W) = V_constants.

This is qualitative fixed-volume nullspace equality for the literal
positive-beta Wilson Haar reference on the actual physical joint L².
It is NOT a volume/rank-uniform positive spectral gap, a reverse
quadratic inequality c E₁₂ ≤ Q_W with c>0, an infinite-volume conclusion,
or a continuum Yang--Mills mass-gap result.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 2400000
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

/-- A symmetric clipping leaves any scalar inside its closed [-M,M]
interval unchanged; this is purely real analysis. -/
private theorem p4Q2CO_truncate_eq_self_of_abs_le
    (M t : ℝ) (h : |t| ≤ M) :
    p4Q2CM_truncate M t = t := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  simp only [p4Q2CM_truncate, min_eq_right hu, max_eq_right hl]

/-- Countably many almost-everywhere constant symmetric clips of a real
function on a probability space force the ORIGINAL function to be a.e.
constant. There is no L²-norm convergence hypothesis or pointwise
constancy outside the common full-measure set. -/
private theorem p4Q2CO_ae_const_of_every_nat_clip_ae_const
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hclip : ∀ n : ℕ,
      ∃ c : ℝ,
        (fun z => p4Q2CM_truncate (n : ℝ) (f z)) =ᵐ[μ] fun _ => c) :
    ∃ c : ℝ, f =ᵐ[μ] fun _ => c := by
  classical
  let c : ℕ → ℝ := fun n => Classical.choose (hclip n)
  have hc : ∀ n : ℕ,
      (fun z => p4Q2CM_truncate (n : ℝ) (f z)) =ᵐ[μ] fun _ => c n :=
    fun n => Classical.choose_spec (hclip n)
  have hall : ∀ᵐ z ∂μ, ∀ n : ℕ,
      p4Q2CM_truncate (n : ℝ) (f z) = c n :=
    ae_all_iff.mpr hc
  obtain ⟨z₀, hz₀⟩ := Filter.Eventually.exists hall
  refine ⟨f z₀, ?_⟩
  filter_upwards [hall] with z hz
  obtain ⟨n, hn⟩ : ∃ n : ℕ, max |f z| |f z₀| < n :=
    exists_nat_gt (max |f z| |f z₀|)
  have hz_abs : |f z| ≤ (n : ℝ) :=
    (le_max_left _ _).trans hn.le
  have hz₀_abs : |f z₀| ≤ (n : ℝ) :=
    (le_max_right _ _).trans hn.le
  have hz_eq : p4Q2CM_truncate (n : ℝ) (f z) = f z :=
    p4Q2CO_truncate_eq_self_of_abs_le (n : ℝ) (f z) hz_abs
  have hz₀_eq : p4Q2CM_truncate (n : ℝ) (f z₀) = f z₀ :=
    p4Q2CO_truncate_eq_self_of_abs_le (n : ℝ) (f z₀) hz₀_abs
  calc
    f z = p4Q2CM_truncate (n : ℝ) (f z) := hz_eq.symm
    _ = c n := hz n
    _ = p4Q2CM_truncate (n : ℝ) (f z₀) := (hz₀ n).symm
    _ = f z₀ := hz₀_eq

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
local notation "muPhys" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta

/-- Every clipped L² element is represented by a LITERAL bounded and
strongly measurable original Wilson concrete joint observable. The physical
L² representative is strongly measurable (pinned mathlib Lp), clipping is
continuous and pointwise bounded, and Lp equality is proved a.e. -/
theorem p4Q2CO_truncatePhysicalL2_mem_originalBoundedCoreRange
    (M : ℝ) (hM : 0 ≤ M) (x : J) :
    p4Q2CN_truncatePhysicalL2 H N hN beta hbeta M hM x ∈ Img := by
  have hX : StronglyMeasurable (fun z : Joint => (x : J) z) :=
    Lp.stronglyMeasurable x
  have hG : StronglyMeasurable
      (fun z : Joint => p4Q2CM_truncate M ((x : J) z)) :=
    ((p4Q2CM_truncate_continuous M).measurable.comp
      hX.measurable).stronglyMeasurable
  let F : Core :=
    ⟨fun z : Joint => p4Q2CM_truncate M ((x : J) z),
      ⟨hG, ⟨M, fun z => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr (p4Q2CM_truncate_mem M hM ((x : J) z))⟩⟩⟩
  have hCore :
      (((T F : J) : Joint → ℝ) =ᵐ[muPhys]
        fun z : Joint => p4Q2CM_truncate M ((x : J) z)) := by
    simpa [F] using
      (p4Q2CL_originalBoundedCoreToPhysical_coeFn H N hN beta hbeta F)
  have hClip :=
    p4Q2CN_truncatePhysicalL2_coeFn H N hN beta hbeta M hM x
  have hEq : T F = p4Q2CN_truncatePhysicalL2 H N hN beta hbeta M hM x := by
    apply Lp.ext
    exact hCore.trans hClip.symm
  exact LinearMap.mem_range.mpr ⟨F, hEq⟩

/-- Every genuine physical Wilson zero-energy vector has a constant
symmetric clip at any nonnegative level M, for the ACTUAL physical joint
measure. This uses CN's all-L² Markov contraction AND CL's exact core-kernel
intersection, not an unproved global reverse Poincare inequality. -/
theorem p4Q2CO_originalRieszKernel_eachClip_aeConst
    (M : ℝ) (hM : 0 ≤ M) (x : J) (hx : W x = 0) :
    ∃ c : ℝ,
      (fun z : Joint => p4Q2CM_truncate M (x z)) =ᵐ[muPhys]
        (fun _ => c) := by
  let y : J := p4Q2CN_truncatePhysicalL2 H N hN beta hbeta M hM x
  have hy0 : W y = 0 :=
    p4Q2CN_originalRieszKernel_stable_under_truncation
      H N hN beta hbeta M hM x hx
  have hyrange : y ∈ Img :=
    p4Q2CO_truncatePhysicalL2_mem_originalBoundedCoreRange
      H N hN beta hbeta M hM x
  have hyV : y ∈ V :=
    p4Q2CL_originalRieszCoreKernel_mem_constantLine
      H N hN beta hbeta ⟨y, hyrange⟩ hy0
  have hyE :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
        H N hN beta hbeta y = 0 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_mem_constantLine
      H N hN beta hbeta y).2 hyV
  obtain ⟨c, hc⟩ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_ae_const
      H N hN beta hbeta y).1 hyE
  have hClip :=
    p4Q2CN_truncatePhysicalL2_coeFn
      H N hN beta hbeta M hM x
  exact ⟨c, hClip.symm.trans hc⟩

/-- Key qualitative closure: all original physical Wilson Riesz-kernel
vectors are a.e. constant, even when the original vectors are unbounded.
The proof intersects only COUNTABLY MANY exact full-measure clip statements. -/
theorem p4Q2CO_originalRieszKernel_ae_const
    (x : J) (hx : W x = 0) :
    ∃ c : ℝ,
      (x : Joint → ℝ) =ᵐ[muPhys] (fun _ => c) := by
  letI : IsProbabilityMeasure muPhys :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H N hN beta hbeta
  exact p4Q2CO_ae_const_of_every_nat_clip_ae_const muPhys x
    (fun n =>
      p4Q2CO_originalRieszKernel_eachClip_aeConst
        H N hN beta hbeta (n : ℝ) (Nat.cast_nonneg n) x hx)

/-- ORIGINAL positive-beta Wilson Haar Riesz full physical joint-L² kernel
is EXACTLY the intrinsic genuine physical constant line, with no extra
bounded-representative hypothesis. This is a qualitative finite-volume
identity, not a quantitative spectral-gap bound. -/
theorem p4Q2CO_originalRieszKernel_eq_constantLine :
    (W : J →ₗ[ℝ] J).ker = V := by
  apply le_antisymm ?_
    (p4Q2BZ_jointConstantLine_le_originalRiesz_ker
      H N hN beta hbeta)
  intro x hx
  have hxW : W x = 0 := LinearMap.mem_ker.mp hx
  obtain ⟨c, hc⟩ :=
    p4Q2CO_originalRieszKernel_ae_const H N hN beta hbeta x hxW
  have hE :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
        H N hN beta hbeta x = 0 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_ae_const
      H N hN beta hbeta x).2 ⟨c, hc⟩
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_mem_constantLine
      H N hN beta hbeta x).1 hE

/-- Genuine full-L² zero-energy locus: Q_W x = 0 iff x is a constant
physical joint L² vector. No positive uniform lower estimate is claimed. -/
theorem p4Q2CO_originalFullQuadratic_zero_iff_mem_constantLine
    (x : J) :
    Q x = 0 ↔ x ∈ V := by
  rw [p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero]
  change W x = 0 ↔ x ∈ V
  rw [← LinearMap.mem_ker]
  exact SetLike.ext'_iff.mp (by
    exact congrArg id (p4Q2CO_originalRieszKernel_eq_constantLine
      H N hN beta hbeta)) x

/-- Original Wilson reference is STRICTLY POSITIVE for EVERY genuinely
nonconstant physical joint L² equivalence class, not just bounded ones.
Strict positivity need not have a volume-uniform coefficient. -/
theorem p4Q2CO_originalFullQuadratic_strict_positive_off_constants
    (x : J) (hx : x ∉ V) :
    0 < Q x := by
  exact
    (p4Q2CC_originalWilsonKernel_eq_constantLine_iff_strict_energy
      H N hN beta hbeta).mp
      (p4Q2CO_originalRieszKernel_eq_constantLine
        H N hN beta hbeta) x hx

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
