import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonVarianceTwelveColorCoercivity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalBoundedCoreKernelExactFrontier
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRieszNullspacePhysicalComparison
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-DS: extend genuine positive-beta finite-volume physical Wilson coercivity to FULL L²

DR proves a coefficient uniform in ALL bounded concrete physical Wilson
observables, comparing genuine Wilson probability variance with the true
original twelve-color conditional expectation Dirichlet energy. CL/BR prove
those observables have exact physical joint-L² representatives, and BW proves
their image dense in the full physical Hilbert space.

We prove the real Wilson probability variance of EVERY actual physical L²
representative is its squared Hilbert distance to its own genuine physical
mean constant. The existing constant-line orthogonal projection minimizes
that distance. Thus DR bounds the true constant-centered L² norm on the
bounded physical core, with a single positive real coefficient. Both the
centered squared norm and the intrinsic physical E12 Dirichlet energy are
continuous, so this same coefficient extends across the ACTUAL dense image
to the WHOLE physical ground-state joint L².

This avoids the invalid step 'density of core ⇒ density of core ∩ ker',
requires no interacting positive-beta conditional projection commutation,
and adds no extra physical law, sorry or axiom.

The coefficient depends on finite-volume H, group rank N and beta. It
does NOT prove any volume-uniform / lattice-spacing-uniform 4D gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

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

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "muW" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta
local notation "Core" =>
  p4Q2BP_originalBoundedStronglyMeasurableCore H N
local notation "T" =>
  p4Q2BR_originalCoreToPhysicalL2Linear H N hN beta hbeta
local notation "Img" => LinearMap.range T
local notation "V" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    H N hN beta hbeta
local notation "B" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
    H N hN beta hbeta
local notation "C" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
    H N hN beta hbeta
local notation "E12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H N hN beta hbeta

local instance p4Q2DS_constantLineHasOrthogonalProjection :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta).HasOrthogonalProjection := by
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta
  change W.HasOrthogonalProjection
  letI : FiniteDimensional ℝ W := by
    unfold W
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    infer_instance
  letI : CompleteSpace W := FiniteDimensional.complete ℝ W
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace W

/-- The actual Wilson probability variance equals the squared physical joint
L² norm after subtraction of the ORIGINAL WILSON mean. The constant here
is in the same physical L², not transported from pair-Haar. -/
theorem p4Q2DS_wilsonVariance_eq_trueMeanCenteredL2NormSq
    (x : J) :
    variance (x : Joint → ℝ) muW =
      ‖x - C (∫ z : Joint, (x : Joint → ℝ) z ∂muW)‖ ^ 2 := by
  letI : IsProbabilityMeasure muW :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H N hN beta hbeta
  let c : ℝ := ∫ z : Joint, (x : Joint → ℝ) z ∂muW
  let g : J := x - C c
  have hConst :
      ((C c : J) : Joint → ℝ) =ᵐ[muW] (fun _ : Joint => c) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2_coeFn
      H N hN beta hbeta c
  have hSub :
      (g : Joint → ℝ) =ᵐ[muW]
        (fun z : Joint => (x : Joint → ℝ) z - c) := by
    filter_upwards [Lp.coeFn_sub x (C c), hConst] with z hz hc
    simpa only [Pi.sub_apply, hc] using hz
  have hSquaredIntegrals :
      (∫ z : Joint, ((x : Joint → ℝ) z - c) ^ 2 ∂muW) =
        ∫ z : Joint, ((g : Joint → ℝ) z) ^ 2 ∂muW := by
    apply integral_congr_ae
    filter_upwards [hSub] with z hz
    rw [hz]
  have hL2Squared :
      (∫ z : Joint, ((g : Joint → ℝ) z) ^ 2 ∂muW) = ‖g‖ ^ 2 := by
    calc
      (∫ z : Joint, ((g : Joint → ℝ) z) ^ 2 ∂muW) =
          ∫ z : Joint, inner ℝ ((g : Joint → ℝ) z) ((g : Joint → ℝ) z)
            ∂muW := by
        congr 1
        funext z
        rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
      _ = inner ℝ g g := (L2.inner_def g g).symm
      _ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  calc
    variance (x : Joint → ℝ) muW =
        ∫ z : Joint, ((x : Joint → ℝ) z - c) ^ 2 ∂muW := by
      simpa only [c] using
        (variance_eq_integral (Lp.aestronglyMeasurable x).aemeasurable)
    _ = ‖g‖ ^ 2 := hSquaredIntegrals.trans hL2Squared
    _ = ‖x - C (∫ z : Joint, (x : Joint → ℝ) z ∂muW)‖ ^ 2 := rfl

/-- Orthogonal projection on the TRUE physical Wilson constant line
minimizes distance to every Wilson-constant, so the constant-centered
Hilbert norm is bounded by the true Wilson probability variance. -/
theorem p4Q2DS_centeredL2NormSq_le_wilsonVariance
    (x : J) :
    ‖x - B x‖ ^ 2 ≤ variance (x : Joint → ℝ) muW := by
  let c : ℝ := ∫ z : Joint, (x : Joint → ℝ) z ∂muW
  have hC : C c ∈ V := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2_eq_smul_one
      H N hN beta hbeta c]
    exact Submodule.smul_mem V c (Submodule.mem_span_singleton_self _)
  have hNorm : ‖x - B x‖ ≤ ‖x - C c‖ := by
    let W :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
        H N hN beta hbeta
    change ‖x - W.starProjection x‖ ≤ ‖x - C c‖
    rw [Submodule.starProjection_minimal (U := W) x]
    exact iInf_le (fun y : W => ‖x - (y : J)‖) ⟨C c, hC⟩
  have hsquared : ‖x - B x‖ ^ 2 ≤ ‖x - C c‖ ^ 2 := by
    nlinarith [norm_nonneg (x - B x), norm_nonneg (x - C c)]
  calc
    ‖x - B x‖ ^ 2 ≤ ‖x - C c‖ ^ 2 := hsquared
    _ = variance (x : Joint → ℝ) muW :=
      (p4Q2DS_wilsonVariance_eq_trueMeanCenteredL2NormSq
        H N hN beta hbeta x).symm

/-- Concrete DR coercivity on any actual bounded Wilson core physical
representative, using the same coefficient for ALL inputs. The positive
ENNReal coefficient is bounded by 1 before conversion to real, retaining
a finite strictly positive coefficient even without an infinity assumption. -/
private theorem p4Q2DS_corePhysicalTwelve_ge_realCenteredSq
    (k : ENNReal)
    (hDR :
      ∀ (F : Joint → ℝ) (hF : StronglyMeasurable F),
        ∀ (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
          (f : Lp ℝ 2 muPair), F =ᵐ[muPair] (f : Joint → ℝ) →
            k * ENNReal.ofReal (variance F muW) ≤
              ENNReal.ofReal
                (p4Q2BC_originalPhysicalTwelveColorResidual
                  H N hN beta hbeta F hF bound hbound))
    (F : Core) :
    (min k 1).toReal * ‖T F - B (T F)‖ ^ 2 ≤ E12 (T F) := by
  letI : IsProbabilityMeasure muPair := by infer_instance
  letI : IsProbabilityMeasure muW :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H N hN beta hbeta
  obtain ⟨hF, ⟨bound, hbound⟩⟩ := F.property
  have hPairMem : MemLp (F.1 : Joint → ℝ) 2 muPair :=
    MemLp.of_bound hF.aestronglyMeasurable bound
      (Filter.Eventually.of_forall hbound)
  let f : Lp ℝ 2 muPair := hPairMem.toLp F.1
  have hEq : (F.1 : Joint → ℝ) =ᵐ[muPair] (f : Joint → ℝ) :=
    (MemLp.coeFn_toLp hPairMem).symm
  have hDR' := hDR F.1 hF bound hbound f hEq
  have hCoreRep :=
    p4Q2BR_originalCorePhysicalL2_eq_originalAZ
      H N hN beta hbeta F hF bound hbound
  change k * ENNReal.ofReal (variance F.1 muW) ≤
    ENNReal.ofReal (E12
      (p4Q2AZ_originalJointL2 H N hN beta hbeta F.1 hF bound hbound))
    at hDR'
  rw [← hCoreRep] at hDR'
  let γ : ENNReal := min k 1
  have hγ_le : γ ≤ k := min_le_left _ _
  have hVar₀ : 0 ≤ variance F.1 muW := variance_nonneg F.1 muW
  have hPhysical₀ : 0 ≤ E12 (T F) := by
    change 0 ≤ groundStateJointColorNormalizedResidualEnergy
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
        H N hN beta hbeta) (T F)
    exact groundStateJointColorNormalizedResidualEnergy_nonneg _ _
  have hENN :
      γ * ENNReal.ofReal (variance F.1 muW) ≤
        ENNReal.ofReal (E12 (T F)) := by
    calc
      γ * ENNReal.ofReal (variance F.1 muW) =
        ENNReal.ofReal (variance F.1 muW) * γ := mul_comm _ _
      _ ≤ ENNReal.ofReal (variance F.1 muW) * k :=
        mul_le_mul_right hγ_le _
      _ = k * ENNReal.ofReal (variance F.1 muW) := mul_comm _ _
      _ ≤ ENNReal.ofReal (E12 (T F)) := hDR'
  have hReal :
      γ.toReal * variance F.1 muW ≤ E12 (T F) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hVar₀,
      ENNReal.toReal_ofReal hPhysical₀] at h
    exact h
  have hCoe :
      variance F.1 muW =
        variance ((T F : J) : Joint → ℝ) muW :=
    variance_congr
      (p4Q2CL_originalBoundedCoreToPhysical_coeFn
        H N hN beta hbeta F).symm
  have hMinimal := p4Q2DS_centeredL2NormSq_le_wilsonVariance
    H N hN beta hbeta (T F)
  calc
    γ.toReal * ‖T F - B (T F)‖ ^ 2 ≤
        γ.toReal * variance ((T F : J) : Joint → ℝ) muW :=
      mul_le_mul_of_nonneg_left hMinimal ENNReal.toReal_nonneg
    _ = γ.toReal * variance F.1 muW := by rw [hCoe]
    _ ≤ E12 (T F) := hReal

/-- Genuine FULL physical Wilson joint L² twelve-color Poincare coercivity.
A single strictly positive finite-volume coefficient controls distance to
the ACTUAL physical Wilson constant line for every joint L² equivalence
class (not merely bounded representatives). -/
theorem p4Q2DS_originalWilsonFullJointL2_physicalTwelveColor_coercive :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ x : J, κ * ‖x - B x‖ ^ 2 ≤ E12 x := by
  obtain ⟨k, hk, hDR⟩ :=
    p4Q2DR_originalWilsonPhysicalTwelveColor_coercive_bounded
      H N hN beta hbeta
  let γ : ENNReal := min k 1
  have hγPos : 0 < γ := lt_min hk (by norm_num)
  have hγTop : γ ≠ ∞ := ne_of_lt
    (lt_of_le_of_lt (min_le_right k (1 : ENNReal)) (by norm_num))
  have hγReal : 0 < γ.toReal :=
    ENNReal.toReal_pos hγPos.ne' hγTop
  refine ⟨γ.toReal, hγReal, ?_⟩
  let i : Img →L[ℝ] J := (LinearMap.range T).subtypeL
  have hd : DenseRange i :=
    p4Q2BW_originalRange_subtype_dense H N hN beta hbeta
  have hclosed : IsClosed
      {x : J | γ.toReal * ‖x - B x‖ ^ 2 ≤ E12 x} :=
    isClosed_le (by fun_prop)
      (p4Q2BZ_physicalTwelveSpatialResidualEnergy_continuous
        H N hN beta hbeta)
  intro x
  refine hd.induction_on x hclosed ?_
  intro y
  let F : Core :=
    p4Q2BV_originalCoreRepresentative H N hN beta hbeta y
  have hRep :
      T F = (y : J) :=
    p4Q2BV_originalCoreRepresentative_spec H N hN beta hbeta y
  have hCore := p4Q2DS_corePhysicalTwelve_ge_realCenteredSq
    H N hN beta hbeta k hDR F
  change γ.toReal * ‖(y : J) - B (y : J)‖ ^ 2 ≤ E12 (y : J)
  rw [← hRep]
  exact hCore

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
