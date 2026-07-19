import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityOneSingletonWitnessL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroFullCoordinateVacuumProjectionL2
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A vector fixed by two distinct coordinates and killed by every other
coordinate belongs to the corresponding two-element joint sector. -/
theorem continuousLinearMap_mem_pair_jointSectorSubmoduleL2_of_pair_profile
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (target source : ι)
    (hNe : target ≠ source)
    {f : V}
    (hTarget : Q target f = f)
    (hSource : Q source f = f)
    (hOther : ∀ edge : ι, edge ≠ target → edge ≠ source → Q edge f = 0) :
    f ∈ continuousLinearMapJointSectorSubmoduleL2 Q {target, source} := by
  rw [continuousLinearMapJointSectorSubmoduleL2_mem_iff]
  constructor
  · intro edge hEdge
    have hCases : edge = target ∨ edge = source := by
      simpa using hEdge
    rcases hCases with hEq | hEq
    · subst edge
      exact hTarget
    · subst edge
      exact hSource
  · intro edge hEdge
    apply hOther edge
    · intro hEq
      subst edge
      exact hEdge (by simp)
    · intro hEq
      subst edge
      exact hEdge (by simp)

/-- A two-element finite set has cardinality two when its entries are distinct. -/
theorem finset_pair_card_eq_two
    {ι : Type*}
    [DecidableEq ι]
    (target source : ι)
    (hNe : target ≠ source) :
    ({target, source} : Finset ι).card = 2 := by
  rw [Finset.card_insert_of_not_mem]
  · simp
  · simpa using hNe

/-- The cardinality-two projector fixes every vector with a two-coordinate
joint-sector profile. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_two_apply_eq_self_of_pair_profile
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (target source : ι)
    (hNe : target ≠ source)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    {f : V}
    (hTarget : Q target f = f)
    (hSource : Q source f = f)
    (hOther : ∀ edge : ι, edge ≠ target → edge ≠ source → Q edge f = 0) :
    continuousLinearMapCardinalitySectorProjectorL2 Q 2 hComm f = f := by
  exact
    continuousLinearMap_cardinalitySectorProjectorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
      Q 2 {target, source} hComm
      (finset_pair_card_eq_two target source hNe)
      (continuousLinearMap_mem_pair_jointSectorSubmoduleL2_of_pair_profile
        Q target source hNe hTarget hSource hOther)

/-- A nonzero two-coordinate profile witnesses nonvanishing of the
cardinality-two projector. -/
theorem continuousLinearMap_cardinalitySectorProjectorL2_two_ne_zero_of_nonzero_pair_profile
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (target source : ι)
    (hNe : target ≠ source)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    {f : V}
    (hfNonzero : f ≠ 0)
    (hTarget : Q target f = f)
    (hSource : Q source f = f)
    (hOther : ∀ edge : ι, edge ≠ target → edge ≠ source → Q edge f = 0) :
    continuousLinearMapCardinalitySectorProjectorL2 Q 2 hComm ≠ 0 := by
  intro hZero
  have hApply := congrArg (fun T : V →L[ℝ] V => T f) hZero
  have hProjectedZero :
      continuousLinearMapCardinalitySectorProjectorL2 Q 2 hComm f = 0 := by
    simpa using hApply
  have hProjectedSelf :=
    continuousLinearMap_cardinalitySectorProjectorL2_two_apply_eq_self_of_pair_profile
      Q target source hNe hComm hTarget hSource hOther
  exact hfNonzero (hProjectedSelf.symm.trans hProjectedZero)

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_cardinalityTwoPairEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- The normalized Haar mean of the rank-two Wilson energy. -/
noncomputable def specialUnitaryTwoWilsonEnergyHaarMean : ℝ :=
  ∫ g : SpecialUnitaryMatrixGroup 2,
    specialUnitaryWilsonPlaquetteEnergy 2 g
      ∂normalizedCompactHaar (SpecialUnitaryMatrixGroup 2)

/-- The centered rank-two Wilson energy read at an arbitrary physical edge. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ := by
  let f :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration → ℝ :=
    fun A =>
      specialUnitaryWilsonPlaquetteEnergy 2 (A edge) -
        specialUnitaryTwoWilsonEnergyHaarMean
  have hf : Continuous f := by
    exact
      ((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
        (continuous_apply edge)).sub continuous_const
  exact BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩

@[simp]
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_apply
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge A =
      specialUnitaryWilsonPlaquetteEnergy 2 (A edge) -
        specialUnitaryTwoWilsonEnergyHaarMean := by
  rfl

/-- A centered coordinate observable depends only on its selected physical
edge. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (A B :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration)
    (hApply : A edge = B edge) :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge A =
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge B := by
  simp only [
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_apply,
    hApply]

/-- A centered coordinate observable is constant along every different
physical-link fiber. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_offLinkFiberConstant_of_ne
    (edge source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hSource : source ≠ edge) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
      source
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge) := by
  intro A B hAgree
  apply
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
  exact hAgree edge (Ne.symm hSource)

/-- Haar averaging the centered coordinate observable in its own coordinate
gives zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_projection_self_eq_zero
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge) =
      fun _ => 0 := by
  funext A
  rw [
    continuous_compact_oriented_singleLinkHeatBathProjection_eq_haarIntegral_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      edge
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge)
      A]
  have hEnergyIntegrable :
      Integrable
        (fun g : SpecialUnitaryMatrixGroup 2 =>
          specialUnitaryWilsonPlaquetteEnergy 2 g)
        (normalizedCompactHaar (SpecialUnitaryMatrixGroup 2)) := by
    exact
      (continuous_specialUnitaryWilsonPlaquetteEnergy 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  calc
    (∫ g : SpecialUnitaryMatrixGroup 2,
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
            A edge g)
        ∂normalizedCompactHaar (SpecialUnitaryMatrixGroup 2)) =
      ∫ g : SpecialUnitaryMatrixGroup 2,
        (specialUnitaryWilsonPlaquetteEnergy 2 g -
          specialUnitaryTwoWilsonEnergyHaarMean)
        ∂normalizedCompactHaar (SpecialUnitaryMatrixGroup 2) := by
          apply integral_congr_ae
          filter_upwards [] with g
          simp [
            periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_apply,
            CompactOrientedGaugeWilsonSystem.replaceLink]
    _ =
      (∫ g : SpecialUnitaryMatrixGroup 2,
          specialUnitaryWilsonPlaquetteEnergy 2 g
          ∂normalizedCompactHaar (SpecialUnitaryMatrixGroup 2)) -
        ∫ _g : SpecialUnitaryMatrixGroup 2,
          specialUnitaryTwoWilsonEnergyHaarMean
          ∂normalizedCompactHaar (SpecialUnitaryMatrixGroup 2) := by
            rw [integral_sub hEnergyIntegrable (integrable_const _)]
    _ = 0 := by
      simp [specialUnitaryTwoWilsonEnergyHaarMean]

/-- Haar averaging a centered coordinate observable in a different coordinate
fixes it. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_projection_eq_self_of_ne
    (edge source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hSource : source ≠ edge) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        source
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge) =
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge := by
  exact
    continuous_compact_oriented_singleLinkHeatBathProjection_fixes
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem source
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_offLinkFiberConstant_of_ne
        edge source hSource)

/-- Product of two centered coordinate observables. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ :=
  periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF target *
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF source

@[simp]
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_apply
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
        target source A =
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF target A *
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF source A := by
  rfl

/-- The pair observable is nonzero whenever its two coordinates are distinct. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_ne_zero
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNe : target ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
        target source ≠ 0 := by
  intro hZero
  let A0 :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
    fun _ => 1
  let A1 :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
        A0 target specialUnitaryTwoNegativeIdentity)
      source specialUnitaryTwoNegativeIdentity
  have hAt0 := congrArg
    (fun F : BoundedContinuousFunction
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ =>
      F A0)
    hZero
  have hAt1 := congrArg
    (fun F : BoundedContinuousFunction
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ =>
      F A1)
    hZero
  have hA1Target : A1 target = specialUnitaryTwoNegativeIdentity := by
    simp [A1, A0, CompactOrientedGaugeWilsonSystem.replaceLink, hNe]
  have hA1Source : A1 source = specialUnitaryTwoNegativeIdentity := by
    simp [A1, A0, CompactOrientedGaugeWilsonSystem.replaceLink]
  simp [
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_apply,
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_apply,
    A0] at hAt0
  simp [
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_apply,
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_apply,
    hA1Target, hA1Source] at hAt1
  nlinarith

/-- A bounded continuous factor that is constant on the target fiber can be
pulled through the target-coordinate Haar average. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_mul_of_right_offLinkFiberConstant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target : C.base.geometry.Edge)
    (F G : BoundedContinuousFunction C.base.Configuration ℝ)
    (hG : C.base.OffLinkFiberConstant target G)
    (A : C.base.Configuration) :
    C.singleLinkHeatBathProjection target (F * G) A =
      C.singleLinkHeatBathProjection target F A * G A := by
  rw [
    continuous_compact_oriented_singleLinkHeatBathProjection_eq_haarIntegral_of_beta_eq_zero
      C hBeta target (F * G) A,
    continuous_compact_oriented_singleLinkHeatBathProjection_eq_haarIntegral_of_beta_eq_zero
      C hBeta target F A]
  calc
    (∫ g : C.base.Gauge,
        (F * G) (C.base.replaceLink A target g)
        ∂normalizedCompactHaar C.base.Gauge) =
      ∫ g : C.base.Gauge,
        F (C.base.replaceLink A target g) * G A
        ∂normalizedCompactHaar C.base.Gauge := by
          apply integral_congr_ae
          filter_upwards [] with g
          have hAgree :
              C.base.AgreeOffLink
                (C.base.replaceLink A target g) A target := by
            intro edge hEdge
            simp [CompactOrientedGaugeWilsonSystem.replaceLink, hEdge]
          rw [show G (C.base.replaceLink A target g) = G A from hG _ _ hAgree]
          rfl
    _ =
      (∫ g : C.base.Gauge,
        F (C.base.replaceLink A target g)
        ∂normalizedCompactHaar C.base.Gauge) * G A := by
          rw [integral_mul_const]

/-- Averaging the pair observable in its first selected coordinate gives zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_projection_target_eq_zero
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNe : target ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        target
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          target source) =
      fun _ => 0 := by
  funext A
  rw [
    continuous_compact_oriented_singleLinkHeatBathProjection_mul_of_right_offLinkFiberConstant
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      target
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF target)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF source)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_offLinkFiberConstant_of_ne
        source target hNe)
      A,
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_projection_self_eq_zero]
  simp

/-- Averaging the pair observable in its second selected coordinate gives zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_projection_source_eq_zero
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNe : target ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        source
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          target source) =
      fun _ => 0 := by
  funext A
  have hComm :
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          target source =
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          source target := by
    ext B
    simp [periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_apply,
      mul_comm]
  rw [hComm]
  exact congrFun
    (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_projection_target_eq_zero
      source target hNe.symm) A

/-- Every unselected coordinate projection fixes the pair observable. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_projection_eq_self_of_ne
    (target source edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTarget : edge ≠ target)
    (hSource : edge ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          target source) =
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
        target source := by
  apply
    continuous_compact_oriented_singleLinkHeatBathProjection_fixes
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem edge
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
        target source)
  intro A B hAgree
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_apply,
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_apply]
  congr 1
  · apply
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
    exact hAgree target (Ne.symm hTarget)
  · apply
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
    exact hAgree source (Ne.symm hSource)

/-- The Gibbs `L²` representative of a two-coordinate centered product. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
    (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
      target source)

/-- The two-link pair mode is nonzero for distinct coordinates. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_ne_zero
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNe : target ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
        target source ≠ 0 := by
  intro hZero
  have hToLp :
      BoundedContinuousFunction.toLp
          2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure
          ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
            target source) =
        BoundedContinuousFunction.toLp
          2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure
          ℝ
          0 := by
    change
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
            target source) =
        0 at hZero
    simpa [
      ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
      using hZero
  have hBCF :
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          target source = 0 :=
    (BoundedContinuousFunction.toLp_injective
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      hToLp
  exact
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_ne_zero
      target source hNe hBCF

/-- The first selected fluctuation projection fixes the pair mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_target_fluctuation_eq_self
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNe : target ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        target
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
          target source) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
        target source := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  have hProjection :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          target
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
            target source) = 0 := by
    rw [
      continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
        target
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          target source)]
    have hBCF :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
            target
            (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
              target source) = 0 := by
      ext A
      exact congrFun
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_projection_target_eq_zero
          target source hNe) A
    rw [hBCF]
    simp [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
  rw [hProjection, sub_zero]

/-- The second selected fluctuation projection fixes the pair mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_source_fluctuation_eq_self
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNe : target ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        source
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
          target source) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
        target source := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  have hProjection :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          source
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
            target source) = 0 := by
    rw [
      continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
        source
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          target source)]
    have hBCF :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
            source
            (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
              target source) = 0 := by
      ext A
      exact congrFun
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_projection_source_eq_zero
          target source hNe) A
    rw [hBCF]
    simp [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
  rw [hProjection, sub_zero]

/-- Every unselected fluctuation projection annihilates the pair mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_fluctuation_eq_zero_of_ne
    (target source edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTarget : edge ≠ target)
    (hSource : edge ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
          target source) = 0 := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  have hProjection :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
            target source) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
          target source := by
    rw [
      continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          target source)]
    have hBCF :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
            edge
            (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
              target source) =
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
            target source := by
      ext A
      exact congrFun
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_projection_eq_self_of_ne
          target source edge hTarget hSource) A
    rw [hBCF]
  rw [hProjection, sub_self]

/-- Every distinct pair mode belongs to its two-coordinate joint sector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_twoLinkPairModeL2_mem_pair_fluctuationJointSector
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNe : target ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
        target source ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        {target, source} := by
  rw [continuous_compact_oriented_fluctuationJointSectorSubmoduleL2_mem_iff]
  constructor
  · intro edge hEdge
    have hCases : edge = target ∨ edge = source := by
      simpa using hEdge
    rcases hCases with hEq | hEq
    · subst edge
      exact
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_target_fluctuation_eq_self
          target source hNe
    · subst edge
      exact
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_source_fluctuation_eq_self
          target source hNe
  · intro edge hEdge
    apply
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_fluctuation_eq_zero_of_ne
        target source edge
    · intro hEq
      subst edge
      exact hEdge (by simp)
    · intro hEq
      subst edge
      exact hEdge (by simp)

/-- The actual cardinality-two projector fixes every distinct two-link pair
mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_two_apply_twoLinkPairMode_eq
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNe : target ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
          target source) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
        target source := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_apply_eq_self_of_mem_jointSector
      2 {target, source}
      (finset_pair_card_eq_two target source hNe)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_twoLinkPairModeL2_mem_pair_fluctuationJointSector
        target source hNe)

/-- There exists a second physical edge distinct from the distinguished edge. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exists_edge_ne_originAxisZeroTarget :
    ∃ source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
      source ≠ periodicHypercubicThreeOriginAxisZeroTarget := by
  letI : Nontrivial
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324]
      norm_num)
  exact exists_ne periodicHypercubicThreeOriginAxisZeroTarget

/-- A canonical noncomputably selected second physical edge. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.choose
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exists_edge_ne_originAxisZeroTarget

theorem periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne :
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget ≠
      periodicHypercubicThreeOriginAxisZeroTarget :=
  Classical.choose_spec
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exists_edge_ne_originAxisZeroTarget

/-- The actual cardinality-two projector is nonzero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_two_ne_zero :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      2 ≠ 0 := by
  let source :=
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
  have hNe :
      periodicHypercubicThreeOriginAxisZeroTarget ≠ source :=
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne.symm
  intro hZero
  have hApply := congrArg
    (fun T :
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure =>
      T
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
          periodicHypercubicThreeOriginAxisZeroTarget source))
    hZero
  have hProjectedZero :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
            periodicHypercubicThreeOriginAxisZeroTarget source) = 0 := by
    simpa using hApply
  have hProjectedSelf :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_two_apply_twoLinkPairMode_eq
      periodicHypercubicThreeOriginAxisZeroTarget source hNe
  exact
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_ne_zero
      periodicHypercubicThreeOriginAxisZeroTarget source hNe
      (hProjectedSelf.symm.trans hProjectedZero)

/-- The actual cardinality-two joint-sector sum is non-bottom. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_two_ne_bot :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
      2 ≠ ⊥ := by
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_iff_cardinalityJointSectorSumSubmoduleL2_ne_bot
      2).1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_two_ne_zero

/-- The nonzero cardinality-two projector realizes eigenvalue two through the
cardinality-sector criterion. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_two_mem_heatBathPointSpectrumL2_of_cardinalityTwoProjector :
    (2 : ℝ) ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 := by
  simpa using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_mem_heatBathPointSpectrumL2_of_fluctuationCardinalityProjectorL2_ne_zero
      2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_two_ne_zero

/-- Compact receipt for the actual beta-zero cardinality-two pair witness. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityTwoPairWitnessL2Receipt :
    Prop :=
  let source :=
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
  periodicHypercubicThreeOriginAxisZeroTarget ≠ source ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
      periodicHypercubicThreeOriginAxisZeroTarget source ≠ 0 ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
      periodicHypercubicThreeOriginAxisZeroTarget source ∈
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
      {periodicHypercubicThreeOriginAxisZeroTarget, source} ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      2
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
        periodicHypercubicThreeOriginAxisZeroTarget source) =
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
      periodicHypercubicThreeOriginAxisZeroTarget source ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      2 ≠ 0 ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
      2 ≠ ⊥ ∧
  (2 : ℝ) ∈
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2

/-- The actual beta-zero cardinality-two pair-witness receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityTwoPairWitnessL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityTwoPairWitnessL2Receipt := by
  dsimp [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityTwoPairWitnessL2Receipt]
  let source :=
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
  have hNe :
      periodicHypercubicThreeOriginAxisZeroTarget ≠ source :=
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne.symm
  exact ⟨
    hNe,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_ne_zero
      periodicHypercubicThreeOriginAxisZeroTarget source hNe,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_twoLinkPairModeL2_mem_pair_fluctuationJointSector
      periodicHypercubicThreeOriginAxisZeroTarget source hNe,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_two_apply_twoLinkPairMode_eq
      periodicHypercubicThreeOriginAxisZeroTarget source hNe,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_two_ne_zero,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_two_ne_bot,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_two_mem_heatBathPointSpectrumL2_of_cardinalityTwoProjector⟩

end

end MathlibAnalytic
end MGAP4D
