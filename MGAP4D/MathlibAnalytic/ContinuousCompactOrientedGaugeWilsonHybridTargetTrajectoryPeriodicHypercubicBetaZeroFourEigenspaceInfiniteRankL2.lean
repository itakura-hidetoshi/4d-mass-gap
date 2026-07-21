import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroThreeEigenspaceInfiniteRankL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_fourInfiniteRankEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  fun a b => instDecidableEqProd a b

/-- There exists a fourth physical edge outside the canonical three-edge sector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exists_edge_not_mem_cardinalityThreeTriple :
    ∃ fourth :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
      fourth ∉
        ({periodicHypercubicThreeOriginAxisZeroTarget,
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget,
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget} :
          Finset
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) := by
  by_contra hNo
  have hAll :
      ∀ edge :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
        edge ∈
          ({periodicHypercubicThreeOriginAxisZeroTarget,
            periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget,
            periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget} :
            Finset
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) := by
    intro edge
    by_contra hNot
    exact hNo ⟨edge, hNot⟩
  have hSub :
      (Finset.univ :
        Finset
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) ⊆
        {periodicHypercubicThreeOriginAxisZeroTarget,
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget,
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget} := by
    intro edge _hEdge
    exact hAll edge
  have hCard := Finset.card_le_card hSub
  have hUnivCard :
      (Finset.univ :
        Finset
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge).card =
        324 := by
    simpa using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324
  have hTripleCard :
      ({periodicHypercubicThreeOriginAxisZeroTarget,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget} :
        Finset
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge).card =
        3 :=
    finset_triple_card_eq_three
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne.symm
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_originAxisZeroTarget.symm
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_secondTarget.symm
  rw [hUnivCard, hTripleCard] at hCard
  norm_num at hCard

/-- A canonical noncomputably selected fourth physical edge. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.choose
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exists_edge_not_mem_cardinalityThreeTriple

theorem periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget_not_mem :
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget ∉
      ({periodicHypercubicThreeOriginAxisZeroTarget,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget} :
        Finset
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :=
  Classical.choose_spec
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exists_edge_not_mem_cardinalityThreeTriple

theorem periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget_ne_originAxisZeroTarget :
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget ≠
      periodicHypercubicThreeOriginAxisZeroTarget := by
  intro hEq
  exact periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget_not_mem
    (by
      rw [hEq]
      exact Finset.mem_insert_self _ _)

theorem periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget_ne_secondTarget :
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget := by
  intro hEq
  exact periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget_not_mem
    (by
      rw [hEq]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))

theorem periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget_ne_thirdTarget :
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget := by
  intro hEq
  exact periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget_not_mem
    (by
      rw [hEq]
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))

/-- The canonical four-edge sector. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankSector :
    Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  insert periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget
    {periodicHypercubicThreeOriginAxisZeroTarget,
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget,
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget}

@[simp]
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankSector_card :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankSector.card = 4 := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankSector
  rw [Finset.card_insert_of_notMem
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget_not_mem]
  have hTripleCard :
      ({periodicHypercubicThreeOriginAxisZeroTarget,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget} :
        Finset
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge).card =
        3 :=
    finset_triple_card_eq_three
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne.symm
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_originAxisZeroTarget.symm
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_secondTarget.symm
  omega

/-- The three-coordinate family is constant along every coordinate outside its
canonical triple. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_offLinkFiberConstant_of_ne
    (n : ℕ)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTarget : edge ≠ periodicHypercubicThreeOriginAxisZeroTarget)
    (hSource : edge ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget)
    (hThird : edge ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
      edge
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n) := by
  rw [← continuous_compact_oriented_singleLinkHeatBathProjection_fixed_iff
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem edge
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n)]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_projection_eq_self_of_ne
      n edge hTarget hSource hThird

/-- Replace the canonical fourth coordinate by the identity. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthIdentityConfiguration
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
    A periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget 1

/-- Replace the canonical fourth coordinate by the central negative identity. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthNegativeConfiguration
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
    A periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget
    specialUnitaryTwoNegativeIdentity

/-- Replacing the fourth coordinate by the identity preserves all other links. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthIdentityConfiguration_agreeOffLink
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.AgreeOffLink
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthIdentityConfiguration A)
      A periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget := by
  intro edge hEdge
  simp [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthIdentityConfiguration,
    CompactOrientedGaugeWilsonSystem.replaceLink, hEdge]

/-- Replacing the fourth coordinate by the negative identity preserves all other
links. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthNegativeConfiguration_agreeOffLink
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.AgreeOffLink
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthNegativeConfiguration A)
      A periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget := by
  intro edge hEdge
  simp [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthNegativeConfiguration,
    CompactOrientedGaugeWilsonSystem.replaceLink, hEdge]

/-- The centered fourth coordinate changes by exactly two between the negative
and identity sections. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankCenteredFourthCoordinate_negative_sub_identity_eq_two
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthNegativeConfiguration A) -
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthIdentityConfiguration A) =
      2 := by
  have hNegative :
      specialUnitaryWilsonPlaquetteEnergy 2 specialUnitaryTwoNegativeIdentity = 2 := by
    norm_num [specialUnitaryTwoNegativeIdentity,
      specialUnitaryWilsonPlaquetteEnergy, Matrix.trace, Matrix.one_apply,
      Fin.sum_univ_two]
  have hFourthNegative :
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthNegativeConfiguration A)
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget =
        specialUnitaryTwoNegativeIdentity := by
    simpa [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthNegativeConfiguration,
      CompactOrientedGaugeWilsonSystem.replaceLink]
  have hFourthIdentity :
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthIdentityConfiguration A)
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget =
        (1 : SpecialUnitaryMatrixGroup 2) := by
    simpa [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthIdentityConfiguration,
      CompactOrientedGaugeWilsonSystem.replaceLink]
  change
    (specialUnitaryWilsonPlaquetteEnergy 2
        ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthNegativeConfiguration A)
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget) -
      specialUnitaryTwoWilsonEnergyHaarMean) -
      (specialUnitaryWilsonPlaquetteEnergy 2
          ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthIdentityConfiguration A)
            periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget) -
        specialUnitaryTwoWilsonEnergyHaarMean) = 2
  rw [hFourthNegative, hFourthIdentity, hNegative,
    specialUnitaryWilsonPlaquetteEnergy_two_one]
  ring

/-- Multiply the countable three-coordinate family by the centered canonical
fourth coordinate. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF
    (n : ℕ) :
    BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n *
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget

/-- The normalized two-section difference used to recover the original
three-coordinate family. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleDifferenceLinearMap :
    BoundedContinuousFunction
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ →ₗ[ℝ]
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration → ℝ) where
  toFun H A :=
    (H (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthNegativeConfiguration A) -
      H (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthIdentityConfiguration A)) / 2
  map_add' H K := by
    funext A
    simp
    ring
  map_smul' a H := by
    funext A
    simp
    ring

/-- The two-section difference recovers the original three-coordinate family. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleDifferenceLinearMap_apply
    (n : ℕ)
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleDifferenceLinearMap
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF n)
        A =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n A := by
  let F := periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n
  let G := periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget
  let AN := periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthNegativeConfiguration A
  let AI := periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthIdentityConfiguration A
  have hFiber :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget F :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_offLinkFiberConstant_of_ne
      n periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget_ne_originAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget_ne_secondTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget_ne_thirdTarget
  have hFNegative : F AN = F A :=
    hFiber AN A
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthNegativeConfiguration_agreeOffLink A)
  have hFIdentity : F AI = F A :=
    hFiber AI A
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankFourthIdentityConfiguration_agreeOffLink A)
  have hJump : G AN - G AI = 2 := by
    simpa [G, AN, AI] using
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankCenteredFourthCoordinate_negative_sub_identity_eq_two
        A
  change (F AN * G AN - F AI * G AI) / 2 = F A
  rw [hFNegative, hFIdentity]
  calc
    (F A * G AN - F A * G AI) / 2 = F A * (G AN - G AI) / 2 := by ring
    _ = F A * 2 / 2 := by rw [hJump]
    _ = F A := by ring

/-- The four-coordinate bounded-continuous family is linearly independent. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_linearIndependent :
    LinearIndependent ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF := by
  let coeLinearMap :
      BoundedContinuousFunction
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ →ₗ[ℝ]
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration → ℝ) where
    toFun H A := H A
    map_add' H K := rfl
    map_smul' a H := rfl
  have hCoeInjective : Function.Injective coeLinearMap := by
    intro F G hFG
    ext A
    exact congrFun hFG A
  have hFunctionLinearIndependent :
      LinearIndependent ℝ
        (fun n : ℕ => fun A =>
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n A) := by
    have hMapped :=
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_linearIndependent.map'
        coeLinearMap (LinearMap.ker_eq_bot.mpr hCoeInjective)
    simpa [coeLinearMap, Function.comp_def] using hMapped
  apply
    boundedContinuousFunction_mul_right_linearIndependent_of_linearMap_recovers
      (u := periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF)
      (g := periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget)
      (recover :=
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleDifferenceLinearMap)
      (w := fun n : ℕ => fun A =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n A)
  · intro n
    funext A
    exact
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleDifferenceLinearMap_apply
        n A
  · exact hFunctionLinearIndependent

/-- The actual countable four-coordinate Gibbs `L²` family. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2
    (n : ℕ) :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF n)

/-- The actual four-coordinate Gibbs `L²` family is linearly independent. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_linearIndependent :
    LinearIndependent ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2 := by
  have hMapped :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_linearIndependent.map'
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap
      (LinearMap.ker_eq_bot.mpr
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap_injective)
  simpa [Function.comp_def,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap,
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
    using hMapped

/-- The target projection annihilates every four-coordinate family member. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_target_projection_eq_zero
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        periodicHypercubicThreeOriginAxisZeroTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF n) =
      fun _ => 0 := by
  funext A
  have hMul :=
    continuous_compact_oriented_singleLinkHeatBathProjection_mul_of_right_offLinkFiberConstant
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      periodicHypercubicThreeOriginAxisZeroTarget
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_offLinkFiberConstant_of_ne
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget_ne_originAxisZeroTarget.symm)
      A
  have hTripleZero := congrFun
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_target_projection_eq_zero
      n) A
  exact hMul.trans (by rw [hTripleZero, zero_mul])

/-- The second projection annihilates every four-coordinate family member. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_source_projection_eq_zero
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF n) =
      fun _ => 0 := by
  funext A
  have hMul :=
    continuous_compact_oriented_singleLinkHeatBathProjection_mul_of_right_offLinkFiberConstant
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_offLinkFiberConstant_of_ne
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget_ne_secondTarget.symm)
      A
  have hTripleZero := congrFun
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_source_projection_eq_zero
      n) A
  exact hMul.trans (by rw [hTripleZero, zero_mul])

/-- The third projection annihilates every four-coordinate family member. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_third_projection_eq_zero
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF n) =
      fun _ => 0 := by
  funext A
  have hMul :=
    continuous_compact_oriented_singleLinkHeatBathProjection_mul_of_right_offLinkFiberConstant
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_offLinkFiberConstant_of_ne
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget_ne_thirdTarget.symm)
      A
  have hTripleZero := congrFun
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_third_projection_eq_zero
      n) A
  exact hMul.trans (by rw [hTripleZero, zero_mul])

/-- The fourth projection annihilates every four-coordinate family member. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_fourth_projection_eq_zero
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF n) =
      fun _ => 0 := by
  have hFiber :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n) :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_offLinkFiberConstant_of_ne
      n periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget_ne_originAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget_ne_secondTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget_ne_thirdTarget
  have hComm :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF n =
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
            periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n := by
    ext A
    simp [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF,
      mul_comm]
  rw [hComm]
  funext A
  have hMul :=
    continuous_compact_oriented_singleLinkHeatBathProjection_mul_of_right_offLinkFiberConstant
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget)
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n)
      hFiber A
  have hZero := congrFun
    (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_projection_self_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget) A
  exact hMul.trans (by rw [hZero, zero_mul])

/-- A zero concrete projection makes the corresponding fluctuation fix the
four-coordinate Gibbs representative. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_fluctuation_eq_self_of_projection_eq_zero
    (n : ℕ)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hProjection :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF n) =
        fun _ => 0) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2 n) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2 n := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  have hProjectionL2 :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2 n) = 0 := by
    change
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF n)) = 0
    rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero]
    have hBCF :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
            edge
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF n) = 0 := by
      ext A
      exact congrFun hProjection A
    rw [hBCF]
    simp [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
  rw [hProjectionL2, sub_zero]

/-- Each selected fluctuation fixes the four-coordinate family. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_target_fluctuation_eq_self
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeOriginAxisZeroTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2 n) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2 n :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_fluctuation_eq_self_of_projection_eq_zero
    n periodicHypercubicThreeOriginAxisZeroTarget
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_target_projection_eq_zero n)

theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_source_fluctuation_eq_self
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2 n) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2 n :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_fluctuation_eq_self_of_projection_eq_zero
    n periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_source_projection_eq_zero n)

theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_third_fluctuation_eq_self
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2 n) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2 n :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_fluctuation_eq_self_of_projection_eq_zero
    n periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_third_projection_eq_zero n)

theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_fourth_fluctuation_eq_self
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2 n) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2 n :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_fluctuation_eq_self_of_projection_eq_zero
    n periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_fourth_projection_eq_zero n)

/-- Every unselected coordinate projection fixes the four-coordinate family. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_projection_eq_self_of_ne
    (n : ℕ)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTarget : edge ≠ periodicHypercubicThreeOriginAxisZeroTarget)
    (hSource : edge ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget)
    (hThird : edge ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget)
    (hFourth : edge ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF n) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF n := by
  apply continuous_compact_oriented_singleLinkHeatBathProjection_fixes
  intro A B hAgree
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n A *
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget A =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n B *
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget B
  have hTriple :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_offLinkFiberConstant_of_ne
      n edge hTarget hSource hThird A B hAgree
  have hFourthCoordinate :=
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_offLinkFiberConstant_of_ne
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget
      edge hFourth A B hAgree
  rw [hTriple, hFourthCoordinate]

/-- Every unselected fluctuation annihilates the four-coordinate family. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_fluctuation_eq_zero_of_ne
    (n : ℕ)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTarget : edge ≠ periodicHypercubicThreeOriginAxisZeroTarget)
    (hSource : edge ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget)
    (hThird : edge ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget)
    (hFourth : edge ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityFourFourthTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2 n) = 0 := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  change
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF n) -
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF n)) = 0
  rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero]
  have hBCF :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF n) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF n := by
    ext A
    exact congrFun
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_projection_eq_self_of_ne
        n edge hTarget hSource hThird hFourth) A
  rw [hBCF, sub_self]

/-- Every family member lies in the exact canonical four-coordinate joint
sector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fourInfiniteRankQuadrupleL2_mem_four_fluctuationJointSector
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2 n ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankSector := by
  rw [continuous_compact_oriented_fluctuationJointSectorSubmoduleL2_mem_iff]
  constructor
  · intro edge hEdge
    unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankSector at hEdge
    rcases Finset.mem_insert.mp hEdge with hEq | hTriple
    · subst edge
      exact
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_fourth_fluctuation_eq_self
          n
    · rcases Finset.mem_insert.mp hTriple with hEq | hRest
      · subst edge
        exact
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_target_fluctuation_eq_self
            n
      · rcases Finset.mem_insert.mp hRest with hEq | hRest
        · subst edge
          exact
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_source_fluctuation_eq_self
              n
        · have hEq := Finset.mem_singleton.mp hRest
          subst edge
          exact
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_third_fluctuation_eq_self
              n
  · intro edge hEdge
    apply
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_fluctuation_eq_zero_of_ne
        n edge
    · intro hEq
      subst edge
      exact hEdge
        (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    · intro hEq
      subst edge
      exact hEdge
        (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    · intro hEq
      subst edge
      exact hEdge
        (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
    · intro hEq
      subst edge
      exact hEdge (Finset.mem_insert_self _ _)

/-- The actual beta-zero heat-bath eigenspace at eigenvalue four has Cardinal
rank at least `aleph0`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_four_heatBathCardinalityEigenspaceL2 :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
          4) := by
  classical
  let Q := fun edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
      edge
  have hGeneric :=
    continuousLinearMap_aleph0_le_rank_cardinalityEigenspace_of_linearIndependent_mem_jointSectorL2
      (Q := Q)
      (s := periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankSector)
      (v := periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2)
      (fun edge f =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
          edge f)
      (fun target source f =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
          target source f)
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_linearIndependent
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fourInfiniteRankQuadrupleL2_mem_four_fluctuationJointSector
  rw [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankSector_card]
    at hGeneric
  simpa [Q,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_univ_sum_fluctuationL2]
    using hGeneric

/-- The range of the actual cardinality-four projector has rank at least
`aleph0`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_range_four_fluctuationCardinalityProjectorL2 :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            4).toLinearMap) := by
  classical
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_heatBathCardinalityEigenspaceL2
      4 (by omega)]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_four_heatBathCardinalityEigenspaceL2

/-- The actual cardinality-four joint-sector sum has rank at least `aleph0`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_four_fluctuationCardinalityJointSectorSumSubmoduleL2 :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
          4) := by
  classical
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_heatBathCardinalityEigenspaceL2
      4 (by omega)]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_four_heatBathCardinalityEigenspaceL2

/-- Compact receipt for the cardinality-four infinite-rank sector. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourEigenspaceInfiniteRankL2Receipt :
    Prop :=
  LinearIndependent ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2 ∧
    (∀ n : ℕ,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2 n ∈
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankSector) ∧
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
          4) ∧
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            4).toLinearMap) ∧
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
          4)

/-- The actual eigenvalue-four infinite-rank receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourEigenspaceInfiniteRankL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourEigenspaceInfiniteRankL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleL2_linearIndependent,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fourInfiniteRankQuadrupleL2_mem_four_fluctuationJointSector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_four_heatBathCardinalityEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_range_four_fluctuationCardinalityProjectorL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_four_fluctuationCardinalityJointSectorSumSubmoduleL2⟩

end

end MathlibAnalytic
end MGAP4D
