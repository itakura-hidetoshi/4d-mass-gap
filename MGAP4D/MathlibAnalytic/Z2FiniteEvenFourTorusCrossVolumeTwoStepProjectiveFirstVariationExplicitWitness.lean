import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepProjectiveFirstVariationSpatialDefect
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeOneStepProjectiveFirstVariationExplicitWitness
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeProjectiveSmallPositiveObstruction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The second finest vertex for the explicit direct two-step `H = 0`
projective witness.  Moving two finest lattice units in the second distinguished
spatial direction changes the intermediate side-four vertex but returns to the
same coarsest side-two vertex. -/
def finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessSecondVertex :
    FiniteEvenFourTorusSpatialVertex
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement 0)) :=
  finiteEvenFourTorusSpatialVertexStep
    (finiteEvenFourTorusDoubleRefinement
      (finiteEvenFourTorusDoubleRefinement 0))
    (finiteEvenFourTorusSpatialVertexStep
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement 0))
      (finiteEvenFourTorusZ2AllVolumeWitnessVertex
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement 0)))
      finiteEvenFourTorusZ2GaussWitnessDirectionTwo)
    finiteEvenFourTorusZ2GaussWitnessDirectionTwo

/-- The second finest link of the explicit direct two-step witness. -/
def finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessSecondLink :
    FiniteEvenFourTorusSpatialLink
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement 0)) :=
  (finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessSecondVertex,
    finiteEvenFourTorusZ2GaussWitnessDirectionOne)

/-- The selected finest links have exactly the same image after the two actual
spatial-link coarse maps. -/
theorem finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessSecondLink_twoStepCoarseMap_eq :
    finiteEvenFourTorusSpatialLinkCoarseMap 0
        (finiteEvenFourTorusSpatialLinkCoarseMap
          (finiteEvenFourTorusDoubleRefinement 0)
          finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessSecondLink) =
      finiteEvenFourTorusSpatialLinkCoarseMap 0
        (finiteEvenFourTorusSpatialLinkCoarseMap
          (finiteEvenFourTorusDoubleRefinement 0)
          (finiteEvenFourTorusZ2AllVolumeWitnessLink
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement 0)))) := by
  native_decide

/-- Explicit finest configuration: excite the canonical witness link and a
second finest link which is distinct at the intermediate side but has the same
coarsest two-step image. -/
def finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration :
    FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement 0)) :=
  finiteEvenFourTorusZ2SingleLinkExcitation
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement 0))
      (finiteEvenFourTorusZ2AllVolumeWitnessLink
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement 0))) *
    finiteEvenFourTorusZ2SingleLinkExcitation
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement 0))
      finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessSecondLink

/-- The explicit finest configuration lies in the kernel of the actual direct
two-step configuration hom.  The first coarse map keeps two distinct
intermediate excitations; the second sends them to the same coarsest link, where
the two nontrivial `Z₂` values cancel. -/
theorem finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration_twoStepCoarseMap_eq_one :
    finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom 0
        finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration = 1 := by
  change
    finiteEvenFourTorusZ2SliceConfigurationCoarseMap 0
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
        (finiteEvenFourTorusDoubleRefinement 0)
        finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration) = 1
  unfold finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration
  rw [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_mul]
  rw [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_singleLinkExcitation,
    finiteEvenFourTorusZ2SliceConfigurationCoarseMap_singleLinkExcitation]
  rw [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_mul]
  rw [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_singleLinkExcitation,
    finiteEvenFourTorusZ2SliceConfigurationCoarseMap_singleLinkExcitation,
    finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessSecondLink_twoStepCoarseMap_eq]
  funext e
  unfold finiteEvenFourTorusZ2SingleLinkExcitation
  change
    (if e = finiteEvenFourTorusSpatialLinkCoarseMap 0
        (finiteEvenFourTorusSpatialLinkCoarseMap
          (finiteEvenFourTorusDoubleRefinement 0)
          (finiteEvenFourTorusZ2AllVolumeWitnessLink
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement 0))))
      then z2GaugeNontrivial else 1) *
      (if e = finiteEvenFourTorusSpatialLinkCoarseMap 0
        (finiteEvenFourTorusSpatialLinkCoarseMap
          (finiteEvenFourTorusDoubleRefinement 0)
          (finiteEvenFourTorusZ2AllVolumeWitnessLink
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement 0))))
      then z2GaugeNontrivial else 1) = 1
  by_cases he : e = finiteEvenFourTorusSpatialLinkCoarseMap 0
      (finiteEvenFourTorusSpatialLinkCoarseMap
        (finiteEvenFourTorusDoubleRefinement 0)
        (finiteEvenFourTorusZ2AllVolumeWitnessLink
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement 0))))
  · rw [if_pos he, z2GaugeNontrivial_mul_self]
  · rw [if_neg he, one_mul]

/-- Direct coarse-kernel cancellation does not remove finest curvature: the
canonical finest witness plaquette still has nontrivial holonomy. -/
theorem finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration_holonomy :
    finiteEvenFourTorusZ2SpatialPlaquetteHolonomy
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement 0))
        finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration
        (finiteEvenFourTorusZ2AllVolumeWitnessPlaquette
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement 0))) =
      z2GaugeNontrivial := by
  native_decide

/-- The explicit direct coarse-kernel witness has strictly positive finest
spatial Wilson action at energies `(0,1)`. -/
theorem finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration_spatialWilsonAction_pos :
    0 < finiteEvenFourTorusZ2SpatialWilsonAction
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement 0))
      0 1
      finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration := by
  apply finiteEvenFourTorusZ2SpatialWilsonAction_zero_one_pos_of_holonomy_ne_one
    (finiteEvenFourTorusDoubleRefinement
      (finiteEvenFourTorusDoubleRefinement 0))
    finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration
    (finiteEvenFourTorusZ2AllVolumeWitnessPlaquette
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement 0)))
  rw [finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration_holonomy]
  native_decide

/- The concrete `H = 0`, `(energyIdentity,energyNontrivial) = (0,1)` direct
witness has a genuinely nonzero beta-zero two-step projective first variation. -/
set_option maxRecDepth 4096 in
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepProjectiveFirstVariation_explicitWitness_ne_zero :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
        0 0 1
        finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration
        1 1 1 ≠ 0 := by
  have hSraw :=
    finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration_spatialWilsonAction_pos
  have hS1raw :=
    finiteEvenFourTorusZ2SpatialWilsonAction_zero_one_one
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement 0))
  let k : ℝ :=
    Fintype.card (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom 0).ker
  let s : ℝ :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale 0
  let S : ℝ :=
    finiteEvenFourTorusZ2SpatialWilsonAction
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement 0))
      0 1 finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration
  let S1 : ℝ :=
    finiteEvenFourTorusZ2SpatialWilsonAction
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement 0))
      0 1
      (1 : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement 0)))
  let d : ℝ := S - S1
  change 0 < S at hSraw
  change S1 = 0 at hS1raw
  have hformula :
      finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
          0 0 1
          finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration
          1 1 1 =
        -(1 / 2 : ℝ) * k * s ^ 2 * d := by
    dsimp [k, s, d, S, S1]
    exact
      finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionFirstVariation_identityAnchor_eq_spatialDefect_of_twoStepCoarseMap_eq_one
        0 0 1 finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration
        finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration_twoStepCoarseMap_eq_one
  have hk0 : k ≠ 0 := by
    dsimp [k]
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom 0).ker ≠ 0)
  have hs0 : s ≠ 0 := by
    exact ne_of_gt
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale_pos 0)
  have hd0 : d ≠ 0 := by
    change S - S1 ≠ 0
    simpa [hS1raw] using (ne_of_gt hSraw)
  have hprod : -(1 / 2 : ℝ) * k * s ^ 2 * d ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) hk0)
        (pow_ne_zero 2 hs0))
      hd0
  intro hzero
  exact hprod (hformula.symm.trans hzero)

/-- Consequently the actual operator-norm-normalized direct finest-to-coarsest
two-step transfer is nonintertwining throughout a whole sufficiently small
positive-coupling interval, with no remaining first-variation hypothesis. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_explicitWitness_exists_smallPositive_interval_ne_zero :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (β : ℝ) (hβ : 0 < β), β < ε →
        finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
          0 β 0 1 (le_of_lt hβ) (by norm_num : (0 : ℝ) ≤ 1) ≠ 0 := by
  exact
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_exists_smallPositive_interval_ne_zero_of_projectiveFirstVariation_ne_zero
      0 0 1 (by norm_num)
      finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration
      (1 : FiniteEvenFourTorusZ2SliceConfiguration 0)
      finiteEvenFourTorusZ2GaugeInvariantTwoStepProjectiveFirstVariation_explicitWitness_ne_zero

/-- Audit-visible Package-S direct two-step witness receipt. -/
structure Z2FiniteEvenFourTorusCrossVolumeTwoStepExplicitProjectiveFirstVariationWitnessPackage where
  directCoarseKernel :
    finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom 0
        finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration = 1
  nontrivialFinestHolonomy :
    finiteEvenFourTorusZ2SpatialPlaquetteHolonomy
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement 0))
        finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration
        (finiteEvenFourTorusZ2AllVolumeWitnessPlaquette
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement 0))) =
      z2GaugeNontrivial
  finestSpatialActionPositive :
    0 < finiteEvenFourTorusZ2SpatialWilsonAction
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement 0))
      0 1 finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration
  firstVariationNonzero :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
        0 0 1
        finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration
        1 1 1 ≠ 0
  normalizedResidualSmallPositive :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (β : ℝ) (hβ : 0 < β), β < ε →
        finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
          0 β 0 1 (le_of_lt hβ) (by norm_num : (0 : ℝ) ≤ 1) ≠ 0

/-- Construct the Package-S direct two-step explicit witness receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeTwoStepExplicitProjectiveFirstVariationWitnessPackage :
    Z2FiniteEvenFourTorusCrossVolumeTwoStepExplicitProjectiveFirstVariationWitnessPackage where
  directCoarseKernel :=
    finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration_twoStepCoarseMap_eq_one
  nontrivialFinestHolonomy :=
    finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration_holonomy
  finestSpatialActionPositive :=
    finiteEvenFourTorusZ2TwoStepProjectiveFirstVariationWitnessConfiguration_spatialWilsonAction_pos
  firstVariationNonzero :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepProjectiveFirstVariation_explicitWitness_ne_zero
  normalizedResidualSmallPositive :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_explicitWitness_exists_smallPositive_interval_ne_zero

end

end MathlibAnalytic
end MGAP4D
