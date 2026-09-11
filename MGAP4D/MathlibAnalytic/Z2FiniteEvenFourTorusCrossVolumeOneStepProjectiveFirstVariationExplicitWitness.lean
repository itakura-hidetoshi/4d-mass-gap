import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeOneStepProjectiveFirstVariationSpatialDefect
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeProjectiveSmallPositiveObstruction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The second fine vertex for the explicit `H = 0` projective witness: move
two fine lattice units in the second distinguished spatial direction.  On the
coarse side of length two this returns to the same coarse vertex. -/
def finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessSecondVertex :
    FiniteEvenFourTorusSpatialVertex (finiteEvenFourTorusDoubleRefinement 0) :=
  finiteEvenFourTorusSpatialVertexStep
    (finiteEvenFourTorusDoubleRefinement 0)
    (finiteEvenFourTorusSpatialVertexStep
      (finiteEvenFourTorusDoubleRefinement 0)
      (finiteEvenFourTorusZ2AllVolumeWitnessVertex
        (finiteEvenFourTorusDoubleRefinement 0))
      finiteEvenFourTorusZ2GaussWitnessDirectionTwo)
    finiteEvenFourTorusZ2GaussWitnessDirectionTwo

/-- The second fine link of the explicit witness. -/
def finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessSecondLink :
    FiniteEvenFourTorusSpatialLink (finiteEvenFourTorusDoubleRefinement 0) :=
  (finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessSecondVertex,
    finiteEvenFourTorusZ2GaussWitnessDirectionOne)

/-- The two selected fine links have exactly the same image under the actual
`H = 0` spatial-link coarse map. -/
theorem finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessSecondLink_coarseMap_eq :
    finiteEvenFourTorusSpatialLinkCoarseMap 0
        finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessSecondLink =
      finiteEvenFourTorusSpatialLinkCoarseMap 0
        (finiteEvenFourTorusZ2AllVolumeWitnessLink
          (finiteEvenFourTorusDoubleRefinement 0)) := by
  native_decide

/-- Explicit fine configuration: excite the canonical witness link and the
second fine link with the same coarse image. -/
def finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration :
    FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement 0) :=
  finiteEvenFourTorusZ2SingleLinkExcitation
      (finiteEvenFourTorusDoubleRefinement 0)
      (finiteEvenFourTorusZ2AllVolumeWitnessLink
        (finiteEvenFourTorusDoubleRefinement 0)) *
    finiteEvenFourTorusZ2SingleLinkExcitation
      (finiteEvenFourTorusDoubleRefinement 0)
      finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessSecondLink

/-- The explicit configuration lies in the kernel of the actual configuration
coarse map.  The two equal coarse-link excitations cancel because the
nontrivial `Z₂` element squares to one. -/
theorem finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration_coarseMap_eq_one :
    finiteEvenFourTorusZ2SliceConfigurationCoarseMap 0
        finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration = 1 := by
  unfold finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration
  rw [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_mul]
  rw [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_singleLinkExcitation,
    finiteEvenFourTorusZ2SliceConfigurationCoarseMap_singleLinkExcitation,
    finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessSecondLink_coarseMap_eq]
  funext e
  unfold finiteEvenFourTorusZ2SingleLinkExcitation
  change
    (if e = finiteEvenFourTorusSpatialLinkCoarseMap 0
        (finiteEvenFourTorusZ2AllVolumeWitnessLink
          (finiteEvenFourTorusDoubleRefinement 0))
      then z2GaugeNontrivial else 1) *
      (if e = finiteEvenFourTorusSpatialLinkCoarseMap 0
        (finiteEvenFourTorusZ2AllVolumeWitnessLink
          (finiteEvenFourTorusDoubleRefinement 0))
      then z2GaugeNontrivial else 1) = 1
  by_cases he : e = finiteEvenFourTorusSpatialLinkCoarseMap 0
      (finiteEvenFourTorusZ2AllVolumeWitnessLink
        (finiteEvenFourTorusDoubleRefinement 0))
  · rw [if_pos he, z2GaugeNontrivial_mul_self]
  · rw [if_neg he, one_mul]

/-- The coarse-kernel cancellation does not remove fine curvature: the
canonical fine witness plaquette has nontrivial holonomy. -/
theorem finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration_holonomy :
    finiteEvenFourTorusZ2SpatialPlaquetteHolonomy
        (finiteEvenFourTorusDoubleRefinement 0)
        finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration
        (finiteEvenFourTorusZ2AllVolumeWitnessPlaquette
          (finiteEvenFourTorusDoubleRefinement 0)) =
      z2GaugeNontrivial := by
  native_decide

/-- At the two-level energies `(0,1)`, every spatial Wilson summand is
nonnegative. -/
theorem finiteEvenFourTorusZ2SpatialWilsonAction_zero_one_nonneg
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 ≤ finiteEvenFourTorusZ2SpatialWilsonAction H 0 1 A := by
  unfold finiteEvenFourTorusZ2SpatialWilsonAction
  apply Finset.sum_nonneg
  intro p _hp
  by_cases hp1 : finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H A p = 1
  · simp [hp1]
  · simp [hp1]

/-- One nontrivial plaquette is enough to make the `(0,1)` spatial Wilson
action strictly positive. -/
theorem finiteEvenFourTorusZ2SpatialWilsonAction_zero_one_pos_of_holonomy_ne_one
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (p : FiniteEvenFourTorusSpatialPlaquette H)
    (hp : finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H A p ≠ 1) :
    0 < finiteEvenFourTorusZ2SpatialWilsonAction H 0 1 A := by
  unfold finiteEvenFourTorusZ2SpatialWilsonAction
  apply Finset.sum_pos'
  · intro q _hq
    by_cases hq1 : finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H A q = 1
    · simp [hq1]
    · simp [hq1]
  · exact ⟨p, Finset.mem_univ p, by simp [hp]⟩

/-- The identity slice has zero `(0,1)` spatial Wilson action. -/
theorem finiteEvenFourTorusZ2SpatialWilsonAction_zero_one_one
    (H : ℕ) :
    finiteEvenFourTorusZ2SpatialWilsonAction H 0 1
      (1 : FiniteEvenFourTorusZ2SliceConfiguration H) = 0 := by
  unfold finiteEvenFourTorusZ2SpatialWilsonAction
  apply Finset.sum_eq_zero
  intro p _hp
  simp [finiteEvenFourTorusZ2SpatialPlaquetteHolonomy]

/-- The explicit fine coarse-kernel witness has strictly positive spatial
Wilson action at energies `(0,1)`. -/
theorem finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration_spatialWilsonAction_pos :
    0 < finiteEvenFourTorusZ2SpatialWilsonAction
      (finiteEvenFourTorusDoubleRefinement 0) 0 1
      finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration := by
  apply finiteEvenFourTorusZ2SpatialWilsonAction_zero_one_pos_of_holonomy_ne_one
    (finiteEvenFourTorusDoubleRefinement 0)
    finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration
    (finiteEvenFourTorusZ2AllVolumeWitnessPlaquette
      (finiteEvenFourTorusDoubleRefinement 0))
  rw [finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration_holonomy]
  native_decide

/-- The configuration-cardinality embedding scale is strictly positive at the
explicit witness volume. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale_zero_pos :
    0 < finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale 0 := by
  rw [← finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_cardinality
    0 (1 : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement 0))]
  exact finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_pos 0 1

/- The explicit `H = 0`, `(energyIdentity,energyNontrivial) = (0,1)` witness
has a genuinely nonzero beta-zero one-step projective first variation. -/
set_option maxRecDepth 2048 in
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepProjectiveFirstVariation_explicitWitness_ne_zero :
    finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
        0 0 1
        finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration
        1 1 1 ≠ 0 := by
  have hSraw :=
    finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration_spatialWilsonAction_pos
  have hS1raw :=
    finiteEvenFourTorusZ2SpatialWilsonAction_zero_one_one
      (finiteEvenFourTorusDoubleRefinement 0)
  let k : ℝ :=
    Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom 0).ker
  let s : ℝ := finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale 0
  let S : ℝ :=
    finiteEvenFourTorusZ2SpatialWilsonAction
      (finiteEvenFourTorusDoubleRefinement 0) 0 1
      finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration
  let S1 : ℝ :=
    finiteEvenFourTorusZ2SpatialWilsonAction
      (finiteEvenFourTorusDoubleRefinement 0) 0 1
      (1 : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement 0))
  let d : ℝ := S - S1
  change 0 < S at hSraw
  change S1 = 0 at hS1raw
  have hformula :
      finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
          0 0 1
          finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration
          1 1 1 =
        -(1 / 2 : ℝ) * k * s ^ 2 * d := by
    dsimp [k, s, d, S, S1]
    exact
      finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionFirstVariation_identityAnchor_eq_spatialDefect_of_coarseMap_eq_one
        0 0 1 finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration
        finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration_coarseMap_eq_one
  have hk0 : k ≠ 0 := by
    dsimp [k]
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom 0).ker ≠ 0)
  have hs0 : s ≠ 0 := by
    exact ne_of_gt finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale_zero_pos
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

/-- Consequently the actual operator-norm-normalized one-step cross-volume
transfer is nonintertwining throughout a whole sufficiently small positive
coupling interval, with no remaining first-variation hypothesis. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_explicitWitness_exists_smallPositive_interval_ne_zero :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (β : ℝ) (hβ : 0 < β), β < ε →
        finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
          0 β 0 1 (le_of_lt hβ) (by norm_num : (0 : ℝ) ≤ 1) ≠ 0 := by
  exact
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_exists_smallPositive_interval_ne_zero_of_projectiveFirstVariation_ne_zero
      0 0 1 (by norm_num)
      finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration
      (1 : FiniteEvenFourTorusZ2SliceConfiguration 0)
      finiteEvenFourTorusZ2GaugeInvariantOneStepProjectiveFirstVariation_explicitWitness_ne_zero

/-- Audit-visible Package-R one-step witness receipt. -/
structure Z2FiniteEvenFourTorusCrossVolumeOneStepExplicitProjectiveFirstVariationWitnessPackage where
  coarseKernel :
    finiteEvenFourTorusZ2SliceConfigurationCoarseMap 0
        finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration = 1
  nontrivialFineHolonomy :
    finiteEvenFourTorusZ2SpatialPlaquetteHolonomy
        (finiteEvenFourTorusDoubleRefinement 0)
        finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration
        (finiteEvenFourTorusZ2AllVolumeWitnessPlaquette
          (finiteEvenFourTorusDoubleRefinement 0)) =
      z2GaugeNontrivial
  spatialActionPositive :
    0 < finiteEvenFourTorusZ2SpatialWilsonAction
      (finiteEvenFourTorusDoubleRefinement 0) 0 1
      finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration
  firstVariationNonzero :
    finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
        0 0 1
        finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration
        1 1 1 ≠ 0
  normalizedResidualSmallPositive :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (β : ℝ) (hβ : 0 < β), β < ε →
        finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
          0 β 0 1 (le_of_lt hβ) (by norm_num : (0 : ℝ) ≤ 1) ≠ 0

/-- Construct the Package-R one-step explicit witness receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeOneStepExplicitProjectiveFirstVariationWitnessPackage :
    Z2FiniteEvenFourTorusCrossVolumeOneStepExplicitProjectiveFirstVariationWitnessPackage where
  coarseKernel :=
    finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration_coarseMap_eq_one
  nontrivialFineHolonomy :=
    finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration_holonomy
  spatialActionPositive :=
    finiteEvenFourTorusZ2ProjectiveFirstVariationWitnessConfiguration_spatialWilsonAction_pos
  firstVariationNonzero :=
    finiteEvenFourTorusZ2GaugeInvariantOneStepProjectiveFirstVariation_explicitWitness_ne_zero
  normalizedResidualSmallPositive :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_explicitWitness_exists_smallPositive_interval_ne_zero

end

end MathlibAnalytic
end MGAP4D