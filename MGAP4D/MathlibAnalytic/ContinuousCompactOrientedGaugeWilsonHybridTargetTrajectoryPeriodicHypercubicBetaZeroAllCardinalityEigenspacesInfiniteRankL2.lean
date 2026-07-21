import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroFourEigenspaceInfiniteRankL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- Generic data carried by a countable bounded-continuous family that occupies
one exact finite projection sector. -/
structure BoundedContinuousFunctionProjectionSectorWitness
    {X Edge : Type*}
    [TopologicalSpace X]
    [DecidableEq Edge]
    (projection : Edge → BoundedContinuousFunction X ℝ → X → ℝ)
    (k : ℕ) where
  sector : Finset Edge
  family : ℕ → BoundedContinuousFunction X ℝ
  card_sector : sector.card = k
  linearIndependent : LinearIndependent ℝ family
  projection_zero_of_mem :
    ∀ n edge, edge ∈ sector → projection edge (family n) = fun _ => 0
  projection_eq_self_of_not_mem :
    ∀ n edge, edge ∉ sector → projection edge (family n) = fun x => family n x

/-- Generic one-step packaging principle for projection-sector witnesses.  The
analytic work is isolated in the supplied product-family hypotheses; this
constructor records the exact insertion and cardinality transition. -/
noncomputable def BoundedContinuousFunctionProjectionSectorWitness.extend
    {X Edge : Type*}
    [TopologicalSpace X]
    [DecidableEq Edge]
    {projection : Edge → BoundedContinuousFunction X ℝ → X → ℝ}
    {k : ℕ}
    (W : BoundedContinuousFunctionProjectionSectorWitness projection k)
    (newEdge : Edge)
    (hNewEdge : newEdge ∉ W.sector)
    (factor : BoundedContinuousFunction X ℝ)
    (hLinearIndependent :
      LinearIndependent ℝ (fun n : ℕ => W.family n * factor))
    (hOldZero :
      ∀ n edge, edge ∈ W.sector →
        projection edge (W.family n * factor) = fun _ => 0)
    (hNewZero :
      ∀ n,
        projection newEdge (W.family n * factor) = fun _ => 0)
    (hOutsideFixed :
      ∀ n edge, edge ∉ insert newEdge W.sector →
        projection edge (W.family n * factor) =
          fun x => (W.family n * factor) x) :
    BoundedContinuousFunctionProjectionSectorWitness projection (k + 1) where
  sector := insert newEdge W.sector
  family := fun n => W.family n * factor
  card_sector := by
    rw [Finset.card_insert_of_notMem hNewEdge, W.card_sector]
  linearIndependent := hLinearIndependent
  projection_zero_of_mem := by
    intro n edge hEdge
    rcases Finset.mem_insert.mp hEdge with hEq | hOld
    · subst edge
      exact hNewZero n
    · exact hOldZero n edge hOld
  projection_eq_self_of_not_mem := hOutsideFixed

/-- Pointwise coercion of bounded-continuous functions as a linear map. -/
noncomputable def boundedContinuousFunctionToFunctionLinearMap
    {X : Type*}
    [TopologicalSpace X] :
    BoundedContinuousFunction X ℝ →ₗ[ℝ] (X → ℝ) where
  toFun F x := F x
  map_add' F G := rfl
  map_smul' a F := rfl

/-- Pointwise coercion of bounded-continuous functions is injective. -/
theorem boundedContinuousFunctionToFunctionLinearMap_injective
    {X : Type*}
    [TopologicalSpace X] :
    Function.Injective
      (boundedContinuousFunctionToFunctionLinearMap (X := X)) := by
  intro F G hFG
  ext x
  exact congrFun hFG x

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_allCardinalityInfiniteRankEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  fun a b => instDecidableEqProd a b

/-- Projection-sector witnesses specialized to the actual side-three periodic
`SU(2)` beta-zero system. -/
abbrev periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness
    (k : ℕ) :=
  BoundedContinuousFunctionProjectionSectorWitness
    (fun edge F =>
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        edge F)
    k

/-- Any witness whose sector has cardinality strictly below 324 admits a fresh
physical edge. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_exists_freshEdge
    {k : ℕ}
    (W : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness k)
    (hk : k < 324) :
    ∃ edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
      edge ∉ W.sector := by
  by_contra hNo
  have hAll :
      ∀ edge :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
        edge ∈ W.sector := by
    intro edge
    by_contra hNot
    exact hNo ⟨edge, hNot⟩
  have hSub :
      (Finset.univ :
        Finset
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) ⊆
        W.sector := by
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
  rw [hUnivCard, W.card_sector] at hCard
  omega

/-- Replace an arbitrary selected physical coordinate by the identity. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankIdentityConfiguration
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
    A edge 1

/-- Replace an arbitrary selected physical coordinate by the central negative
identity. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankNegativeConfiguration
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
    A edge specialUnitaryTwoNegativeIdentity

/-- Identity replacement preserves every off-edge coordinate. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankIdentityConfiguration_agreeOffLink
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.AgreeOffLink
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankIdentityConfiguration
        edge A)
      A edge := by
  intro other hOther
  simp [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankIdentityConfiguration,
    CompactOrientedGaugeWilsonSystem.replaceLink, hOther]

/-- Negative-identity replacement preserves every off-edge coordinate. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankNegativeConfiguration_agreeOffLink
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.AgreeOffLink
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankNegativeConfiguration
        edge A)
      A edge := by
  intro other hOther
  simp [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankNegativeConfiguration,
    CompactOrientedGaugeWilsonSystem.replaceLink, hOther]

/-- The centered Wilson coordinate has a universal jump of two between the
negative and identity sections at the same edge. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankCenteredCoordinate_negative_sub_identity_eq_two
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankNegativeConfiguration
          edge A) -
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankIdentityConfiguration
          edge A) =
      2 := by
  have hNegative :
      specialUnitaryWilsonPlaquetteEnergy 2 specialUnitaryTwoNegativeIdentity = 2 := by
    norm_num [specialUnitaryTwoNegativeIdentity,
      specialUnitaryWilsonPlaquetteEnergy, Matrix.trace, Matrix.one_apply,
      Fin.sum_univ_two]
  have hNegativeLink :
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankNegativeConfiguration
          edge A) edge = specialUnitaryTwoNegativeIdentity := by
    unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankNegativeConfiguration
    exact compact_oriented_replaceLink_same
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base
      A edge specialUnitaryTwoNegativeIdentity
  have hIdentityLink :
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankIdentityConfiguration
          edge A) edge = (1 : SpecialUnitaryMatrixGroup 2) := by
    unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankIdentityConfiguration
    exact compact_oriented_replaceLink_same
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base
      A edge (1 : SpecialUnitaryMatrixGroup 2)
  change
    (specialUnitaryWilsonPlaquetteEnergy 2
        ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankNegativeConfiguration
          edge A) edge) - specialUnitaryTwoWilsonEnergyHaarMean) -
      (specialUnitaryWilsonPlaquetteEnergy 2
        ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankIdentityConfiguration
          edge A) edge) - specialUnitaryTwoWilsonEnergyHaarMean) = 2
  rw [hNegativeLink, hIdentityLink, hNegative,
    specialUnitaryWilsonPlaquetteEnergy_two_one]
  ring

/-- A witness family is off-link-fiber constant at every edge outside its exact
sector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_family_offLinkFiberConstant_of_not_mem
    {k : ℕ}
    (W : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness k)
    (n : ℕ)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hEdge : edge ∉ W.sector) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
      edge (W.family n) := by
  rw [← continuous_compact_oriented_singleLinkHeatBathProjection_fixed_iff
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem edge (W.family n)]
  simpa using W.projection_eq_self_of_not_mem n edge hEdge

/-- The normalized two-section difference at one arbitrary edge. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankDifferenceLinearMap
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    BoundedContinuousFunction
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ →ₗ[ℝ]
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration → ℝ) where
  toFun H A :=
    (H (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankNegativeConfiguration
          edge A) -
      H (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankIdentityConfiguration
          edge A)) / 2
  map_add' H K := by
    funext A
    simp
    ring
  map_smul' a H := by
    funext A
    simp
    ring

/-- The two-section difference recovers the old witness family after multiplying
by the centered coordinate at a fresh edge. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankDifferenceLinearMap_apply
    {k : ℕ}
    (W : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness k)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hEdge : edge ∉ W.sector)
    (n : ℕ)
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankDifferenceLinearMap edge
        (W.family n *
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge)
        A =
      W.family n A := by
  let F := W.family n
  let G := periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge
  let AN :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankNegativeConfiguration
      edge A
  let AI :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankIdentityConfiguration
      edge A
  have hFiber :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
        edge F :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_family_offLinkFiberConstant_of_not_mem
      W n edge hEdge
  have hFNegative : F AN = F A :=
    hFiber AN A
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankNegativeConfiguration_agreeOffLink
        edge A)
  have hFIdentity : F AI = F A :=
    hFiber AI A
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankIdentityConfiguration_agreeOffLink
        edge A)
  have hJump : G AN - G AI = 2 := by
    simpa [G, AN, AI] using
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankCenteredCoordinate_negative_sub_identity_eq_two
        edge A
  change (F AN * G AN - F AI * G AI) / 2 = F A
  rw [hFNegative, hFIdentity]
  calc
    (F A * G AN - F A * G AI) / 2 = F A * (G AN - G AI) / 2 := by ring
    _ = F A * 2 / 2 := by rw [hJump]
    _ = F A := by ring

/-- Multiplication by a centered coordinate at a fresh edge preserves the
countable linear independence of an exact-sector witness. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_product_linearIndependent
    {k : ℕ}
    (W : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness k)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hEdge : edge ∉ W.sector) :
    LinearIndependent ℝ
      (fun n : ℕ =>
        W.family n *
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge) := by
  have hFunctionLinearIndependent :
      LinearIndependent ℝ (fun n : ℕ => fun A => W.family n A) := by
    have hMapped :=
      W.linearIndependent.map'
        (boundedContinuousFunctionToFunctionLinearMap
          (X := periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration))
        (LinearMap.ker_eq_bot.mpr
          (boundedContinuousFunctionToFunctionLinearMap_injective
            (X := periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration)))
    simpa [boundedContinuousFunctionToFunctionLinearMap, Function.comp_def]
      using hMapped
  apply
    boundedContinuousFunction_mul_right_linearIndependent_of_linearMap_recovers
      (u := W.family)
      (g := periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF edge)
      (recover :=
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankDifferenceLinearMap
          edge)
      (w := fun n : ℕ => fun A => W.family n A)
  · intro n
    funext A
    exact
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankDifferenceLinearMap_apply
        W edge hEdge n A
  · exact hFunctionLinearIndependent

/-- At an old selected edge, the extended product family still has zero
projection. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_product_projection_zero_of_mem_old
    {k : ℕ}
    (W : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness k)
    (newEdge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNewEdge : newEdge ∉ W.sector)
    (n : ℕ)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hEdge : edge ∈ W.sector) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        edge
        (W.family n *
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF newEdge) =
      fun _ => 0 := by
  have hEdgeNe : edge ≠ newEdge := by
    intro hEq
    subst edge
    exact hNewEdge hEdge
  funext A
  have hMul :=
    continuous_compact_oriented_singleLinkHeatBathProjection_mul_of_right_offLinkFiberConstant
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      edge (W.family n)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF newEdge)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_offLinkFiberConstant_of_ne
        newEdge edge hEdgeNe)
      A
  have hOldZero := congrFun (W.projection_zero_of_mem n edge hEdge) A
  exact hMul.trans (by rw [hOldZero, zero_mul])

/-- At the newly inserted edge, the extended product family has zero
projection. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_product_projection_zero_new
    {k : ℕ}
    (W : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness k)
    (newEdge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNewEdge : newEdge ∉ W.sector)
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        newEdge
        (W.family n *
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF newEdge) =
      fun _ => 0 := by
  have hFiber :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
        newEdge (W.family n) :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_family_offLinkFiberConstant_of_not_mem
      W n newEdge hNewEdge
  have hComm :
      (fun A =>
        W.family n A *
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF newEdge A) =
        fun A =>
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF newEdge A *
            W.family n A := by
    funext A
    rw [mul_comm]
  change
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        newEdge
        (fun A =>
          W.family n A *
            periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF newEdge A) =
      fun _ => 0
  rw [hComm]
  funext A
  have hMul :=
    continuous_compact_oriented_singleLinkHeatBathProjection_mul_of_right_offLinkFiberConstant
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      newEdge
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF newEdge)
      (W.family n) hFiber A
  have hZero := congrFun
    (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_projection_self_eq_zero
      newEdge) A
  exact hMul.trans (by rw [hZero, zero_mul])

/-- Every edge outside the enlarged sector fixes the extended product family. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_product_projection_eq_self_of_not_mem_insert
    {k : ℕ}
    (W : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness k)
    (newEdge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (n : ℕ)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hEdge : edge ∉ insert newEdge W.sector) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        edge
        (W.family n *
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF newEdge) =
      fun A =>
        (W.family n *
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF newEdge) A := by
  have hEdgeNe : edge ≠ newEdge := by
    intro hEq
    subst edge
    exact hEdge (Finset.mem_insert_self _ _)
  have hOldNot : edge ∉ W.sector := by
    intro hOld
    exact hEdge (Finset.mem_insert_of_mem hOld)
  apply continuous_compact_oriented_singleLinkHeatBathProjection_fixes
  intro A B hAgree
  change
    W.family n A *
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF newEdge A =
      W.family n B *
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF newEdge B
  have hFamily :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_family_offLinkFiberConstant_of_not_mem
      W n edge hOldNot A B hAgree
  have hFactor :=
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_offLinkFiberConstant_of_ne
      newEdge edge hEdgeNe A B hAgree
  rw [hFamily, hFactor]

/-- Actual one-step induction: insert one fresh physical edge and multiply by
its centered Wilson coordinate. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_extend
    {k : ℕ}
    (W : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness k)
    (hk : k < 324) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness
      (k + 1) := by
  let newEdge := Classical.choose
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_exists_freshEdge
      W hk)
  have hNewEdge : newEdge ∉ W.sector :=
    Classical.choose_spec
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_exists_freshEdge
        W hk)
  exact
    BoundedContinuousFunctionProjectionSectorWitness.extend
      W newEdge hNewEdge
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF newEdge)
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_product_linearIndependent
        W newEdge hNewEdge)
      (fun n edge hEdge =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_product_projection_zero_of_mem_old
          W newEdge hNewEdge n edge hEdge)
      (fun n =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_product_projection_zero_new
          W newEdge hNewEdge n)
      (fun n edge hEdge =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_product_projection_eq_self_of_not_mem_insert
          W newEdge n edge hEdge)

/-- The explicit cardinality-four construction packaged as the base witness for
the finite induction. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankSectorWitness :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness 4 where
  sector := periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankSector
  family := periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF
  card_sector :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankSector_card
  linearIndependent :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_linearIndependent
  projection_zero_of_mem := by
    intro n edge hEdge
    unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankSector at hEdge
    rcases Finset.mem_insert.mp hEdge with hEq | hTriple
    · subst edge
      exact
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_fourth_projection_eq_zero
          n
    · rcases Finset.mem_insert.mp hTriple with hEq | hRest
      · subst edge
        exact
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_target_projection_eq_zero
            n
      · rcases Finset.mem_insert.mp hRest with hEq | hRest
        · subst edge
          exact
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_source_projection_eq_zero
              n
        · have hEq := Finset.mem_singleton.mp hRest
          subst edge
          exact
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_third_projection_eq_zero
              n
  projection_eq_self_of_not_mem := by
    intro n edge hEdge
    apply
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankQuadrupleBCF_projection_eq_self_of_ne
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

/-- Iterate the one-step extension from cardinality four for a specified number
of steps, while staying inside the 324-edge system. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_fromFour :
    (d : ℕ) →
      4 + d ≤ 324 →
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness
        (4 + d)
  | 0, _h => by
      simpa using
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFourInfiniteRankSectorWitness
  | d + 1, h => by
      have hPrev : 4 + d ≤ 324 := by omega
      have hStrict : 4 + d < 324 := by omega
      have W :=
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_fromFour
          d hPrev
      simpa [Nat.add_assoc] using
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_extend
          W hStrict

/-- Every cardinality from four through 324 has an exact countable
bounded-continuous witness family. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_nonempty
    (k : ℕ)
    (hLower : 4 ≤ k)
    (hUpper : k ≤ 324) :
    Nonempty
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness
        k) := by
  have hEq : 4 + (k - 4) = k := by omega
  have hBound : 4 + (k - 4) ≤ 324 := by omega
  exact ⟨hEq ▸
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_fromFour
      (k - 4) hBound⟩

/-- The Gibbs `L²` family represented by an arbitrary exact-sector witness. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_familyL2
    {k : ℕ}
    (W : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness k)
    (n : ℕ) :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
    (W.family n)

/-- Every witness remains linearly independent after injective passage to the
actual Gibbs `L²` space. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_familyL2_linearIndependent
    {k : ℕ}
    (W : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness k) :
    LinearIndependent ℝ
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_familyL2
        W) := by
  have hMapped :=
    W.linearIndependent.map'
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap
      (LinearMap.ker_eq_bot.mpr
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap_injective)
  simpa [Function.comp_def,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_familyL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap,
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
    using hMapped

/-- Zero concrete projection makes the corresponding fluctuation fix the Gibbs
representative. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZero_gibbsL2RepresentativeBCF_fluctuation_eq_self_of_projection_eq_zero
    (F : BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hProjection :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        edge F = fun _ => 0) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF F) =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF F := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  have hProjectionL2 :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF F) =
        0 := by
    rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero]
    have hBCF :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
            edge F = 0 := by
      ext A
      exact congrFun hProjection A
    rw [hBCF]
    simp [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
  rw [hProjectionL2, sub_zero]

/-- Fixed concrete projection makes the corresponding fluctuation annihilate
the Gibbs representative. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZero_gibbsL2RepresentativeBCF_fluctuation_eq_zero_of_projection_eq_self
    (F : BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hProjection :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        edge F = fun A => F A) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF F) =
      0 := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero]
  have hBCF :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
          edge F = F := by
    ext A
    exact congrFun hProjection A
  rw [hBCF, sub_self]

/-- Every Gibbs `L²` family member occupies exactly the joint sector carried by
its witness. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_familyL2_mem_jointSector
    {k : ℕ}
    (W : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness k)
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_familyL2
        W n ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        W.sector := by
  rw [continuous_compact_oriented_fluctuationJointSectorSubmoduleL2_mem_iff]
  constructor
  · intro edge hEdge
    exact
      periodicHypercubicThreeSpecialUnitaryTwoBetaZero_gibbsL2RepresentativeBCF_fluctuation_eq_self_of_projection_eq_zero
        (W.family n) edge (W.projection_zero_of_mem n edge hEdge)
  · intro edge hEdge
    exact
      periodicHypercubicThreeSpecialUnitaryTwoBetaZero_gibbsL2RepresentativeBCF_fluctuation_eq_zero_of_projection_eq_self
        (W.family n) edge (W.projection_eq_self_of_not_mem n edge hEdge)

/-- Any exact-sector witness of cardinality `k` gives an `aleph0` lower bound
for the actual beta-zero heat-bath eigenspace at eigenvalue `k`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_aleph0_le_rank_heatBathCardinalityEigenspaceL2
    {k : ℕ}
    (W : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness k) :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
          k) := by
  classical
  let Q := fun edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
      edge
  have hGeneric :=
    continuousLinearMap_aleph0_le_rank_cardinalityEigenspace_of_linearIndependent_mem_jointSectorL2
      (Q := Q)
      (s := W.sector)
      (v :=
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_familyL2
          W)
      (fun edge f =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
          edge f)
      (fun target source f =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
          target source f)
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_familyL2_linearIndependent
        W)
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_familyL2_mem_jointSector
        W)
  rw [W.card_sector] at hGeneric
  simpa [Q,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_univ_sum_fluctuationL2]
    using hGeneric

/-- All actual beta-zero heat-bath eigenspaces with eigenvalues from four
through 324 have rank at least `aleph0`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_heatBathCardinalityEigenspaceL2_of_four_le
    (k : ℕ)
    (hLower : 4 ≤ k)
    (hUpper : k ≤ 324) :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
          k) := by
  let W := Classical.choice
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_nonempty
      k hLower hUpper)
  exact
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroInfiniteRankSectorWitness_aleph0_le_rank_heatBathCardinalityEigenspaceL2
      W

/-- The range of every actual beta-zero cardinality projector from four through
324 has rank at least `aleph0`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_range_fluctuationCardinalityProjectorL2_of_four_le
    (k : ℕ)
    (hLower : 4 ≤ k)
    (hUpper : k ≤ 324) :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            k).toLinearMap) := by
  have hEdgeCard :
      Fintype.card
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =
        324 := by
    simpa using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324
  have hkCard :
      k ≤ Fintype.card
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge := by
    omega
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_heatBathCardinalityEigenspaceL2
      k hkCard]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_heatBathCardinalityEigenspaceL2_of_four_le
      k hLower hUpper

/-- Every actual beta-zero cardinality joint-sector sum from four through 324
has rank at least `aleph0`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_fluctuationCardinalityJointSectorSumSubmoduleL2_of_four_le
    (k : ℕ)
    (hLower : 4 ≤ k)
    (hUpper : k ≤ 324) :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
          k) := by
  have hEdgeCard :
      Fintype.card
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =
        324 := by
    simpa using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324
  have hkCard :
      k ≤ Fintype.card
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge := by
    omega
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_heatBathCardinalityEigenspaceL2
      k hkCard]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_heatBathCardinalityEigenspaceL2_of_four_le
      k hLower hUpper

/-- Compact receipt for simultaneous infinite rank of every beta-zero
cardinality sector from four through the full 324-edge sector. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllCardinalityEigenspacesInfiniteRankL2Receipt :
    Prop :=
  ∀ k : ℕ, 4 ≤ k → k ≤ 324 →
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
          k) ∧
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            k).toLinearMap) ∧
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
          k)

/-- The simultaneous cardinality-four-through-324 infinite-rank receipt is
proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllCardinalityEigenspacesInfiniteRankL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllCardinalityEigenspacesInfiniteRankL2Receipt := by
  intro k hLower hUpper
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_heatBathCardinalityEigenspaceL2_of_four_le
      k hLower hUpper,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_range_fluctuationCardinalityProjectorL2_of_four_le
      k hLower hUpper,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_fluctuationCardinalityJointSectorSumSubmoduleL2_of_four_le
      k hLower hUpper⟩

end

end MathlibAnalytic
end MGAP4D
