import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroZeroEigenspaceMultiplicityOneL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityOneSingletonWitnessL2
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A countably infinite linearly independent family contained in one exact joint
sector forces the matching cardinality eigenspace of a finite commuting
idempotent family to have Cardinal rank at least `aleph0`. -/
theorem continuousLinearMap_aleph0_le_rank_cardinalityEigenspace_of_linearIndependent_mem_jointSectorL2
    {ι κ : Type*}
    [Fintype ι]
    [DecidableEq ι]
    [Infinite κ]
    (Q : ι → V →L[ℝ] V)
    (s : Finset ι)
    (v : κ → V)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (hLinearIndependent : LinearIndependent ℝ v)
    (hMem : ∀ a : κ, v a ∈ continuousLinearMapJointSectorSubmoduleL2 Q s) :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (Module.End.genEigenspace
          ((∑ i : ι, Q i).toLinearMap)
          (s.card : ℝ) 1) := by
  classical
  have hsLe : s.card ≤ Fintype.card ι := by
    simpa using Finset.card_le_card (Finset.subset_univ s)
  let w : κ →
      Module.End.genEigenspace
        ((∑ i : ι, Q i).toLinearMap)
        (s.card : ℝ) 1 :=
    fun a => ⟨v a, by
      rw [← continuousLinearMap_range_cardinalitySectorProjectorL2_eq_eigenspace
        Q s.card hIdempotent hComm hsLe]
      exact ⟨v a,
        continuousLinearMap_cardinalitySectorProjectorL2_apply_eq_self_of_mem_jointSectorSubmoduleL2
          Q s.card s hComm rfl (hMem a)⟩⟩
  have hwLinearIndependent : LinearIndependent ℝ w := by
    apply LinearIndependent.of_comp
      (Module.End.genEigenspace
        ((∑ i : ι, Q i).toLinearMap)
        (s.card : ℝ) 1).subtype
    simpa [w, Function.comp_def] using hLinearIndependent
  exact hwLinearIndependent.aleph0_le_rank

/-- Rational cosine coordinate on a concrete algebraic rotation curve. -/
noncomputable def specialUnitaryTwoRationalRotationCos (t : ℝ) : ℝ :=
  (1 - t ^ 2) / (1 + t ^ 2)

/-- Rational sine coordinate on a concrete algebraic rotation curve. -/
noncomputable def specialUnitaryTwoRationalRotationSin (t : ℝ) : ℝ :=
  (2 * t) / (1 + t ^ 2)

/-- The rational rotation coordinates lie on the unit circle. -/
theorem specialUnitaryTwoRationalRotationCos_sq_add_sin_sq (t : ℝ) :
    specialUnitaryTwoRationalRotationCos t ^ 2 +
        specialUnitaryTwoRationalRotationSin t ^ 2 = 1 := by
  have hDen : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  unfold specialUnitaryTwoRationalRotationCos
    specialUnitaryTwoRationalRotationSin
  field_simp [hDen]
  ring

/-- The real rational rotation matrix, viewed inside complex matrices. -/
noncomputable def specialUnitaryTwoRationalRotationMatrix (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![((specialUnitaryTwoRationalRotationCos t : ℝ) : ℂ),
      ((specialUnitaryTwoRationalRotationSin t : ℝ) : ℂ);
    -((specialUnitaryTwoRationalRotationSin t : ℝ) : ℂ),
      ((specialUnitaryTwoRationalRotationCos t : ℝ) : ℂ)]

/-- A concrete one-parameter rational curve in `SU(2)`. -/
noncomputable def specialUnitaryTwoRationalRotation (t : ℝ) :
    SpecialUnitaryMatrixGroup 2 := by
  refine ⟨specialUnitaryTwoRationalRotationMatrix t, ?_⟩
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [specialUnitaryTwoRationalRotationMatrix, Matrix.mul_apply,
        Fin.sum_univ_two,
        specialUnitaryTwoRationalRotationCos_sq_add_sin_sq]
  · simp [specialUnitaryTwoRationalRotationMatrix, Matrix.det_fin_two,
      specialUnitaryTwoRationalRotationCos_sq_add_sin_sq]

@[simp]
theorem specialUnitaryTwoRationalRotation_coe (t : ℝ) :
    ((specialUnitaryTwoRationalRotation t : SpecialUnitaryMatrixGroup 2) :
      Matrix (Fin 2) (Fin 2) ℂ) =
      specialUnitaryTwoRationalRotationMatrix t := by
  rfl

/-- Wilson energy along the rational rotation curve. -/
theorem specialUnitaryWilsonPlaquetteEnergy_two_rationalRotation (t : ℝ) :
    specialUnitaryWilsonPlaquetteEnergy 2
        (specialUnitaryTwoRationalRotation t) =
      2 * t ^ 2 / (1 + t ^ 2) := by
  have hDen : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  unfold specialUnitaryWilsonPlaquetteEnergy
  simp [specialUnitaryTwoRationalRotationMatrix, Matrix.trace,
    Fin.sum_univ_two, specialUnitaryTwoRationalRotationCos]
  field_simp [hDen]
  ring

/-- The identity background configuration used for difference evaluation. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoIdentityConfiguration :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
  fun _ => 1

/-- Replace the distinguished link in the identity background by the `n`th
rational rotation. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoRationalRotationConfiguration
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
    periodicHypercubicThreeSpecialUnitaryTwoIdentityConfiguration
    periodicHypercubicThreeOriginAxisZeroTarget
    (specialUnitaryTwoRationalRotation (n : ℝ))

/-- Explicit Wilson-energy values on the countable rational rotation family. -/
noncomputable def specialUnitaryTwoRationalRotationEnergySequence (n : ℕ) : ℝ :=
  2 * (n : ℝ) ^ 2 / (1 + (n : ℝ) ^ 2)

@[simp]
theorem periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_identityConfiguration :
    periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF
        periodicHypercubicThreeSpecialUnitaryTwoIdentityConfiguration = 0 := by
  simp [periodicHypercubicThreeSpecialUnitaryTwoIdentityConfiguration,
    periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_apply]

@[simp]
theorem periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_rationalRotationConfiguration
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF
        (periodicHypercubicThreeSpecialUnitaryTwoRationalRotationConfiguration n) =
      specialUnitaryTwoRationalRotationEnergySequence n := by
  simp [periodicHypercubicThreeSpecialUnitaryTwoRationalRotationConfiguration,
    periodicHypercubicThreeSpecialUnitaryTwoIdentityConfiguration,
    periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_apply,
    specialUnitaryTwoRationalRotationEnergySequence,
    specialUnitaryWilsonPlaquetteEnergy_two_rationalRotation]

/-- The rational-rotation Wilson-energy sequence is injective. -/
theorem specialUnitaryTwoRationalRotationEnergySequence_injective :
    Function.Injective specialUnitaryTwoRationalRotationEnergySequence := by
  intro m n hmn
  have hmDen : (1 + (m : ℝ) ^ 2 : ℝ) ≠ 0 := by positivity
  have hnDen : (1 + (n : ℝ) ^ 2 : ℝ) ≠ 0 := by positivity
  change
    2 * (m : ℝ) ^ 2 / (1 + (m : ℝ) ^ 2) =
      2 * (n : ℝ) ^ 2 / (1 + (n : ℝ) ^ 2) at hmn
  field_simp [hmDen, hnDen] at hmn
  have hSq : (m : ℝ) ^ 2 = (n : ℝ) ^ 2 := by nlinarith
  have hReal : (m : ℝ) = (n : ℝ) := by
    nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity,
      show (0 : ℝ) ≤ (n : ℝ) by positivity]
  exact_mod_cast hReal

/-- The rational-rotation energy sequence is transcendental as an element of the
function algebra `ℕ → ℝ`, because its range is infinite. -/
theorem specialUnitaryTwoRationalRotationEnergySequence_transcendental :
    Transcendental ℝ specialUnitaryTwoRationalRotationEnergySequence := by
  rw [transcendental_iff]
  intro p hp
  apply Polynomial.eq_zero_of_infinite_isRoot p
  have hRangeInfinite :
      (Set.range specialUnitaryTwoRationalRotationEnergySequence).Infinite :=
    Set.infinite_range_of_injective
      specialUnitaryTwoRationalRotationEnergySequence_injective
  refine hRangeInfinite.mono ?_
  intro x hx
  rcases hx with ⟨n, rfl⟩
  have hn := congrFun hp n
  simpa using hn

/-- Positive powers of the rational-rotation energy sequence are linearly
independent. -/
theorem specialUnitaryTwoRationalRotationEnergySequence_positivePowers_linearIndependent :
    LinearIndependent ℝ
      (fun n : ℕ => fun m : ℕ =>
        specialUnitaryTwoRationalRotationEnergySequence m ^ (n + 1)) := by
  have hAevalInjective :
      Function.Injective
        (Polynomial.aeval specialUnitaryTwoRationalRotationEnergySequence) := by
    intro p q hpq
    apply sub_eq_zero.mp
    apply
      (transcendental_iff.mp
        specialUnitaryTwoRationalRotationEnergySequence_transcendental)
    rw [map_sub, hpq, sub_self]
  have hAll :
      LinearIndependent ℝ
        (fun n : ℕ =>
          specialUnitaryTwoRationalRotationEnergySequence ^ n) := by
    have hMapped :=
      (Polynomial.basisMonomials ℝ).linearIndependent.map'
        (Polynomial.aeval
          specialUnitaryTwoRationalRotationEnergySequence).toLinearMap
        (LinearMap.ker_eq_bot.mpr hAevalInjective)
    simpa [Function.comp_def, Polynomial.coe_basisMonomials] using hMapped
  have hPositive := hAll.comp Nat.succ Nat.succ_injective
  simpa [Function.comp_def, Pi.pow_apply, Nat.succ_eq_add_one] using hPositive

/-- The positive power of the distinguished-coordinate Wilson energy. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF
    (n : ℕ) :
    BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ :=
  periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF ^ (n + 1)

/-- Center each positive Wilson-energy power by the exact beta-zero target-link
conditional expectation. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPowerFluctuationBCF
    (n : ℕ) :
    BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ :=
  periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF n -
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      periodicHypercubicThreeOriginAxisZeroTarget
      (periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF n)

/-- Difference evaluation between the `n`th rational-rotation configuration and
the identity background. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoRationalRotationDifferenceEvaluationLinearMap :
    BoundedContinuousFunction
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ →ₗ[ℝ]
      (ℕ → ℝ) where
  toFun F n :=
    F (periodicHypercubicThreeSpecialUnitaryTwoRationalRotationConfiguration n) -
      F periodicHypercubicThreeSpecialUnitaryTwoIdentityConfiguration
  map_add' F G := by
    funext n
    simp
    ring
  map_smul' a F := by
    funext n
    simp
    ring

/-- Difference evaluation kills the projected constant-on-target-fiber term and
returns the corresponding positive power of the explicit energy sequence. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoRationalRotationDifferenceEvaluationLinearMap_apply_powerFluctuationBCF
    (n m : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoRationalRotationDifferenceEvaluationLinearMap
        (periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPowerFluctuationBCF n) m =
      specialUnitaryTwoRationalRotationEnergySequence m ^ (n + 1) := by
  have hProjection :=
    continuous_compact_oriented_singleLinkHeatBathProjection_replaceLink
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      (periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF n)
      periodicHypercubicThreeSpecialUnitaryTwoIdentityConfiguration
      periodicHypercubicThreeOriginAxisZeroTarget
      (specialUnitaryTwoRationalRotation (m : ℝ))
  change
    ((periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF n)
        (periodicHypercubicThreeSpecialUnitaryTwoRationalRotationConfiguration m) -
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        periodicHypercubicThreeOriginAxisZeroTarget
        (periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF n)
        (periodicHypercubicThreeSpecialUnitaryTwoRationalRotationConfiguration m)) -
      ((periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF n)
          periodicHypercubicThreeSpecialUnitaryTwoIdentityConfiguration -
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          periodicHypercubicThreeOriginAxisZeroTarget
          (periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF n)
          periodicHypercubicThreeSpecialUnitaryTwoIdentityConfiguration) =
      specialUnitaryTwoRationalRotationEnergySequence m ^ (n + 1)
  have hProjection' :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          periodicHypercubicThreeOriginAxisZeroTarget
          (periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF n)
          (periodicHypercubicThreeSpecialUnitaryTwoRationalRotationConfiguration m) =
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          periodicHypercubicThreeOriginAxisZeroTarget
          (periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF n)
          periodicHypercubicThreeSpecialUnitaryTwoIdentityConfiguration := by
    simpa [periodicHypercubicThreeSpecialUnitaryTwoRationalRotationConfiguration]
      using hProjection
  rw [hProjection']
  simp [periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF]

/-- The centered positive-power bounded-continuous observables are linearly
independent. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPowerFluctuationBCF_linearIndependent :
    LinearIndependent ℝ
      periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPowerFluctuationBCF := by
  apply LinearIndependent.of_comp
    periodicHypercubicThreeSpecialUnitaryTwoRationalRotationDifferenceEvaluationLinearMap
  simpa [Function.comp_def,
    periodicHypercubicThreeSpecialUnitaryTwoRationalRotationDifferenceEvaluationLinearMap_apply_powerFluctuationBCF]
    using
      specialUnitaryTwoRationalRotationEnergySequence_positivePowers_linearIndependent

/-- The injective linear passage from bounded-continuous observables to the
actual Gibbs `L²` space. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoGibbsL2RepresentativeBCFLinearMap :
    BoundedContinuousFunction
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ →ₗ[ℝ]
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure where
  toFun F :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF F
  map_add' F G := by
    simp [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
  map_smul' a F := by
    simp [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]

/-- The bounded-continuous to Gibbs-`L²` linear map is injective. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoGibbsL2RepresentativeBCFLinearMap_injective :
    Function.Injective
      periodicHypercubicThreeSpecialUnitaryTwoGibbsL2RepresentativeBCFLinearMap := by
  intro F G hFG
  change
    BoundedContinuousFunction.toLp
        2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure ℝ F =
      BoundedContinuousFunction.toLp
        2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure ℝ G at hFG
  exact
    (BoundedContinuousFunction.toLp_injective
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) hFG

/-- The countable actual Gibbs-`L²` family obtained from the centered positive
Wilson-energy powers. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2
    (n : ℕ) :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
    (periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPowerFluctuationBCF n)

/-- The actual countable Gibbs-`L²` one-link power-fluctuation family is linearly
independent. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2_linearIndependent :
    LinearIndependent ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2 := by
  have hMapped :=
    periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPowerFluctuationBCF_linearIndependent.map'
      periodicHypercubicThreeSpecialUnitaryTwoGibbsL2RepresentativeBCFLinearMap
      (LinearMap.ker_eq_bot.mpr
        periodicHypercubicThreeSpecialUnitaryTwoGibbsL2RepresentativeBCFLinearMap_injective)
  simpa [Function.comp_def,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2,
    periodicHypercubicThreeSpecialUnitaryTwoGibbsL2RepresentativeBCFLinearMap]
    using hMapped

/-- The `L²` family is exactly the target-link fluctuation of the corresponding
uncentered positive-power representative. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2_eq_target_fluctuation
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2 n =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeOriginAxisZeroTarget
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          (periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF n)) := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero]
  simp [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2,
    periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPowerFluctuationBCF,
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]

/-- The distinguished fluctuation projection fixes every member of the countable
power family. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2_target_fluctuation_eq_self
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeOriginAxisZeroTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2 n) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2 n := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2_eq_target_fluctuation]
  exact
    continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply_fluctuation
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget _

/-- Every other one-link fluctuation annihilates the uncentered target-coordinate
positive-power representative. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerL2_fluctuation_eq_zero_of_ne
    (n : ℕ)
    (source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hSource : source ≠ periodicHypercubicThreeOriginAxisZeroTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        source
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          (periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF n)) = 0 := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  have hFiber :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
        source
        (periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF n) := by
    intro A B hAgree
    simp only [periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF,
      BoundedContinuousFunction.coe_pow]
    congr 1
    exact hAgree periodicHypercubicThreeOriginAxisZeroTarget (Ne.symm hSource)
  have hBCF :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
          source
          (periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF n) =
        periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF n := by
    ext A
    exact congrFun
      (continuous_compact_oriented_singleLinkHeatBathProjection_fixes
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
        (periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerBCF n)
        source hFiber) A
  rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero]
  rw [hBCF, sub_self]

/-- Every non-target fluctuation projection annihilates every member of the
countable target-link power family. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2_fluctuation_eq_zero_of_ne
    (n : ℕ)
    (source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hSource : source ≠ periodicHypercubicThreeOriginAxisZeroTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        source
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2 n) = 0 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2_eq_target_fluctuation]
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
    source periodicHypercubicThreeOriginAxisZeroTarget]
  rw [periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyPositivePowerL2_fluctuation_eq_zero_of_ne
    n source hSource]
  simp

/-- Every member of the countable family lies in the exact singleton joint
sector at the distinguished physical link. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_oneLinkPowerFluctuationL2_mem_singleton_fluctuationJointSector
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2 n ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        {periodicHypercubicThreeOriginAxisZeroTarget} := by
  exact
    continuousLinearMap_mem_singleton_jointSectorSubmoduleL2_of_eq_self_of_eq_zero_of_ne
      (Q := fun edge :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
            edge)
      periodicHypercubicThreeOriginAxisZeroTarget
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2_target_fluctuation_eq_self
        n)
      (fun source hSource =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2_fluctuation_eq_zero_of_ne
          n source hSource)

/-- The actual beta-zero heat-bath eigenspace at eigenvalue one has Cardinal rank
at least `aleph0`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_one_heatBathCardinalityEigenspaceL2 :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
          1) := by
  let Q := fun edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
      edge
  have hGeneric :=
    continuousLinearMap_aleph0_le_rank_cardinalityEigenspace_of_linearIndependent_mem_jointSectorL2
      (Q := Q)
      (s := {periodicHypercubicThreeOriginAxisZeroTarget})
      (v := periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2)
      (fun edge f =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
          edge f)
      (fun target source f =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
          target source f)
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2_linearIndependent
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_oneLinkPowerFluctuationL2_mem_singleton_fluctuationJointSector
  simpa [Q, Finset.card_singleton,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_univ_sum_fluctuationL2]
    using hGeneric

/-- The range of the actual cardinality-one projector also has rank at least
`aleph0`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_range_one_fluctuationCardinalityProjectorL2 :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            1).toLinearMap) := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_heatBathCardinalityEigenspaceL2
    1 (by omega)]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_one_heatBathCardinalityEigenspaceL2

/-- The actual cardinality-one joint-sector sum has rank at least `aleph0`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_one_fluctuationCardinalityJointSectorSumSubmoduleL2 :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
          1) := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_heatBathCardinalityEigenspaceL2
    1 (by omega)]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_one_heatBathCardinalityEigenspaceL2

/-- Compact receipt for the first positive-cardinality infinite-rank sector. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneEigenspaceInfiniteRankL2Receipt :
    Prop :=
  LinearIndependent ℝ
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2 ∧
  (∀ n : ℕ,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2 n ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        {periodicHypercubicThreeOriginAxisZeroTarget}) ∧
  Cardinal.aleph0 ≤
    Module.rank ℝ
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
        1) ∧
  Cardinal.aleph0 ≤
    Module.rank ℝ
      (LinearMap.range
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          1).toLinearMap) ∧
  Cardinal.aleph0 ≤
    Module.rank ℝ
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
        1)

/-- The eigenvalue-one infinite-rank receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneEigenspaceInfiniteRankL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneEigenspaceInfiniteRankL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneLinkPowerFluctuationL2_linearIndependent,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_oneLinkPowerFluctuationL2_mem_singleton_fluctuationJointSector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_one_heatBathCardinalityEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_range_one_fluctuationCardinalityProjectorL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_one_fluctuationCardinalityJointSectorSumSubmoduleL2⟩

end

end MathlibAnalytic
end MGAP4D
