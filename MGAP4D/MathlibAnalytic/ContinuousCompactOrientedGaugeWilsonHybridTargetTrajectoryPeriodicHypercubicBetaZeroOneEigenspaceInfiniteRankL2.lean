import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroZeroEigenspaceMultiplicityOneL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityOneSingletonWitnessL2
import Mathlib.LinearAlgebra.Dimension.Basic
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

/-- Rational cosine coordinate for the dedicated eigenvalue-one infinite-rank
witness curve. -/
noncomputable def specialUnitaryTwoBetaZeroOneInfiniteRankRationalCos
    (t : ℝ) : ℝ :=
  (1 - t ^ 2) / (1 + t ^ 2)

/-- Rational sine coordinate for the dedicated eigenvalue-one infinite-rank
witness curve. -/
noncomputable def specialUnitaryTwoBetaZeroOneInfiniteRankRationalSin
    (t : ℝ) : ℝ :=
  (2 * t) / (1 + t ^ 2)

/-- The dedicated rational coordinates lie on the unit circle. -/
theorem specialUnitaryTwoBetaZeroOneInfiniteRankRationalCos_sq_add_sin_sq
    (t : ℝ) :
    specialUnitaryTwoBetaZeroOneInfiniteRankRationalCos t ^ 2 +
        specialUnitaryTwoBetaZeroOneInfiniteRankRationalSin t ^ 2 = 1 := by
  have hDen : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  unfold specialUnitaryTwoBetaZeroOneInfiniteRankRationalCos
    specialUnitaryTwoBetaZeroOneInfiniteRankRationalSin
  field_simp [hDen]
  ring

/-- Complex-coefficient form of the rational unit-circle identity. -/
@[simp]
theorem specialUnitaryTwoBetaZeroOneInfiniteRankRationalCos_mul_add_sin_mul_complex
    (t : ℝ) :
    ((specialUnitaryTwoBetaZeroOneInfiniteRankRationalCos t : ℝ) : ℂ) *
          ((specialUnitaryTwoBetaZeroOneInfiniteRankRationalCos t : ℝ) : ℂ) +
        ((specialUnitaryTwoBetaZeroOneInfiniteRankRationalSin t : ℝ) : ℂ) *
          ((specialUnitaryTwoBetaZeroOneInfiniteRankRationalSin t : ℝ) : ℂ) =
      1 := by
  exact_mod_cast
    (by
      simpa [pow_two] using
        specialUnitaryTwoBetaZeroOneInfiniteRankRationalCos_sq_add_sin_sq t)

/-- The real rational rotation matrix, embedded into complex matrices. -/
noncomputable def specialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationMatrix
    (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((specialUnitaryTwoBetaZeroOneInfiniteRankRationalCos t : ℝ) : ℂ),
      ((specialUnitaryTwoBetaZeroOneInfiniteRankRationalSin t : ℝ) : ℂ);
    -((specialUnitaryTwoBetaZeroOneInfiniteRankRationalSin t : ℝ) : ℂ),
      ((specialUnitaryTwoBetaZeroOneInfiniteRankRationalCos t : ℝ) : ℂ)]

/-- The trace of the dedicated rational rotation matrix. -/
@[simp]
theorem specialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationMatrix_trace
    (t : ℝ) :
    Matrix.trace
        (specialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationMatrix t) =
      (((2 * specialUnitaryTwoBetaZeroOneInfiniteRankRationalCos t : ℝ) : ℂ)) := by
  simp [specialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationMatrix,
    Matrix.trace, Fin.sum_univ_two]
  ring

/-- A concrete rational one-parameter curve in `SU(2)`. -/
noncomputable def specialUnitaryTwoBetaZeroOneInfiniteRankRationalRotation
    (t : ℝ) : SpecialUnitaryMatrixGroup 2 := by
  refine ⟨specialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationMatrix t, ?_⟩
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [specialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationMatrix,
        Matrix.mul_apply, Fin.sum_univ_two, add_comm] <;>
      ring
  · simp [specialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationMatrix,
      Matrix.det_fin_two, add_comm]

@[simp]
theorem specialUnitaryTwoBetaZeroOneInfiniteRankRationalRotation_coe
    (t : ℝ) :
    ((specialUnitaryTwoBetaZeroOneInfiniteRankRationalRotation t :
        SpecialUnitaryMatrixGroup 2) : Matrix (Fin 2) (Fin 2) ℂ) =
      specialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationMatrix t := by
  rfl

/-- Wilson energy along the dedicated rational `SU(2)` curve. -/
theorem specialUnitaryWilsonPlaquetteEnergy_two_betaZeroOneInfiniteRankRationalRotation
    (t : ℝ) :
    specialUnitaryWilsonPlaquetteEnergy 2
        (specialUnitaryTwoBetaZeroOneInfiniteRankRationalRotation t) =
      2 * t ^ 2 / (1 + t ^ 2) := by
  have hDen : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  change
    1 -
        (Matrix.trace
          (specialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationMatrix t)).re /
          (2 : ℝ) =
      2 * t ^ 2 / (1 + t ^ 2)
  rw [specialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationMatrix_trace]
  simp only [Complex.ofReal_re]
  unfold specialUnitaryTwoBetaZeroOneInfiniteRankRationalCos
  field_simp [hDen]
  ring

/-- The identity background used only by the eigenvalue-one infinite-rank
witness construction. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
  fun _ => 1

/-- Replace the distinguished link in the identity background by the `n`th
rational rotation. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationConfiguration
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration
    periodicHypercubicThreeOriginAxisZeroTarget
    (specialUnitaryTwoBetaZeroOneInfiniteRankRationalRotation (n : ℝ))

/-- Explicit Wilson-energy values along the countable rational rotation family. -/
noncomputable def specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence
    (n : ℕ) : ℝ :=
  2 * (n : ℝ) ^ 2 / (1 + (n : ℝ) ^ 2)

@[simp]
theorem periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_betaZeroOneInfiniteRankIdentityConfiguration :
    periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration =
      0 := by
  simp only [periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_apply]
  change specialUnitaryWilsonPlaquetteEnergy 2
      (1 : SpecialUnitaryMatrixGroup 2) = 0
  unfold specialUnitaryWilsonPlaquetteEnergy
  norm_num [Matrix.trace, Fin.sum_univ_two]

@[simp]
theorem periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_betaZeroOneInfiniteRankRationalRotationConfiguration
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationConfiguration
          n) =
      specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence n := by
  simp [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationConfiguration,
    periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_apply,
    specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence,
    specialUnitaryWilsonPlaquetteEnergy_two_betaZeroOneInfiniteRankRationalRotation]

/-- The dedicated rational-rotation Wilson-energy sequence is injective. -/
theorem specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence_injective :
    Function.Injective specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence := by
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

end

end MathlibAnalytic
end MGAP4D
