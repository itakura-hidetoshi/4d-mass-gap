import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusResidualGaugeOneSlabKernelInvariance
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobMixtureCoordinateInfluence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The repository's chosen strictly-positive ambient Perron ground is
pointwise residual-gauge invariant.  This is not a new Perron assumption: it
follows because the chosen ground is an exact fixed vector of the actual
unfixed-gauge transfer and every such fixed vector lies in the Gauss-invariant
submodule. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_smul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy (g • A) =
      finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy A := by
  have hInvariant :=
    finiteEvenFourTorusZ2UnfixedGauge_fixedVector_mem_invariant
      H β energyIdentity energyNontrivial hβ hEnergy
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_fixed
        H β energyIdentity energyNontrivial hβ hEnergy)
  exact hInvariant g A

/-- The temporal-gauge chosen-ground raw posterior is invariant under the
diagonal residual-gauge action on its environment and hidden slice. -/
theorem finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight_smul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight
        H β energyIdentity energyNontrivial hβ hEnergy
        (g • environment) (g • hidden) =
      finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight
        H β energyIdentity energyNontrivial hβ hEnergy
        environment hidden := by
  unfold finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight
  rw [finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul,
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_smul]

/-- Consequently the total mass of the temporal raw posterior is unchanged by
residual-gauge transformation of the environment. -/
theorem finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorPartition_smul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteRealWeightPartition
        (finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight
          H β energyIdentity energyNontrivial hβ hEnergy
          (g • environment)) =
      finiteRealWeightPartition
        (finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight
          H β energyIdentity energyNontrivial hβ hEnergy
          environment) := by
  classical
  unfold finiteRealWeightPartition
  refine Fintype.sum_equiv
    (finiteMulActionEquiv
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H) g) _ _ ?_
  intro hidden
  exact
    finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight_smul
      H β energyIdentity energyNontrivial hβ hEnergy
      g environment hidden

/-- The effective latent-index weight `scale × componentPartition` is exactly
the total mass of the corresponding temporal-gauge raw posterior. -/
theorem finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexWeight_eq_rawPosteriorPartition
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) :
    finitePositiveWeightMixtureIndexWeight
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale
          H β energyIdentity energyNontrivial environment)
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight
          H β energyIdentity energyNontrivial hβ hEnergy environment)
        g =
      finiteRealWeightPartition
        (finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight
          H β energyIdentity energyNontrivial hβ hEnergy
          (g • environment)) := by
  classical
  unfold finitePositiveWeightMixtureIndexWeight
    finitePositiveWeightMixtureComponentPartition
    finiteRealWeightPartition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro hidden _hhidden
  simpa [finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale,
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight] using
    (finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight_eq_scale_mul
      H β energyIdentity energyNontrivial hβ hEnergy
      (g • environment) hidden).symm

/-- Every effective latent residual-gauge index has the same weight, namely
the untransformed raw-posterior partition. -/
theorem finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexWeight_eq_environmentRawPosteriorPartition
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) :
    finitePositiveWeightMixtureIndexWeight
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale
          H β energyIdentity energyNontrivial environment)
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight
          H β energyIdentity energyNontrivial hβ hEnergy environment)
        g =
      finiteRealWeightPartition
        (finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight
          H β energyIdentity energyNontrivial hβ hEnergy environment) := by
  calc
    finitePositiveWeightMixtureIndexWeight
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale
          H β energyIdentity energyNontrivial environment)
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight
          H β energyIdentity energyNontrivial hβ hEnergy environment)
        g =
      finiteRealWeightPartition
        (finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight
          H β energyIdentity energyNontrivial hβ hEnergy
          (g • environment)) :=
      finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexWeight_eq_rawPosteriorPartition
        H β energyIdentity energyNontrivial hβ hEnergy environment g
    _ =
      finiteRealWeightPartition
        (finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight
          H β energyIdentity energyNontrivial hβ hEnergy environment) :=
      finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorPartition_smul
        H β energyIdentity energyNontrivial hβ hEnergy g environment

/-- The latent residual-gauge law in the actual geometric Perron Doob mixture
is exactly uniform.  In particular it does not depend on the boundary
environment. -/
theorem finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbability_eq_card_inv
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) :
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
      C β hβ hβCutoff H environment).probability g =
      (Fintype.card
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) : ℝ)⁻¹ := by
  classical
  let scale :=
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale
      H β energyIdentity energyNontrivial environment
  let weight :=
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le environment
  let mass :=
    finiteRealWeightPartition
      (finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
  have hscale : ∀ a, 0 < scale a := by
    intro a
    exact
      finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale_pos
        H β energyIdentity energyNontrivial environment a
  have hweight : ∀ a hidden, 0 < weight a hidden := by
    intro a hidden
    exact
      finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight_pos
        C β hβ hβCutoff H environment a hidden
  have hIndexWeight :
      ∀ a : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        finitePositiveWeightMixtureIndexWeight scale weight a = mass := by
    intro a
    simpa [scale, weight, mass] using
      finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexWeight_eq_environmentRawPosteriorPartition
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment a
  have hmass : 0 < mass := by
    rw [← hIndexWeight (1 : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)]
    exact
      finitePositiveWeightMixtureIndexWeight_pos
        scale weight hscale hweight 1
  have hIndexPartition :
      finitePositiveWeightMixtureIndexPartition scale weight =
        (Fintype.card
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) : ℝ) * mass := by
    unfold finitePositiveWeightMixtureIndexPartition
    calc
      (∑ a : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        finitePositiveWeightMixtureIndexWeight scale weight a) =
          ∑ _a : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H, mass := by
        apply Finset.sum_congr rfl
        intro a _ha
        exact hIndexWeight a
      _ =
          (Fintype.card
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) : ℝ) * mass := by
        simp
  have hcard :
      (Fintype.card
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData,
    finitePositiveWeightMixtureIndexProbabilityData,
    finiteRealWeightProbabilityData,
    finiteRealWeightProbability]
  change
    finitePositiveWeightMixtureIndexWeight scale weight g /
        finitePositiveWeightMixtureIndexPartition scale weight =
      (Fintype.card
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) : ℝ)⁻¹
  rw [hIndexWeight g, hIndexPartition]
  field_simp [hcard, ne_of_gt hmass]

/-- The latent residual-gauge index laws attached to any two boundary
configurations are pointwise identical. -/
theorem finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbability_environment_independent
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) :
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
      C β hβ hβCutoff H left).probability g =
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
        C β hβ hβCutoff H right).probability g := by
  rw [
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbability_eq_card_inv,
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbability_eq_card_inv]

/-- Hence the unhalved `L¹` distance between any two latent residual-gauge
index laws is exactly zero. -/
theorem finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbability_l1Distance_eq_zero
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
      C β hβ hβCutoff H left).l1Distance
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
        C β hβ hβCutoff H right) = 0 := by
  unfold FiniteRealProbabilityData.l1Distance
  apply Finset.sum_eq_zero
  intro g _hg
  rw [
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbability_environment_independent
      C β hβ hβCutoff H left right g]
  simp

/-- The overlap coupling of the two latent residual-gauge laws is therefore
supported entirely on the diagonal. -/
theorem finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCoupling_disagreementMass_eq_zero
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
      C β hβ hβCutoff H left right).disagreementMass = 0 := by
  rw [
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCoupling_disagreementMass_eq_half_mul_l1Distance,
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbability_l1Distance_eq_zero]
  ring

/-- The coordinatewise mismatch of the full actual geometric Doob mixture is
controlled by same-index posterior transport alone: the latent-index
obstruction vanishes exactly by residual-gauge symmetry. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch_le_diagonal
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H)
    (diagonalBound :
      FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H → ℝ)
    (hDiagonal :
      ∀ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedCoordinateMismatch
            C β hβ hβCutoff H left right g g source ≤ diagonalBound g) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch
        C β hβ hβCutoff H left right source ≤
      ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
          C β hβ hβCutoff H left right).joint g g * diagonalBound g := by
  have h :=
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch_le_diagonal_add_halfIndexL1
      C β hβ hβCutoff H left right source diagonalBound hDiagonal
  rw [
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbability_l1Distance_eq_zero]
    at h
  simpa using h

end

end MathlibAnalytic
end MGAP4D
