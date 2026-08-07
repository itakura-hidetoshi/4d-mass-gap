import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeConfigurationKernelNontrivial
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepBoltzmannOrbitFiberBalance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Bundled direct finest-to-coarsest configuration hom for two canonical
doubling steps. -/
noncomputable def finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom
    (H : ℕ) :
    FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) →*
      FiniteEvenFourTorusZ2SliceConfiguration H :=
  (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).comp
    (finiteEvenFourTorusZ2SliceConfigurationCoarseHom
      (finiteEvenFourTorusDoubleRefinement H))

@[simp] theorem finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom_apply
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H A =
      finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
          (finiteEvenFourTorusDoubleRefinement H) A) :=
  rfl

/-- The direct two-step configuration hom is surjective. -/
theorem finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom_surjective
    (H : ℕ) :
    Function.Surjective
      (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H) := by
  intro B
  rcases finiteEvenFourTorusZ2SliceConfigurationCoarseHom_surjective H B with
    ⟨B₁, hB₁⟩
  rcases finiteEvenFourTorusZ2SliceConfigurationCoarseHom_surjective
      (finiteEvenFourTorusDoubleRefinement H) B₁ with
    ⟨B₂, hB₂⟩
  exact ⟨B₂, by simp [finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom,
    hB₂, hB₁]⟩

/-- Constant direct two-step embedding scale, expressed as the product of the
two one-step configuration-cardinality scales. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale
    (H : ℕ) : ℝ :=
  finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale
      (finiteEvenFourTorusDoubleRefinement H) *
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H

/-- The actual direct two-step pointwise scale is configuration independent. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale_eq_cardinality
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_cardinality,
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_cardinality]

/-- The constant direct two-step scale is strictly positive. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale_pos
    (H : ℕ) :
    0 < finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H := by
  exact mul_pos
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale_pos
      (finiteEvenFourTorusDoubleRefinement H))
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale_pos H)

/-- At `β = 0`, the direct finest Boltzmann coefficient is exactly direct
kernel multiplicity times target orbit mass times the constant two-step scale. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannFineOrbitFiberCoefficient_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannFineOrbitFiberCoefficient
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A q =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H *
        (Fintype.card (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker : ℝ) *
        finiteGroupOrbitMass
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H) q := by
  classical
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannFineOrbitFiberCoefficient
    finiteGroupOrbitFiberCoefficient
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]
  simp_rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale_eq_cardinality]
  calc
    (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)),
      if finiteGroupOrbitClass
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H)
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
              (finiteEvenFourTorusDoubleRefinement H) B)) = q then
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H
      else 0) =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H *
        (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H)),
          if finiteGroupOrbitClass
              (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
              (FiniteEvenFourTorusZ2SliceConfiguration H)
              (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H B) = q then
            (1 : ℝ)
          else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro B _hB
        by_cases hBq : finiteGroupOrbitClass
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H)
            (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H B) = q
        · simp [finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom_apply, hBq]
        · simp [finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom_apply, hBq]
    _ = finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H *
        ((Fintype.card (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker : ℝ) *
          finiteGroupOrbitMass
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H) q) := by
      rw [finiteSurjectiveGroupHom_orbit_preimage_count
        (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H)
        (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom_surjective H) q]
    _ = _ := by ring

/-- At `β = 0`, the direct coarse coefficient has no finest-fibre
multiplicity. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannCoarseOrbitCoefficient_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannCoarseOrbitCoefficient
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A q =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H *
        finiteGroupOrbitMass
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H) q := by
  classical
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannCoarseOrbitCoefficient
    finiteGroupOrbitAggregateCoefficient
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale_eq_cardinality]
  unfold finiteGroupOrbitMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hbq : finiteGroupOrbitClass
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H) b = q
  · simp [hbq, eq_comm]
  · simp [hbq, eq_comm]

/-- The direct `β = 0` Boltzmann balance holds exactly when the composed
configuration coarse hom has singleton kernel. -/
theorem finiteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance_beta_zero_iff_card_ker_eq_one
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy ↔
      Fintype.card (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker = 1 := by
  constructor
  · intro hBalance
    let A := finiteEvenFourTorusZ2IdentitySlice
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
    let q := finiteEvenFourTorusZ2IdentityGaugeOrbit H
    have hEq := hBalance A q
    rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannFineOrbitFiberCoefficient_beta_zero,
      finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannCoarseOrbitCoefficient_beta_zero]
      at hEq
    have hc :
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H ≠ 0 :=
      ne_of_gt (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale_pos H)
    have hm :
        finiteGroupOrbitMass
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H) q ≠ 0 :=
      ne_of_gt (finiteGroupOrbitMass_pos _ _ q)
    have hkR :
        (Fintype.card (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker : ℝ) = 1 := by
      apply mul_right_cancel₀ hm
      apply mul_left_cancel₀ hc
      simpa [mul_assoc] using hEq
    exact_mod_cast hkR
  · intro hker A q
    rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannFineOrbitFiberCoefficient_beta_zero,
      finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannCoarseOrbitCoefficient_beta_zero]
    norm_cast at hker
    rw [hker]
    ring

/-- The composed direct two-step coarse hom also has nontrivial kernel. -/
noncomputable instance finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHomKerNontrivial
    (H : ℕ) :
    Nontrivial (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker := by
  classical
  let φ₁ := finiteEvenFourTorusZ2SliceConfigurationCoarseHom
    (finiteEvenFourTorusDoubleRefinement H)
  haveI : Nontrivial φ₁.ker :=
    finiteEvenFourTorusZ2SliceConfigurationCoarseHomKerNontrivial
      (finiteEvenFourTorusDoubleRefinement H)
  obtain ⟨k, hk⟩ := exists_ne (1 : φ₁.ker)
  let K : (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker :=
    ⟨k.1, by
      change finiteEvenFourTorusZ2SliceConfigurationCoarseHom H (φ₁ k.1) = 1
      rw [k.2]
      simp⟩
  have hK : K ≠ 1 := by
    intro h
    apply hk
    apply Subtype.ext
    exact congrArg Subtype.val h
  exact ⟨⟨1, K, hK⟩⟩

/-- Direct two-step kernel cardinality is strictly larger than one. -/
theorem finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom_card_ker_gt_one
    (H : ℕ) :
    1 < Fintype.card (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker := by
  exact Fintype.one_lt_card

/-- The direct two-step `β = 0` Boltzmann balance is genuinely false. -/
theorem finiteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance_beta_zero_false
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    ¬ FiniteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy := by
  intro hBalance
  have hker :=
    (finiteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance_beta_zero_iff_card_ker_eq_one
      H energyIdentity energyNontrivial hEnergy).1 hBalance
  exact (ne_of_gt
    (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom_card_ker_gt_one H)) hker

/-- Main direct Package-K obstruction: the actual direct two-step raw
cross-volume transfer residual is nonzero at `β = 0`. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_beta_zero_ne_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy ≠ 0 := by
  intro hZero
  have hBalance :=
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_boltzmannOrbitFiberBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy).1 hZero
  exact finiteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance_beta_zero_false
    H energyIdentity energyNontrivial hEnergy hBalance

end

end MathlibAnalytic
end MGAP4D
