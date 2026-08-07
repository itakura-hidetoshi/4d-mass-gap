import MGAP4D.MathlibAnalytic.FiniteGroupOrbitProbabilityEmbeddingScaleCancellation
import MGAP4D.MathlibAnalytic.FiniteSurjectiveGroupHomFiberMultiplicity
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeBoltzmannOrbitFiberBalance
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeConfigurationSurjectivity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The configuration-cardinality scalar hidden inside the actual one-step
normalized invariant embedding. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale
    (H : ℕ) : ℝ :=
  finiteGroupConfigurationCardinalityEmbeddingScale
    (FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (FiniteEvenFourTorusZ2SliceConfiguration H)

/-- All orbit-mass factors in the actual pointwise embedding scale cancel:
the scale is independent of the fine configuration and is exactly the square-
root ratio of coarse/fine configuration cardinalities. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_cardinality
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A =
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H := by
  let qf := finiteEvenFourTorusZ2FineGaugeOrbitOfConfiguration H A
  let qc := finiteEvenFourTorusZ2CoarseGaugeOrbitOfFineConfiguration H A
  unfold finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale
  change
    finiteGroupOrbitProbabilityEmbeddingScale
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
        (finiteEvenFourTorusDoubleRefinement H))
      (FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H))
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H) qf qc =
    finiteGroupConfigurationCardinalityEmbeddingScale
      (FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H))
      (FiniteEvenFourTorusZ2SliceConfiguration H)
  exact finiteGroupOrbitProbabilityEmbeddingScale_eq_cardinality
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
      (finiteEvenFourTorusDoubleRefinement H))
    (FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H) qf qc

/-- The actual cardinality scale is strictly positive. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale_pos
    (H : ℕ) :
    0 < finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H :=
  finiteGroupConfigurationCardinalityEmbeddingScale_pos
    (FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (FiniteEvenFourTorusZ2SliceConfiguration H)

/-- At `β = 0`, the fine Boltzmann orbit-fibre coefficient is exactly the
constant embedding scale times the kernel multiplicity of the configuration
coarse hom times the target orbit mass. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannFineOrbitFiberCoefficient_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannFineOrbitFiberCoefficient
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A q =
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H *
        (Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker : ℝ) *
        finiteGroupOrbitMass
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H) q := by
  classical
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannFineOrbitFiberCoefficient
    finiteGroupOrbitFiberCoefficient
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]
  simp_rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_cardinality]
  have hCount := finiteSurjectiveGroupHom_orbit_preimage_count
    (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H)
    (finiteEvenFourTorusZ2SliceConfigurationCoarseHom_surjective H) q
  change
    (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H),
      if finiteGroupOrbitClass
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H)
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B) = q then
        (1 : ℝ)
      else 0) =
      (Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker : ℝ) *
        finiteGroupOrbitMass
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H) q at hCount
  calc
    (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H),
      if finiteGroupOrbitClass
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H)
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B) = q then
        finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H
      else 0) =
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H *
        (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H),
          if finiteGroupOrbitClass
              (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
              (FiniteEvenFourTorusZ2SliceConfiguration H)
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B) = q then
            (1 : ℝ)
          else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro B _hB
        by_cases hBq : finiteGroupOrbitClass
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H)
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B) = q
        · rw [if_pos hBq, if_pos hBq, mul_one]
        · rw [if_neg hBq, if_neg hBq, mul_zero]
    _ = finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H *
        ((Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker : ℝ) *
          finiteGroupOrbitMass
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H) q) := by
      rw [hCount]
    _ = _ := by ring

/-- At `β = 0`, the coarse Boltzmann coefficient is the same positive
cardinality scale times the target orbit mass, with no fine-fibre
multiplicity. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannCoarseOrbitCoefficient_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannCoarseOrbitCoefficient
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A q =
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H *
        finiteGroupOrbitMass
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H) q := by
  classical
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannCoarseOrbitCoefficient
    finiteGroupOrbitAggregateCoefficient
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_cardinality]
  unfold finiteGroupOrbitMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hbq : finiteGroupOrbitClass
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H) b = q
  · have hqb : q = finiteGroupOrbitClass
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H) b := hbq.symm
    rw [if_pos hbq, if_pos hqb, mul_one]
  · have hqb : q ≠ finiteGroupOrbitClass
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H) b := by
      intro h
      exact hbq h.symm
    rw [if_neg hbq, if_neg hqb, mul_zero]

/-- The one-step `β = 0` Boltzmann balance holds exactly when the actual
configuration coarse hom has singleton kernel. -/
theorem finiteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance_beta_zero_iff_card_ker_eq_one
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy ↔
      Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker = 1 := by
  constructor
  · intro hBalance
    let A := finiteEvenFourTorusZ2IdentitySlice
      (finiteEvenFourTorusDoubleRefinement H)
    let q := finiteEvenFourTorusZ2IdentityGaugeOrbit H
    have hEq := hBalance A q
    rw [finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannFineOrbitFiberCoefficient_beta_zero,
      finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannCoarseOrbitCoefficient_beta_zero]
      at hEq
    have hcPos :
        0 < finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H :=
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale_pos H
    have hmPos :
        0 < finiteGroupOrbitMass
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H) q :=
      finiteGroupOrbitMass_pos _ _ q
    have hcmNe :
        finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H *
          finiteGroupOrbitMass
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H) q ≠ 0 :=
      mul_ne_zero (ne_of_gt hcPos) (ne_of_gt hmPos)
    have hFactor :
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H *
          finiteGroupOrbitMass
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H) q) *
          ((Fintype.card
            (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker : ℝ) - 1) = 0 := by
      calc
        _ = finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H *
              (Fintype.card
                (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker : ℝ) *
              finiteGroupOrbitMass
                (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
                (FiniteEvenFourTorusZ2SliceConfiguration H) q -
            finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H *
              finiteGroupOrbitMass
                (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
                (FiniteEvenFourTorusZ2SliceConfiguration H) q := by ring
        _ = 0 := sub_eq_zero.mpr hEq
    have hkSub :
        (Fintype.card
          (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker : ℝ) - 1 = 0 :=
      (mul_eq_zero.mp hFactor).resolve_left hcmNe
    have hkR :
        (Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker : ℝ) = 1 :=
      sub_eq_zero.mp hkSub
    exact_mod_cast hkR
  · intro hker A q
    have hkerR :
        (Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker : ℝ) = 1 := by
      exact_mod_cast hker
    rw [finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannFineOrbitFiberCoefficient_beta_zero,
      finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannCoarseOrbitCoefficient_beta_zero,
      hkerR]
    ring

/-- Consequently, the actual one-step raw transfer residual at `β = 0`
vanishes exactly when the configuration coarse hom has singleton kernel. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_beta_zero_eq_zero_iff_card_ker_eq_one
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0 ↔
      Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker = 1 := by
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_boltzmannOrbitFiberBalance]
  exact finiteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance_beta_zero_iff_card_ker_eq_one
    H energyIdentity energyNontrivial hEnergy

end

end MathlibAnalytic
end MGAP4D
