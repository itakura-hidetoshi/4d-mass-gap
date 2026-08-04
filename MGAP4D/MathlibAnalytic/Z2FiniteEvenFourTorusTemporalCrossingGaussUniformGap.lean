import MGAP4D.MathlibAnalytic.FiniteDimensionalCenteredPowerDecay
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGaussProjectedOneSlabTransfer
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusTemporalCrossingRawNormalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- The pure temporal-crossing Gram kernel is invariant under the simultaneous
residual gauge action on its two boundary slices. -/
theorem finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel_smul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel
        (g • A) (g • B) =
      (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
        H β energyIdentity energyNontrivial hβ hEnergy).kernel A B := by
  rw [finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel_eq_boltzmann,
    finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel_eq_boltzmann,
    finiteEvenFourTorusZ2TemporalGaugeCrossingAction_smul]

/-- Operator-norm normalized temporal-crossing transfer compressed to the
Gauss-invariant boundary Hilbert subspace. -/
noncomputable def finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
  finiteGroupInvariantCompressedNormalizedTransfer
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel
    (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel_smul
      H β energyIdentity energyNontrivial hβ hEnergy)

@[simp] theorem finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer_apply_coe
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    (finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer
      H β energyIdentity energyNontrivial hβ hEnergy f).1 =
      finiteKernelNormalizedOperator
        (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
          H β energyIdentity energyNontrivial hβ hEnergy).kernel f.1 :=
  rfl

/-- Symmetry of the normalized crossing transfer survives Gauss compression. -/
theorem finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer_isSymmetric
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric :=
  finiteGroupInvariantCompressedNormalizedTransfer_isSymmetric
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel_smul
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- Positivity of the normalized crossing transfer survives Gauss compression. -/
theorem finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer_quadratic_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    0 ≤ inner ℝ
      (finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer
        H β energyIdentity energyNontrivial hβ hEnergy f) f :=
  finiteGroupInvariantCompressedNormalizedTransfer_quadratic_nonneg
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel_smul
      H β energyIdentity energyNontrivial hβ hEnergy) f

/-- Total mass functional on the finite Gauss-invariant boundary Hilbert
subspace. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantMassLinearMap
    (H : ℕ) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ] ℝ :=
  { toFun := fun f => finiteFunctionMass f.1
    map_add' := by
      intro f g
      simp [finiteFunctionMass, Finset.sum_add_distrib]
    map_smul' := by
      intro c f
      simp [finiteFunctionMass, Finset.mul_sum] }

/-- The Gauss-compressed normalized crossing transfer preserves total mass. -/
theorem finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer_mass
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GaugeInvariantMassLinearMap H
        (finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer
          H β energyIdentity energyNontrivial hβ.le hEnergy.le f) =
      finiteEvenFourTorusZ2GaugeInvariantMassLinearMap H f := by
  change
    finiteFunctionMass
        (finiteKernelNormalizedOperator
          (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
            H β energyIdentity energyNontrivial hβ.le hEnergy.le).kernel f.1) =
      finiteFunctionMass f.1
  rw [finiteEvenFourTorusZ2TemporalGaugeCrossingNormalizedOperator_eq
    H β energyIdentity energyNontrivial hβ hEnergy]
  simpa [finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel] using
    finiteZ2GaugeNormalizedProductKernel_operator_mass
      (z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial)
      (FiniteEvenFourTorusSpatialLink H) f.1

/-- The same volume-independent Rayleigh rate holds after Gauss compression. -/
theorem finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer_rayleigh_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (hmass : finiteFunctionMass f.1 = 0) :
    inner ℝ
        (finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer
          H β energyIdentity energyNontrivial hβ.le hEnergy.le f) f ≤
      z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial * ‖f‖ ^ 2 := by
  change
    inner ℝ
        (finiteKernelNormalizedOperator
          (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
            H β energyIdentity energyNontrivial hβ.le hEnergy.le).kernel f.1) f.1 ≤
      z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial * ‖f.1‖ ^ 2
  rw [finiteEvenFourTorusZ2TemporalGaugeCrossingNormalizedOperator_eq
    H β energyIdentity energyNontrivial hβ hEnergy]
  exact finiteEvenFourTorusZ2NormalizedTemporalCrossing_rayleigh_le
    H β energyIdentity energyNontrivial hβ hEnergy f.1 hmass

/-- The same positive volume-independent Poincare constant holds after Gauss
compression. -/
theorem finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer_poincare
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (hmass : finiteFunctionMass f.1 = 0) :
    z2WilsonTemporalCrossingCoercivity
          β energyIdentity energyNontrivial * ‖f‖ ^ 2 ≤
      inner ℝ
        (f - finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer
          H β energyIdentity energyNontrivial hβ.le hEnergy.le f) f := by
  change
    z2WilsonTemporalCrossingCoercivity
          β energyIdentity energyNontrivial * ‖f.1‖ ^ 2 ≤
      inner ℝ
        (f.1 - finiteKernelNormalizedOperator
          (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
            H β energyIdentity energyNontrivial hβ.le hEnergy.le).kernel f.1) f.1
  exact finiteEvenFourTorusZ2TemporalGaugeCrossingNormalizedOperator_poincare
    H β energyIdentity energyNontrivial hβ hEnergy f.1 hmass

/-- Centered Gauss-invariant boundary sector for the temporal-crossing
transfer. -/
abbrev FiniteEvenFourTorusZ2GaussCenteredTemporalCrossingHilbert
    (H : ℕ) : Type :=
  finiteLinearFunctionalCenteredSubspace
    (finiteEvenFourTorusZ2GaugeInvariantMassLinearMap H)

/-- Gauss-compressed temporal-crossing transfer restricted to its centered
sector. -/
noncomputable def finiteEvenFourTorusZ2GaussCenteredTemporalCrossingTransfer
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    FiniteEvenFourTorusZ2GaussCenteredTemporalCrossingHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2GaussCenteredTemporalCrossingHilbert H :=
  finiteCenteredRestriction
    (finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer
      H β energyIdentity energyNontrivial hβ.le hEnergy.le)
    (finiteEvenFourTorusZ2GaugeInvariantMassLinearMap H)
    (finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer_mass
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- Every centered Gauss-invariant natural-time power decays with the same
strict local sign-mode rate, independently of the finite volume. -/
theorem finiteEvenFourTorusZ2GaussCenteredTemporalCrossingTransfer_pow_norm_apply_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (n : ℕ)
    (f : FiniteEvenFourTorusZ2GaussCenteredTemporalCrossingHilbert H) :
    ‖(finiteEvenFourTorusZ2GaussCenteredTemporalCrossingTransfer
        H β energyIdentity energyNontrivial hβ hEnergy) ^ n f‖ ≤
      z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial ^ n * ‖f‖ := by
  exact finiteCenteredRestriction_pow_norm_apply_le
    (finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer
      H β energyIdentity energyNontrivial hβ.le hEnergy.le)
    (finiteEvenFourTorusZ2GaugeInvariantMassLinearMap H)
    (finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer_mass
      H β energyIdentity energyNontrivial hβ hEnergy)
    (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
    (finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer_isSymmetric
      H β energyIdentity energyNontrivial hβ.le hEnergy.le)
    (fun x =>
      finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer_quadratic_nonneg
        H β energyIdentity energyNontrivial hβ.le hEnergy.le x.1)
    (fun x =>
      finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer_rayleigh_le
        H β energyIdentity energyNontrivial hβ hEnergy x.1 (by
          change finiteFunctionMass x.1.1 = 0
          exact x.2))
    n f

/-- The geometric natural-time factor is exactly the exponential generated by
the positive crossing gap. -/
theorem z2WilsonTemporalCrossingRate_pow_eq_exp_neg_gap_mul_nat
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (n : ℕ) :
    z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial ^ n =
      Real.exp (-(n : ℝ) *
        z2WilsonTemporalCrossingGap
          β energyIdentity energyNontrivial) := by
  calc
    z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial ^ n =
      (Real.exp (-z2WilsonTemporalCrossingGap
        β energyIdentity energyNontrivial)) ^ n := by
        rw [exp_neg_z2WilsonTemporalCrossingGap hβ hEnergy]
    _ = Real.exp ((n : ℝ) *
        (-z2WilsonTemporalCrossingGap
          β energyIdentity energyNontrivial)) := by
      exact (Real.exp_nat_mul
        (-z2WilsonTemporalCrossingGap
          β energyIdentity energyNontrivial) n).symm
    _ = Real.exp (-(n : ℝ) *
        z2WilsonTemporalCrossingGap
          β energyIdentity energyNontrivial) := by
      congr 1
      ring

/-- Exponential natural-time decay on the centered Gauss-invariant crossing
sector with a strictly positive volume-independent exponent. -/
theorem finiteEvenFourTorusZ2GaussCenteredTemporalCrossingTransfer_exp_decay
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (n : ℕ)
    (f : FiniteEvenFourTorusZ2GaussCenteredTemporalCrossingHilbert H) :
    ‖(finiteEvenFourTorusZ2GaussCenteredTemporalCrossingTransfer
        H β energyIdentity energyNontrivial hβ hEnergy) ^ n f‖ ≤
      Real.exp (-(n : ℝ) *
          z2WilsonTemporalCrossingGap
            β energyIdentity energyNontrivial) * ‖f‖ := by
  rw [← z2WilsonTemporalCrossingRate_pow_eq_exp_neg_gap_mul_nat
    β energyIdentity energyNontrivial hβ hEnergy n]
  exact finiteEvenFourTorusZ2GaussCenteredTemporalCrossingTransfer_pow_norm_apply_le
    H β energyIdentity energyNontrivial hβ hEnergy n f

/-- Complete all-volume Gauss-compressed uniform-gap package for the actual raw
temporal-crossing Wilson kernel. -/
structure Z2FiniteEvenFourTorusTemporalCrossingGaussUniformGapPackage
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  rate : ℝ
  coercivity : ℝ
  gap : ℝ
  rate_eq : rate = z2WilsonTemporalCrossingRate
    β energyIdentity energyNontrivial
  coercivity_eq : coercivity = z2WilsonTemporalCrossingCoercivity
    β energyIdentity energyNontrivial
  gap_eq : gap = z2WilsonTemporalCrossingGap
    β energyIdentity energyNontrivial
  rate_pos : 0 < rate
  rate_lt_one : rate < 1
  coercivity_pos : 0 < coercivity
  gap_pos : 0 < gap
  compressedPoincare :
    ∀ (H : ℕ)
      (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H),
      finiteFunctionMass f.1 = 0 →
        coercivity * ‖f‖ ^ 2 ≤
          inner ℝ
            (f - finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer
              H β energyIdentity energyNontrivial hβ.le hEnergy.le f) f
  centeredPowerDecay :
    ∀ (H n : ℕ)
      (f : FiniteEvenFourTorusZ2GaussCenteredTemporalCrossingHilbert H),
      ‖(finiteEvenFourTorusZ2GaussCenteredTemporalCrossingTransfer
          H β energyIdentity energyNontrivial hβ hEnergy) ^ n f‖ ≤
        rate ^ n * ‖f‖
  centeredExponentialDecay :
    ∀ (H n : ℕ)
      (f : FiniteEvenFourTorusZ2GaussCenteredTemporalCrossingHilbert H),
      ‖(finiteEvenFourTorusZ2GaussCenteredTemporalCrossingTransfer
          H β energyIdentity energyNontrivial hβ hEnergy) ^ n f‖ ≤
        Real.exp (-(n : ℝ) * gap) * ‖f‖

/-- Canonical complete Gauss-compressed temporal-crossing uniform-gap package. -/
noncomputable def finiteEvenFourTorusZ2TemporalCrossingGaussUniformGapPackage
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Z2FiniteEvenFourTorusTemporalCrossingGaussUniformGapPackage
      β energyIdentity energyNontrivial hβ hEnergy :=
  { rate := z2WilsonTemporalCrossingRate
      β energyIdentity energyNontrivial
    coercivity := z2WilsonTemporalCrossingCoercivity
      β energyIdentity energyNontrivial
    gap := z2WilsonTemporalCrossingGap
      β energyIdentity energyNontrivial
    rate_eq := rfl
    coercivity_eq := rfl
    gap_eq := rfl
    rate_pos := z2WilsonTemporalCrossingRate_pos hβ hEnergy
    rate_lt_one := z2WilsonTemporalCrossingRate_lt_one hβ hEnergy
    coercivity_pos := z2WilsonTemporalCrossingCoercivity_pos hβ hEnergy
    gap_pos := z2WilsonTemporalCrossingGap_pos hβ hEnergy
    compressedPoincare := fun H f hmass =>
      finiteEvenFourTorusZ2GaussProjectedTemporalCrossingTransfer_poincare
        H β energyIdentity energyNontrivial hβ hEnergy f hmass
    centeredPowerDecay := fun H n f =>
      finiteEvenFourTorusZ2GaussCenteredTemporalCrossingTransfer_pow_norm_apply_le
        H β energyIdentity energyNontrivial hβ hEnergy n f
    centeredExponentialDecay := fun H n f =>
      finiteEvenFourTorusZ2GaussCenteredTemporalCrossingTransfer_exp_decay
        H β energyIdentity energyNontrivial hβ hEnergy n f }

end

end MathlibAnalytic
end MGAP4D
