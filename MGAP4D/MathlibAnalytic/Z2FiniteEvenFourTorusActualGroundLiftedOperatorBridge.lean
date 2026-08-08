import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusActualGroundLiftedQuadraticObstruction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Finite-kernel operators commute with multiplication of every kernel entry
by a real scalar. -/
theorem finiteKernelOperator_const_mul_kernel
    {α : Type} [Fintype α]
    (c : ℝ)
    (K : α → α → ℝ) :
    finiteKernelOperator (fun x y => c * K x y) =
      c • finiteKernelOperator K := by
  apply ContinuousLinearMap.ext
  intro f
  ext y
  rw [finiteKernelOperator_apply]
  simp only [ContinuousLinearMap.smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [finiteKernelOperator_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  ring

/-- Finite-kernel operators commute with kernel subtraction. -/
theorem finiteKernelOperator_sub_kernel
    {α : Type} [Fintype α]
    (K L : α → α → ℝ) :
    finiteKernelOperator (fun x y => K x y - L x y) =
      finiteKernelOperator K - finiteKernelOperator L := by
  apply ContinuousLinearMap.ext
  intro f
  ext y
  rw [finiteKernelOperator_apply]
  change
    (∑ x : α, (K x y - L x y) * f x) =
      (finiteKernelOperator K f) y - (finiteKernelOperator L f) y
  rw [finiteKernelOperator_apply, finiteKernelOperator_apply,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  ring

/-- The scalar-normalized all-real coupling-family kernel represents exactly
its canonical operator-norm-normalized transfer. -/
theorem finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyKernel_operator_eq_normalizedOperator
    (H : ℕ)
    (energyIdentity energyNontrivial β : ℝ) :
    finiteKernelOperator
        (finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyKernel
          H energyIdentity energyNontrivial β) =
      finiteKernelNormalizedOperator
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
          H energyIdentity energyNontrivial β) := by
  unfold finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyKernel
    finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
    finiteKernelNormalizedOperator
  exact finiteKernelOperator_const_mul_kernel
    ‖finiteKernelOperator
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
        H energyIdentity energyNontrivial β)‖⁻¹
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
      H energyIdentity energyNontrivial β)

/-- On the physical nonnegative domain, the normalized coupling-family kernel
operator is exactly the actual finite-Z₂ unfixed-gauge one-slab transfer. -/
theorem finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyKernel_operator_eq_actual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteKernelOperator
        (finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyKernel
          H energyIdentity energyNontrivial β) =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy := by
  rw [finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyKernel_operator_eq_normalizedOperator]
  exact
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransferCouplingFamily_eq_actual
      H β energyIdentity energyNontrivial hβ hEnergy

/-- The finite kernel built from a nonzero vector's normalized rank-one formula
represents the corresponding continuous rank-one operator. -/
theorem finiteEvenFourTorusZ2CanonicalGroundRankOneProjectorKernelRightExtension_operator_eq_rankOne
    (H : ℕ)
    (energyIdentity energyNontrivial β : ℝ) :
    let p :=
      finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
        H energyIdentity energyNontrivial β
    finiteKernelOperator
        (finiteEvenFourTorusZ2CanonicalGroundRankOneProjectorKernelRightExtension
          H energyIdentity energyNontrivial β) =
      (inner ℝ p p)⁻¹ • InnerProductSpace.rankOne ℝ p p := by
  let p :=
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
      H energyIdentity energyNontrivial β
  change
    finiteKernelOperator
        (fun A B : FiniteEvenFourTorusZ2SliceConfiguration H =>
          (inner ℝ p p)⁻¹ * p A * p B) =
      (inner ℝ p p)⁻¹ • InnerProductSpace.rankOne ℝ p p
  apply ContinuousLinearMap.ext
  intro f
  ext y
  rw [finiteKernelOperator_apply, ContinuousLinearMap.smul_apply,
    InnerProductSpace.rankOne_apply]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [PiLp.inner_apply]
  change
    (∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
        ((inner ℝ p p)⁻¹ * p x * p y) * f x) =
      (inner ℝ p p)⁻¹ *
        (∑ x : FiniteEvenFourTorusZ2SliceConfiguration H, f x * p x) * p y
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _hx
  ring

/-- On the physical nonnegative domain, the canonical Perron rank-one kernel
operator is exactly the actual ambient ground spectral projector. -/
theorem finiteEvenFourTorusZ2CanonicalGroundRankOneProjectorKernelRightExtension_operator_eq_actualGroundProjector
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteKernelOperator
        (finiteEvenFourTorusZ2CanonicalGroundRankOneProjectorKernelRightExtension
          H energyIdentity energyNontrivial β) =
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData
        H β energyIdentity energyNontrivial hβ hEnergy).groundSpectralProjector := by
  have hk :=
    finiteEvenFourTorusZ2CanonicalGroundRankOneProjectorKernelRightExtension_operator_eq_rankOne
      H energyIdentity energyNontrivial β
  rw [finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_of_nonneg
    H energyIdentity energyNontrivial β hβ] at hk
  have hp :=
    finiteEvenFourTorusZ2UnfixedGaugeAmbientGroundSpectralProjector_eq_canonicalPerronRankOne
      H β energyIdentity energyNontrivial hβ hEnergy
  exact hk.trans (by simpa using hp.symm)

/-- The Package-Z ground-lifted kernel is not merely a scalar proxy: on every
physical nonnegative coupling it represents exactly the actual spectral defect
`P_ground - T` of the finite-Z₂ transfer. -/
theorem finiteEvenFourTorusZ2GroundLiftedKernelRightExtension_operator_eq_actualGroundSpectralDefect
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteKernelOperator
        (finiteEvenFourTorusZ2GroundLiftedKernelRightExtension
          H energyIdentity energyNontrivial β) =
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData
          H β energyIdentity energyNontrivial hβ hEnergy).groundSpectralProjector -
        (finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData
          H β energyIdentity energyNontrivial hβ hEnergy).operator := by
  unfold finiteEvenFourTorusZ2GroundLiftedKernelRightExtension
  rw [finiteKernelOperator_sub_kernel]
  rw [finiteEvenFourTorusZ2CanonicalGroundRankOneProjectorKernelRightExtension_operator_eq_actualGroundProjector
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyKernel_operator_eq_actual
      H β energyIdentity energyNontrivial hβ hEnergy]
  rfl

/-- Operator-level unconditional Package-Z obstruction, now stated directly
for the actual finite-Z₂ spectral data: on an entire sufficiently small
positive-coupling interval, the beta-zero uniform complement sees a nonzero
block of `P_ground - T`. -/
theorem finiteEvenFourTorusZ2ActualGroundSpectralDefect_exists_smallPositive_uniformComplementBlock_ne_zero_zero
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ β : ℝ, ∀ hβ : 0 < β, β < ε →
        finiteUniformAverageComplementLinearMap.comp
          ((((finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData
                0 β energyIdentity energyNontrivial hβ.le hEnergy.le).groundSpectralProjector -
              (finiteEvenFourTorusZ2UnfixedGaugeAmbientSpectralData
                0 β energyIdentity energyNontrivial hβ.le hEnergy.le).operator).toLinearMap).comp
            finiteUniformAverageComplementLinearMap) ≠ 0 := by
  rcases
      finiteEvenFourTorusZ2GroundLiftedKernelRightExtension_exists_smallPositive_uniformComplementBlock_ne_zero_zero
        energyIdentity energyNontrivial hEnergy with
    ⟨ε, hε, hBlock⟩
  refine ⟨ε, hε, ?_⟩
  intro β hβ hβε
  have h := hBlock β hβ hβε
  have hop :=
    finiteEvenFourTorusZ2GroundLiftedKernelRightExtension_operator_eq_actualGroundSpectralDefect
      0 β energyIdentity energyNontrivial hβ.le hEnergy.le
  rw [hop] at h
  exact h

end

end MathlibAnalytic
end MGAP4D
