import MGAP4D.MathlibAnalytic.FiniteOSGramKernelEuclideanTransfer
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusTemporalGaugeOneSlabKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- Boundary Hilbert space of one actual even-torus spatial time slice. -/
abbrev FiniteEvenFourTorusZ2SliceHilbert (H : ℕ) : Type :=
  FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H)

/-- Raw temporal-gauge one-slab Wilson transfer operator. -/
noncomputable def finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2SliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2SliceHilbert H :=
  finiteKernelOperator
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel

/-- Canonically normalized actual one-slab Wilson transfer. -/
noncomputable def finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2SliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2SliceHilbert H :=
  finiteKernelNormalizedOperator
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel

/-- The raw one-slab transfer is nonzero because every diagonal Boltzmann
weight is strictly positive. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_ne_zero
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
      H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  let A : FiniteEvenFourTorusZ2SliceConfiguration H := fun _ => 1
  apply finiteKernelOperator_ne_zero_of_diagonal_ne_zero
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel A
  exact ne_of_gt
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_pos
      H β energyIdentity energyNontrivial hβ hEnergy A A)

/-- Exact one-slab transfer matrix element on point boundary states. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_point_matrixElement
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    inner ℝ
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteBoundaryPointVector A))
        (finiteBoundaryPointVector B) =
      Real.exp (-β *
        finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
          H β energyIdentity energyNontrivial A B) := by
  rw [finiteKernelOperator_point_matrixElement]
  exact
    finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_eq_boltzmann
      H β energyIdentity energyNontrivial hβ hEnergy A B

/-- The normalized one-slab transfer is symmetric. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer_isSymmetric
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric :=
  finiteGramKernelNormalizedOperator_isSymmetric
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The normalized one-slab transfer is positive. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer_quadratic_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H) :
    0 ≤ inner ℝ
      (finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy f) f :=
  finiteGramKernelNormalizedOperator_quadratic_nonneg
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy) f

/-- The normalized one-slab transfer has operator norm exactly one. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer_norm_eq_one
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    ‖finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy‖ = 1 :=
  finiteKernelNormalizedOperator_norm_eq_one _
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_ne_zero
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The normalized one-slab transfer is contractive. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer_norm_apply_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H) :
    ‖finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy f‖ ≤ ‖f‖ :=
  finiteKernelNormalizedOperator_norm_apply_le _
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_ne_zero
      H β energyIdentity energyNontrivial hβ hEnergy) f

/-- Natural-time powers of the actual one-slab transfer. -/
noncomputable def finiteEvenFourTorusZ2TemporalGaugeTransferSemigroup
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (n : ℕ) :
    FiniteEvenFourTorusZ2SliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2SliceHilbert H :=
  finiteKernelNormalizedSemigroup
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel n

/-- Additive geometric lattice time is composition of slab transfers. -/
theorem finiteEvenFourTorusZ2TemporalGaugeTransferSemigroup_add
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (m n : ℕ) :
    finiteEvenFourTorusZ2TemporalGaugeTransferSemigroup
        H β energyIdentity energyNontrivial hβ hEnergy (m + n) =
      (finiteEvenFourTorusZ2TemporalGaugeTransferSemigroup
        H β energyIdentity energyNontrivial hβ hEnergy m).comp
      (finiteEvenFourTorusZ2TemporalGaugeTransferSemigroup
        H β energyIdentity energyNontrivial hβ hEnergy n) :=
  finiteKernelNormalizedSemigroup_add _ m n

/-- Every natural geometric time is contractive. -/
theorem finiteEvenFourTorusZ2TemporalGaugeTransferSemigroup_norm_apply_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (n : ℕ)
    (f : FiniteEvenFourTorusZ2SliceHilbert H) :
    ‖finiteEvenFourTorusZ2TemporalGaugeTransferSemigroup
      H β energyIdentity energyNontrivial hβ hEnergy n f‖ ≤ ‖f‖ :=
  finiteKernelNormalizedSemigroup_norm_apply_le _
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_ne_zero
      H β energyIdentity energyNontrivial hβ hEnergy) n f

/-- Terminal receipt for the actual temporal-gauge even-torus Wilson transfer. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabTransferPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
      H β energyIdentity energyNontrivial hβ hEnergy ≠ 0) ∧
    ((finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric) ∧
    (∀ f : FiniteEvenFourTorusZ2SliceHilbert H,
      0 ≤ inner ℝ
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy f) f) ∧
    (∀ f : FiniteEvenFourTorusZ2SliceHilbert H,
      ‖finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy f‖ ≤ ‖f‖) ∧
    (∀ m n : ℕ,
      finiteEvenFourTorusZ2TemporalGaugeTransferSemigroup
          H β energyIdentity energyNontrivial hβ hEnergy (m + n) =
        (finiteEvenFourTorusZ2TemporalGaugeTransferSemigroup
          H β energyIdentity energyNontrivial hβ hEnergy m).comp
        (finiteEvenFourTorusZ2TemporalGaugeTransferSemigroup
          H β energyIdentity energyNontrivial hβ hEnergy n)) := by
  exact ⟨
    finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_ne_zero
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer_isSymmetric
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer_quadratic_nonneg
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer_norm_apply_le
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2TemporalGaugeTransferSemigroup_add
      H β energyIdentity energyNontrivial hβ hEnergy⟩

end

end MathlibAnalytic
end MGAP4D
