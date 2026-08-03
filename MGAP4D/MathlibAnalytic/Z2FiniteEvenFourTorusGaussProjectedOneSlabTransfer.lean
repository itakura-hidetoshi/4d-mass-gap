import MGAP4D.MathlibAnalytic.FiniteGroupInvariantKernelCompressedTransfer
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusResidualGaugeOneSlabKernelInvariance
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusTemporalGaugeOneSlabNontriviality
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- Gauge-invariant Euclidean boundary Hilbert subspace after the finite Gauss
projection. -/
abbrev FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert (H : ℕ) : Type :=
  finiteGroupInvariantSubmodule
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)

/-- Orthogonal residual-gauge averaging projector on the ambient boundary
Hilbert space. -/
noncomputable def finiteEvenFourTorusZ2GaussProjector
    (H : ℕ) :
    FiniteEvenFourTorusZ2SliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2SliceHilbert H :=
  finiteGroupAveragingProjector
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)

/-- The Gauss projector is idempotent. -/
theorem finiteEvenFourTorusZ2GaussProjector_idempotent
    (H : ℕ) :
    (finiteEvenFourTorusZ2GaussProjector H).comp
        (finiteEvenFourTorusZ2GaussProjector H) =
      finiteEvenFourTorusZ2GaussProjector H :=
  finiteGroupAveragingProjector_idempotent
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)

/-- The gauge-averaging residual is orthogonal to every Gauss-invariant
boundary vector. -/
theorem finiteEvenFourTorusZ2GaussProjector_orthogonal
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2SliceHilbert H)
    (h : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    inner ℝ (f - finiteEvenFourTorusZ2GaussProjector H f) h.1 = 0 :=
  finiteGroupAveragingProjector_orthogonal
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H) f h

/-- The normalized actual one-slab transfer commutes with the Gauss
projector. -/
theorem finiteEvenFourTorusZ2OneSlabTransfer_commutes_GaussProjector
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy).comp
        (finiteEvenFourTorusZ2GaussProjector H) =
      (finiteEvenFourTorusZ2GaussProjector H).comp
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy) :=
  finiteKernelNormalizedOperator_commutes_groupAveraging
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The actual one-slab Wilson transfer compressed to the Gauss-invariant
boundary Hilbert subspace. -/
noncomputable def finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
  finiteGroupInvariantCompressedNormalizedTransfer
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The Gauss-projected one-slab transfer is symmetric. -/
theorem finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer_isSymmetric
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric :=
  finiteGroupInvariantCompressedNormalizedTransfer_isSymmetric
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The Gauss-projected one-slab transfer is positive. -/
theorem finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer_quadratic_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    0 ≤ inner ℝ
      (finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy f) f :=
  finiteGroupInvariantCompressedNormalizedTransfer_quadratic_nonneg
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul
      H β energyIdentity energyNontrivial hβ hEnergy) f

/-- The Gauss-projected one-slab transfer is contractive. -/
theorem finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer_norm_apply_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    ‖finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy f‖ ≤ ‖f‖ :=
  finiteGroupInvariantCompressedNormalizedTransfer_norm_apply_le
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_ne_zero
      H β energyIdentity energyNontrivial hβ hEnergy) f

/-- Natural geometric time after Gauss projection. -/
noncomputable def finiteEvenFourTorusZ2GaussProjectedTransferSemigroup
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (n : ℕ) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
  finiteGroupInvariantCompressedTransferSemigroup
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul
      H β energyIdentity energyNontrivial hβ hEnergy) n

/-- Additive natural time remains composition after Gauss projection. -/
theorem finiteEvenFourTorusZ2GaussProjectedTransferSemigroup_add
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (m n : ℕ) :
    finiteEvenFourTorusZ2GaussProjectedTransferSemigroup
        H β energyIdentity energyNontrivial hβ hEnergy (m + n) =
      (finiteEvenFourTorusZ2GaussProjectedTransferSemigroup
        H β energyIdentity energyNontrivial hβ hEnergy m).comp
      (finiteEvenFourTorusZ2GaussProjectedTransferSemigroup
        H β energyIdentity energyNontrivial hβ hEnergy n) :=
  finiteGroupInvariantCompressedTransferSemigroup_add
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul
      H β energyIdentity energyNontrivial hβ hEnergy) m n

/-- Every natural-time Gauss-projected transfer remains contractive. -/
theorem finiteEvenFourTorusZ2GaussProjectedTransferSemigroup_norm_apply_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (n : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    ‖finiteEvenFourTorusZ2GaussProjectedTransferSemigroup
      H β energyIdentity energyNontrivial hβ hEnergy n f‖ ≤ ‖f‖ :=
  finiteGroupInvariantCompressedTransferSemigroup_norm_apply_le
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_ne_zero
      H β energyIdentity energyNontrivial hβ hEnergy) n f

/-- Terminal package for the actual Gauss-projected one-slab transfer. -/
theorem finiteEvenFourTorusZ2GaussProjectedOneSlabTransferPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    ((finiteEvenFourTorusZ2GaussProjector H).comp
        (finiteEvenFourTorusZ2GaussProjector H) =
      finiteEvenFourTorusZ2GaussProjector H) ∧
    ((finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy).comp
        (finiteEvenFourTorusZ2GaussProjector H) =
      (finiteEvenFourTorusZ2GaussProjector H).comp
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy)) ∧
    ((finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric) ∧
    (∀ f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
      0 ≤ inner ℝ
        (finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy f) f) ∧
    (∀ f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
      ‖finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy f‖ ≤ ‖f‖) ∧
    (∀ m n : ℕ,
      finiteEvenFourTorusZ2GaussProjectedTransferSemigroup
          H β energyIdentity energyNontrivial hβ hEnergy (m + n) =
        (finiteEvenFourTorusZ2GaussProjectedTransferSemigroup
          H β energyIdentity energyNontrivial hβ hEnergy m).comp
        (finiteEvenFourTorusZ2GaussProjectedTransferSemigroup
          H β energyIdentity energyNontrivial hβ hEnergy n)) := by
  exact ⟨
    finiteEvenFourTorusZ2GaussProjector_idempotent H,
    finiteEvenFourTorusZ2OneSlabTransfer_commutes_GaussProjector
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer_isSymmetric
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer_quadratic_nonneg
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer_norm_apply_le
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2GaussProjectedTransferSemigroup_add
      H β energyIdentity energyNontrivial hβ hEnergy⟩

end

end MathlibAnalytic
end MGAP4D
