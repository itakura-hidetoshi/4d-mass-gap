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

/-- A concrete spatial link on the one-site slice. -/
def finiteEvenFourTorusZ2ZeroSliceDistinguishedLink :
    FiniteEvenFourTorusSpatialLink 0 :=
  (⟨fun _ => 0, rfl⟩, ⟨1, by decide⟩)

/-- The identity and one-link-excited one-site boundary configurations are
distinct. -/
theorem finiteEvenFourTorusZ2ZeroSlice_identity_ne_excitation :
    finiteEvenFourTorusZ2IdentitySlice 0 ≠
      finiteEvenFourTorusZ2SingleLinkExcitation 0
        finiteEvenFourTorusZ2ZeroSliceDistinguishedLink := by
  intro h
  have hlink := congrFun h finiteEvenFourTorusZ2ZeroSliceDistinguishedLink
  simp [finiteEvenFourTorusZ2IdentitySlice,
    finiteEvenFourTorusZ2SingleLinkExcitation] at hlink

/-- Every ambient point vector on the one-site slice is already Gauss
invariant because the residual gauge action is trivial there. -/
noncomputable def finiteEvenFourTorusZ2ZeroSliceInvariantPointVector
    (A : FiniteEvenFourTorusZ2SliceConfiguration 0) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0 :=
  ⟨finiteBoundaryPointVector A, by
    intro g X
    rw [finiteEvenFourTorusZ2ResidualSlice_smul_zero]
  ⟩

/-- Explicit nonidentity witness in a genuine gauge-invariant sector.  On the
one-site spatial torus the Gauss-invariant subspace is the full boundary
Hilbert space, and the strictly positive off-diagonal slab kernel rules out the
identity operator. -/
theorem finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer_ne_identity_zeroSlice
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer
        0 β energyIdentity energyNontrivial hβ hEnergy ≠ 1 := by
  let A := finiteEvenFourTorusZ2IdentitySlice 0
  let B := finiteEvenFourTorusZ2SingleLinkExcitation 0
    finiteEvenFourTorusZ2ZeroSliceDistinguishedLink
  let f := finiteEvenFourTorusZ2ZeroSliceInvariantPointVector A
  let h := finiteEvenFourTorusZ2ZeroSliceInvariantPointVector B
  have hAB : A ≠ B := by
    exact finiteEvenFourTorusZ2ZeroSlice_identity_ne_excitation
  have horth : inner ℝ f h = 0 := by
    exact finiteEvenFourTorusZ2BoundaryPointVector_inner_eq_zero_of_ne
      0 A B hAB
  have hoff :
      0 < inner ℝ
        (finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer
          0 β energyIdentity energyNontrivial hβ hEnergy f) h := by
    change
      0 < inner ℝ
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
          0 β energyIdentity energyNontrivial hβ hEnergy
          (finiteBoundaryPointVector A))
        (finiteBoundaryPointVector B)
    unfold finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
      finiteKernelNormalizedOperator
    rw [ContinuousLinearMap.smul_apply, real_inner_smul_left]
    apply mul_pos
    · exact inv_pos.mpr
        (norm_pos_iff.mpr
          (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_ne_zero
            0 β energyIdentity energyNontrivial hβ hEnergy))
    · rw [finiteKernelOperator_point_matrixElement,
        finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_eq_boltzmann]
      exact Real.exp_pos _
  intro hId
  have hmatrix := congrArg
    (fun T : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0 →L[ℝ]
        FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert 0 =>
      inner ℝ (T f) h) hId
  change inner ℝ
      (finiteEvenFourTorusZ2GaussProjectedOneSlabTransfer
        0 β energyIdentity energyNontrivial hβ hEnergy f) h =
    inner ℝ f h at hmatrix
  rw [horth] at hmatrix
  rw [hmatrix] at hoff
  exact (lt_irrefl 0) hoff

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
