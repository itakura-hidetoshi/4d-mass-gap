import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedGeneratorAffineRealSpectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped TensorProduct InnerProductSpace InnerProduct BigOperators

noncomputable section

/-- Natural powers of a symmetric bounded real-Hilbert endomorphism with
nonnegative quadratic form have nonnegative quadratic forms.  This is the
positivity statement needed below, expressed without asking typeclass
inference to reconstruct `LinearMap.IsPositive` on a dependent carrier. -/
theorem realContinuousLinearMap_pow_inner_nonneg_of_inner_symm_of_inner_nonneg
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (hSymm : ∀ x y : E, inner ℝ (A x) y = inner ℝ x (A y))
    (hpos : ∀ x : E, 0 ≤ inner ℝ (A x) x)
    (n : ℕ)
    (u : E) :
    0 ≤ inner ℝ ((A ^ n) u) u := by
  induction n using Nat.strong_induction_on generalizing u with
  | h n ih =>
      rcases n with _ | n
      · simpa [real_inner_self_eq_norm_sq] using sq_nonneg ‖u‖
      · rcases n with _ | k
        · simpa using hpos u
        · have hpow : A ^ (k + 2) = A * (A ^ k) * A := by
            calc
              A ^ (k + 2) = A ^ (k + 1) * A := by
                simpa [Nat.add_assoc] using pow_succ A (k + 1)
              _ = (A * A ^ k) * A := by
                rw [show k + 1 = 1 + k by omega, pow_add, pow_one]
          rw [hpow]
          change 0 ≤ inner ℝ (A ((A ^ k) (A u))) u
          have hs :
              inner ℝ (A ((A ^ k) (A u))) u =
                inner ℝ ((A ^ k) (A u)) (A u) :=
            hSymm ((A ^ k) (A u)) u
          rw [hs]
          exact ih k (by omega) (A u)

/-- The matrix of symmetric positive-operator coefficients on any finite
family is positive semidefinite.  This is the Gram-type input for the Schur
product argument on tensor squares. -/
theorem realContinuousLinearMap_positiveCoefficientMatrix_posSemidef_of_inner_symm_of_inner_nonneg
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {ι : Type*}
    [Fintype ι]
    (A : E →L[ℝ] E)
    (hSymm : ∀ x y : E, inner ℝ (A x) y = inner ℝ x (A y))
    (hpos : ∀ x : E, 0 ≤ inner ℝ (A x) x)
    (v : ι → E) :
    Matrix.PosSemidef (fun i j : ι => inner ℝ (A (v i)) (v j)) := by
  have hcoeff (i j : ι) :
      inner ℝ (A (v i)) (v j) = inner ℝ (A (v j)) (v i) := by
    calc
      inner ℝ (A (v i)) (v j) = inner ℝ (v i) (A (v j)) :=
        hSymm (v i) (v j)
      _ = inner ℝ (A (v j)) (v i) := real_inner_comm _ _
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa only [star_trivial] using hcoeff j i
  · intro c
    have hquad := hpos (∑ i, c i • v i)
    simpa [dotProduct, Matrix.mulVec, map_sum, inner_sum, sum_inner,
      inner_smul_left, inner_smul_right, Finset.mul_sum, hcoeff,
      mul_comm, mul_left_comm, mul_assoc] using hquad

/-- The tensor square of a symmetric positive bounded real-Hilbert
endomorphism has a nonnegative quadratic form on the whole algebraic Hilbert
tensor product.  For a finite presentation `z = Σᵢ xᵢ ⊗ yᵢ`, the quadratic
form is the sum of all entries of the Hadamard product of the two positive
coefficient matrices; Mathlib's Schur product theorem makes this nonnegative. -/
theorem hilbertTensorMap_self_inner_nonneg_of_inner_symm_of_inner_nonneg
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (hSymm : ∀ x y : E, inner ℝ (A x) y = inner ℝ x (A y))
    (hpos : ∀ x : E, 0 ≤ inner ℝ (A x) x)
    (z : E ⊗[ℝ] E) :
    0 ≤ inner ℝ (hilbertTensorMap A A z) z := by
  obtain ⟨k, x, y, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
  let M : Matrix (Fin k) (Fin k) ℝ :=
    fun i j => inner ℝ (A (x i)) (x j)
  let N : Matrix (Fin k) (Fin k) ℝ :=
    fun i j => inner ℝ (A (y i)) (y j)
  have hM : M.PosSemidef := by
    simpa [M] using
      realContinuousLinearMap_positiveCoefficientMatrix_posSemidef_of_inner_symm_of_inner_nonneg
        A hSymm hpos x
  have hN : N.PosSemidef := by
    simpa [N] using
      realContinuousLinearMap_positiveCoefficientMatrix_posSemidef_of_inner_symm_of_inner_nonneg
        A hSymm hpos y
  have hMN : (Matrix.hadamard M N).PosSemidef :=
    Matrix.PosSemidef.hadamard hM hN
  have hones :=
    hMN.dotProduct_mulVec_nonneg (fun _ : Fin k => (1 : ℝ))
  have hsum : 0 ≤ ∑ i : Fin k, ∑ j : Fin k, M i j * N i j := by
    simpa [dotProduct, Matrix.mulVec, Matrix.hadamard,
      Finset.mul_sum] using hones
  rw [Finset.sum_comm] at hsum
  simp only [map_sum, inner_sum, sum_inner, hilbertTensorMap_tmul,
    TensorProduct.inner_tmul]
  simpa [M, N] using hsum

/-- Quadratic nonnegativity transports from a dense Hilbert source along a
linear isometry intertwining the source and target bounded endomorphisms. -/
theorem continuousLinearMap_inner_nonneg_of_dense_linearIsometry_intertwining
    {E F : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    (J : E →ₗᵢ[ℝ] F)
    (hDense : DenseRange J)
    (S : E →L[ℝ] E)
    (T : F →L[ℝ] F)
    (hS : ∀ x, 0 ≤ inner ℝ (S x) x)
    (hIntertwine : ∀ x, T (J x) = J (S x)) :
    ∀ u : F, 0 ≤ inner ℝ (T u) u := by
  intro u
  have hcontinuous : Continuous (fun y : F => inner ℝ (T y) y) := by
    fun_prop
  refine hDense.induction_on u (isClosed_le continuous_const hcontinuous) ?_
  intro x
  change 0 ≤ inner ℝ (T (J x)) (J x)
  rw [hIntertwine x]
  simpa using hS x

local instance osBoundaryExcitationCompletedTransferPositivitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedTransferPositivitySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedTransferPositivitySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedTransferPositivitySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedTransferPositivitySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedTransferPositivitySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedTransferPositivitySpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

@[reducible] local instance osBoundaryExcitationCompletedTransferPositivityNormedAddCommGroup
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    NormedAddCommGroup
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta) :=
  TensorProduct.instNormedAddCommGroup
    (𝕜 := ℝ)
    (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)

@[reducible] local instance osBoundaryExcitationCompletedTransferPositivityAddCommGroup
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    AddCommGroup
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta) :=
  (osBoundaryExcitationCompletedTransferPositivityNormedAddCommGroup
    H N hN beta hbeta).toAddCommGroup

@[reducible] local instance osBoundaryExcitationCompletedTransferPositivityInnerProductSpace
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    InnerProductSpace ℝ
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta) :=
  TensorProduct.instInnerProductSpace
    (𝕜 := ℝ)
    (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)

local instance osBoundaryExcitationCompletedTransferPositivityPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- The one-slice top-eigenspace-orthogonal transfer has nonnegative quadratic
form, directly inherited from positivity of the ambient normalized physical
transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_inner_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    0 ≤ inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta u) u := by
  change 0 ≤ inner ℝ
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
      (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
    (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
  exact
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isPositive
      H N hN beta hbeta).inner_nonneg_left
        (u : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)

/-- Every natural power of the one-slice top-eigenspace-orthogonal transfer
has nonnegative quadratic form. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_inner_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    0 ≤ inner ℝ
      (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta) ^ n) u) u := by
  exact
    realContinuousLinearMap_pow_inner_nonneg_of_inner_symm_of_inner_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_inner_symm
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_inner_nonneg
        H N hN beta hbeta)
      n u

/-- The native algebraic two-endpoint transfer has nonnegative quadratic form
at every Euclidean time. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_inner_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    0 ≤ inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n z) z := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_eq_hilbertTensorMap]
  let A :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta →L[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n
  have hSymm : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y) := by
    intro x y
    simpa [A] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_inner_symm
        H N hN beta hbeta n x y
  have hpos : ∀ x, 0 ≤ inner ℝ (A x) x := by
    intro x
    simpa [A] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_inner_nonneg
        H N hN beta hbeta n x
  change 0 ≤ inner ℝ (hilbertTensorMap A A z) z
  exact
    hilbertTensorMap_self_inner_nonneg_of_inner_symm_of_inner_nonneg
      A hSymm hpos z

/-- Completed pair-Hilbert transfer quadratic forms are nonnegative, by dense
transport of the algebraic Schur-product positivity theorem. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_inner_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    0 ≤ inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n u) u := by
  exact
    continuousLinearMap_inner_nonneg_of_dense_linearIsometry_intertwining
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry_denseRange
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_inner_nonneg
        H N hN beta hbeta n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_apply_algebraic
        H N hN beta hbeta n)
      u

/-- The completed pair-Hilbert transfer is a positive bounded operator at
every Euclidean time. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta n).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff'
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta n)).2
  exact ⟨
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isSelfAdjoint
      H N hN beta hbeta n,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_inner_nonneg
      H N hN beta hbeta n⟩

/-- Positivity forces the whole real spectrum of every completed pair transfer
to be nonnegative. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_spectrum_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    ∀ lambda ∈ spectrum ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n),
      0 ≤ lambda := by
  have hrestrict :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta n).spectrumRestricts
  rw [SpectrumRestricts.nnreal_iff] at hrestrict
  exact hrestrict

/-- At positive Euclidean time the completed pair-transfer spectrum lies in
`[0, rho_n]`: positivity supplies the lower endpoint and the existing operator
norm/decay argument supplies the upper endpoint. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_spectrum_subset_nonneg_decayInterval_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n) :
    spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n) ⊆
      Icc 0
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
          H N hN beta hbeta n) := by
  intro lambda hlambda
  have hnonneg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_spectrum_nonneg
      H N hN beta hbeta n lambda hlambda
  have hdecay :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_spectrum_subset_decayInterval_of_pos
      H N hN beta hbeta n hn hlambda
  exact ⟨hnonneg, hdecay.2⟩

/-- In particular, the one-step completed transfer has real spectrum contained
in `[0, rho₁]`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_spectrum_subset_nonneg_decayInterval
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1) ⊆
      Icc 0
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
          H N hN beta hbeta 1) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_spectrum_subset_nonneg_decayInterval_of_pos
      H N hN beta hbeta 1 (by norm_num)

/-- Combining transfer positivity with the exact affine spectrum relation
narrows the completed one-step generator spectrum from `[gap,1+rho₁]` to the
sharp one-sided interval `[gap,1]`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_spectrum_subset_gap_to_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta) ⊆
      Icc
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta)
        1 := by
  intro lambda hlambda
  have htransfer :
      1 - lambda ∈ spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_spectrum_mem_iff_transfer
      H N hN beta hbeta lambda).1 hlambda
  have hbounds :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_spectrum_subset_nonneg_decayInterval
      H N hN beta hbeta htransfer
  constructor
  · rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap_eq_one_sub_decayRadius]
    linarith [hbounds.2]
  · linarith [hbounds.1]

/-- Audit-visible package for completed transfer positivity and the resulting
nonnegative transfer / `[gap,1]` generator real-spectrum geometry. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedTransferPositivityPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  transferPositive :
    ∀ n : ℕ,
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n).IsPositive
  transferSpectrumNonnegative :
    ∀ n : ℕ,
      ∀ lambda ∈ spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n),
        0 ≤ lambda
  positiveTimeSpectrumEnclosure :
    ∀ n : ℕ, 0 < n →
      spectrum ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta n) ⊆
        Icc 0
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
            H N hN beta hbeta n)
  oneStepGeneratorSpectrumEnclosure :
    spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta) ⊆
      Icc
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta)
        1

/-- Construct the completed positivity package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedTransferPositivityPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedTransferPositivityPackage
      H N hN beta hbeta :=
  { transferPositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
        H N hN beta hbeta
    transferSpectrumNonnegative :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_spectrum_nonneg
        H N hN beta hbeta
    positiveTimeSpectrumEnclosure :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_spectrum_subset_nonneg_decayInterval_of_pos
        H N hN beta hbeta
    oneStepGeneratorSpectrumEnclosure :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_spectrum_subset_gap_to_one
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D