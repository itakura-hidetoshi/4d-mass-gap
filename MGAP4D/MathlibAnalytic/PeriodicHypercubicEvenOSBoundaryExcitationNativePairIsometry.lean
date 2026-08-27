import MGAP4D.MathlibAnalytic.HilbertTensorLinearIsometry
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationNativeHilbertTensorTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped TensorProduct InnerProductSpace

noncomputable section

local instance osBoundaryExcitationNativePairIsometrySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationNativePairIsometrySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationNativePairIsometrySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationNativePairIsometrySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationNativePairIsometrySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationNativePairIsometrySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationNativePairIsometrySpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Keep Mathlib's native Hilbert tensor norm explicit on the physical
excitation algebraic tensor carrier. -/
@[reducible] local instance osBoundaryExcitationNativePairIsometryNormedAddCommGroup
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

/-- The matching native tensor inner product on the physical excitation core. -/
@[reducible] local instance osBoundaryExcitationNativePairIsometryInnerProductSpace
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

/-- Keep the native Hilbert tensor norm explicit on the ambient one-slice
`L²` tensor square used as the intermediate realization. -/
@[reducible] local instance osBoundaryExcitationNativePairIsometryL2TensorNormedAddCommGroup
    (H N : ℕ) :
    NormedAddCommGroup
      (Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) ⊗[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
  TensorProduct.instNormedAddCommGroup
    (𝕜 := ℝ)
    (E := Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (F := Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- The matching native inner product on the ambient one-slice `L²` tensor square. -/
@[reducible] local instance osBoundaryExcitationNativePairIsometryL2TensorInnerProductSpace
    (H N : ℕ) :
    InnerProductSpace ℝ
      (Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) ⊗[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
  TensorProduct.instInnerProductSpace
    (𝕜 := ℝ)
    (E := Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (F := Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- Tensor the one-slice physical excitation inclusion with itself as an exact
linear isometry for Mathlib's native Hilbert tensor norm. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorFactorLinearIsometry
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta →ₗᵢ[ℝ]
      (Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) ⊗[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :=
  hilbertTensorLinearIsometry
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
      H N hN beta hbeta)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorFactorLinearIsometry_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorFactorLinearIsometry
        H N hN beta hbeta x =
      TensorProduct.map
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
          H N hN beta hbeta) x :=
  rfl

/-- The canonical algebraic excitation embedding into concrete endpoint-pair
`L²` is an exact linear isometry on the whole algebraic Hilbert tensor core,
not only on decomposable tensors. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingNativeLinearIsometry
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  (realL2ExternalTensorLiftLinearIsometry
      (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)).comp
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorFactorLinearIsometry
      H N hN beta hbeta)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingNativeLinearIsometry_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingNativeLinearIsometry
        H N hN beta hbeta x =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta x :=
  rfl

/-- Full-core norm identification between the native Hilbert tensor norm and
the concrete endpoint-pair `L²` norm. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta x‖ = ‖x‖ := by
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingNativeLinearIsometry_apply]
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingNativeLinearIsometry
      H N hN beta hbeta).norm_map x

/-- The canonical algebraic map with codomain restricted to the concrete
closed pair-`L²` excitation sector is still an exact linear isometry. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta →ₗᵢ[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta where
  toLinearMap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSector
      H N hN beta hbeta
  norm_map' := fun x => by
    change
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta x‖ = ‖x‖
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_norm
        H N hN beta hbeta x

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry_coe
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
        H N hN beta hbeta x :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) =
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
      H N hN beta hbeta x :=
  rfl

/-- The native continuous tensor transfer has exactly the pre-existing
algebraic tensor transfer as its underlying linear map. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_toLinearMap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
      H N hN beta hbeta n).toLinearMap =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
        H N hN beta hbeta n := by
  apply TensorProduct.ext'
  intro f g
  rfl

/-- The new native Hilbert-tensor transfer and the old concrete pair-`L²`
realization form an exact intertwining square on the whole algebraic core. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativePairIsometry_intertwines
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingNativeLinearIsometry
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
          H N hN beta hbeta n x) =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta n x := by
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
          H N hN beta hbeta n x) =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
          H N hN beta hbeta n x)
  congr 1
  have hmap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_toLinearMap
      H N hN beta hbeta n
  exact LinearMap.congr_fun hmap x

/-- Hence the concrete pair-`L²` evolved realization has exactly the norm of
the native Hilbert-tensor transfer on every algebraic tensor. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding_norm_eq_native
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta n x‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n x‖ := by
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativePairIsometry_intertwines]
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingNativeLinearIsometry
      H N hN beta hbeta).norm_map _

/-- The doubled finite-volume exponential estimate therefore holds for every
algebraic excitation tensor in the concrete pair-`L²` realization, not merely
for decomposable tensors. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding_norm_le_exp_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta n x‖ ≤
      Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta x‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding_norm_eq_native]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_norm]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_apply_norm_le_exp_of_pos
      H N hN beta hbeta n hn x

/-- The actual shared Wilson-boundary realization inherits the same full-core
doubled exponential estimate by its exact pair/boundary `L²` isometry. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding_norm_le_exp_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta n x‖ ≤
      Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta x‖ := by
  change
    ‖periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding
          H N hN beta hbeta n x)‖ ≤
      Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta x‖
  rw [(periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N).norm_map]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding_norm_le_exp_of_pos
      H N hN beta hbeta n hn x

/-- Audit-visible receipt for the exact native-Hilbert/concrete-pair norm
identification and transfer intertwining on the full algebraic excitation core. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationNativePairIsometryPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  canonicalNorm :
    ∀ x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta x‖ = ‖x‖
  transferLinearization :
    ∀ n : ℕ,
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n).toLinearMap =
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
          H N hN beta hbeta n
  pairIntertwining :
    ∀ (n : ℕ)
      (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta),
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingNativeLinearIsometry
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
            H N hN beta hbeta n x) =
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding
          H N hN beta hbeta n x

/-- Construct the exact native/concrete pair-isometry package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationNativePairIsometryPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationNativePairIsometryPackage
      H N hN beta hbeta :=
  { canonicalNorm :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_norm
        H N hN beta hbeta
    transferLinearization :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_toLinearMap
        H N hN beta hbeta
    pairIntertwining :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativePairIsometry_intertwines
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
