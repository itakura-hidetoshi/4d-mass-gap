import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryExcitationObservableImage
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorIsometry
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedPairSemigroup
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceExponentialDecay
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance osBoundaryOneSidedExcitationTransferTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryOneSidedExcitationTransferCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryOneSidedExcitationTransferSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryOneSidedExcitationTransferMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryOneSidedExcitationTransferBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryOneSidedExcitationTransferSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryOneSidedExcitationTransferSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Expose the restricted real normed-space structure on the named physical
orthogonal submodule. Generic continuous conjugation is given this instance
explicitly at the few sites where Lean would otherwise have to unfold the
dependent named submodule during typeclass search. -/
@[reducible] local instance osBoundaryOneSidedExcitationTransferPhysicalOrthogonalNormedSpace
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
  Submodule.normedSpace
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)

/-- The normalized physical top mode, viewed in the ambient spatial-slice Haar
`L²` carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
    H N hN beta hbeta

/-- The ambient `L²` top mode remains normalized. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
      H N hN beta hbeta‖ = 1 := by
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
    H N hN beta hbeta

/-- Embed one physical excitation into the ordered endpoint-pair Haar `L²`
carrier by tensoring it with the normalized physical top mode on the companion
endpoint. This is the one-particle, rather than excitation-tensor-square,
realization. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearMap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta →ₗ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N where
  toFun f :=
    realL2ExternalTensor
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
        H N hN beta hbeta f)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
        H N hN beta hbeta)
  map_add' f g := by
    rw [map_add, realL2ExternalTensor_add_left]
    rfl
  map_smul' c f := by
    rw [map_smul, realL2ExternalTensor_smul_left]
    rfl

/-- Fixing a unit top mode makes the one-sided pair embedding an exact linear
isometry. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N where
  toLinearMap :=
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearMap
      H N hN beta hbeta
  norm_map' f := by
    change
      ‖realL2ExternalTensor
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
          H N hN beta hbeta f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          H N hN beta hbeta)‖ = ‖f‖
    rw [realL2ExternalTensor_norm]
    rw [(periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
      H N hN beta hbeta).norm_map]
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2_norm]
    simp

/-- The concrete one-particle endpoint-pair Hilbert sector is the exact range of
the one-sided excitation isometry. -/
abbrev periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairSector
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :=
  LinearMap.range
    (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearMap
      H N hN beta hbeta)

/-- The physical excitation Hilbert space is isometrically equivalent to its
concrete one-sided pair-`L²` range. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairEquiv
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta ≃ₗᵢ[ℝ]
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairSector
        H N hN beta hbeta where
  toLinearEquiv :=
    LinearEquiv.ofInjective
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearMap
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
        H N hN beta hbeta).injective
  norm_map' f := by
    exact
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
        H N hN beta hbeta).norm_map f

/-- Transport the one-sided pair isometry through the exact pair/shared-boundary
coordinate equivalence. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N where
  toLinearMap :=
    (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N).toLinearMap.comp
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearMap
        H N hN beta hbeta)
  norm_map' f := by
    change
      ‖periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearMap
          H N hN beta hbeta f)‖ = ‖f‖
    rw [(periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N).norm_map]
    exact
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
        H N hN beta hbeta).norm_map f

/-- The concrete one-particle shared-boundary Hilbert sector is the exact range
of the one-sided physical excitation boundary isometry. -/
abbrev periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySector
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :=
  LinearMap.range
    (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
      H N hN beta hbeta).toLinearMap

/-- The physical excitation Hilbert space is isometrically equivalent to its
actual shared-boundary one-particle range. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryEquiv
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta ≃ₗᵢ[ℝ]
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySector
        H N hN beta hbeta where
  toLinearEquiv :=
    LinearEquiv.ofInjective
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
        H N hN beta hbeta).toLinearMap
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
        H N hN beta hbeta).injective
  norm_map' f := by
    exact
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
        H N hN beta hbeta).norm_map f

/-- On the ambient shared boundary, the one-sided excitation isometry is exactly
the previously canonical `f ⊗ Ω_top` boundary vector. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
        H N hN beta hbeta f =
      periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2 H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry
          H N hN beta hbeta f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          H N hN beta hbeta) := by
  rfl

/-- Concrete finite-volume physical transfer on the one-particle pair-`L²`
sector. It is exactly the normalized physical excitation transfer power,
conjugated through the one-sided endpoint-pair isometry. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairSectorTransfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairSector
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairSector
        H N hN beta hbeta := by
  letI : NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
    osBoundaryOneSidedExcitationTransferPhysicalOrthogonalNormedSpace
      H N hN beta hbeta
  exact
    continuousLinearMapConjugateLinearIsometryEquiv
      (𝕜 := ℝ)
      (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta)
      (F := periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairSector
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairEquiv
        H N hN beta hbeta)
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta) ^ n)

/-- The concrete one-sided pair transfer acts exactly by physical excitation
transfer on every represented one-particle vector. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairSectorTransfer_apply_image
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairSectorTransfer
        H N hN beta hbeta n
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairEquiv
          H N hN beta hbeta f) =
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairEquiv
        H N hN beta hbeta
        (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) f) := by
  letI : NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
    osBoundaryOneSidedExcitationTransferPhysicalOrthogonalNormedSpace
      H N hN beta hbeta
  exact
    continuousLinearMapConjugateLinearIsometryEquiv_apply_image
      (𝕜 := ℝ)
      (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta)
      (F := periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairSector
        H N hN beta hbeta)
      _ _ _

/-- Concrete finite-volume physical transfer on the actual shared-boundary
one-particle sector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySector
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySector
        H N hN beta hbeta := by
  letI : NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
    osBoundaryOneSidedExcitationTransferPhysicalOrthogonalNormedSpace
      H N hN beta hbeta
  exact
    continuousLinearMapConjugateLinearIsometryEquiv
      (𝕜 := ℝ)
      (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta)
      (F := periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySector
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryEquiv
        H N hN beta hbeta)
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta) ^ n)

/-- Exact physical-transfer/shared-boundary intertwining on the complete
one-particle boundary sector. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer_apply_image
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
        H N hN beta hbeta n
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryEquiv
          H N hN beta hbeta f) =
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryEquiv
        H N hN beta hbeta
        (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) f) := by
  letI : NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
    osBoundaryOneSidedExcitationTransferPhysicalOrthogonalNormedSpace
      H N hN beta hbeta
  exact
    continuousLinearMapConjugateLinearIsometryEquiv_apply_image
      (𝕜 := ℝ)
      (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta)
      (F := periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySector
        H N hN beta hbeta)
      _ _ _

/-- The one-particle boundary transfer inherits the single-excitation
finite-volume exponential decay rate without the doubled tensor-square rate. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer_apply_norm_le_exp_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n)
    (y : periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySector
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
        H N hN beta hbeta n y‖ ≤
      Real.exp
          (-(n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) * ‖y‖ := by
  letI : NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
    osBoundaryOneSidedExcitationTransferPhysicalOrthogonalNormedSpace
      H N hN beta hbeta
  let U := periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryEquiv
    H N hN beta hbeta
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
  calc
    ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
        H N hN beta hbeta n y‖ =
      ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
        H N hN beta hbeta n (U (U.symm y))‖ := by
      rw [U.apply_symm_apply]
    _ = ‖U ((T ^ n) (U.symm y))‖ := by
      rw [periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer_apply_image]
    _ = ‖(T ^ n) (U.symm y)‖ := by
      exact U.norm_map _
    _ ≤ Real.exp
          (-(n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) * ‖U.symm y‖ := by
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le_exp_of_pos
          H N hN beta hbeta n hn (U.symm y)
    _ = Real.exp
          (-(n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) * ‖y‖ := by
      rw [U.symm.norm_map]

/-- Operator-norm form of the concrete one-particle boundary contraction. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer_opNorm_le_exp_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n) :
    ContinuousLinearMap.opNorm
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
        H N hN beta hbeta n) ≤
      Real.exp
        (-(n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) := by
  letI : NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
    osBoundaryOneSidedExcitationTransferPhysicalOrthogonalNormedSpace
      H N hN beta hbeta
  apply ContinuousLinearMap.opNorm_le_bound
  · exact (Real.exp_pos _).le
  · intro y
    exact
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer_apply_norm_le_exp_of_pos
        H N hN beta hbeta n hn y

/-- Squared-norm form of the same concrete contraction. This is the exact
finite-volume quadratic estimate naturally consumed by the boundary-gap lane;
no scale-uniform lower bound on the finite-volume rate is asserted here. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer_apply_norm_sq_le_exp_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n)
    (y : periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySector
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
        H N hN beta hbeta n y‖ ^ 2 ≤
      Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) * ‖y‖ ^ 2 := by
  letI : NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
    osBoundaryOneSidedExcitationTransferPhysicalOrthogonalNormedSpace
      H N hN beta hbeta
  let r :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  let q := Real.exp (-(n : ℝ) * r)
  have hnorm :
      ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
          H N hN beta hbeta n y‖ ≤ q * ‖y‖ := by
    simpa [q, r] using
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer_apply_norm_le_exp_of_pos
        H N hN beta hbeta n hn y
  have hqnorm : 0 ≤ q * ‖y‖ := by
    dsimp [q]
    positivity
  have hsq :
      ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
          H N hN beta hbeta n y‖ ^ 2 ≤ (q * ‖y‖) ^ 2 := by
    nlinarith [norm_nonneg
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
        H N hN beta hbeta n y), hqnorm]
  calc
    ‖periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundarySectorTransfer
        H N hN beta hbeta n y‖ ^ 2 ≤ (q * ‖y‖) ^ 2 := hsq
    _ = q ^ 2 * ‖y‖ ^ 2 := by ring
    _ = Real.exp (-2 * (n : ℝ) * r) * ‖y‖ ^ 2 := by
      congr 1
      dsimp [q]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    _ = Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) * ‖y‖ ^ 2 := by
      rfl

end

end MathlibAnalytic
end MGAP4D
