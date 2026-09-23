import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStatePhysicalPairHaarOrthogonalBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSixSpatialProductHaarRayleighConstant
import Mathlib.Tactic

/-!
# Genuine physical beta-zero six-spatial exact frame/Rayleigh package

This unit closes the direct literal pair-Haar endpoint package on the genuine
physical beta-zero top-orthogonal sector.

For a physical top-orthogonal vector `x`, pull its ambient Haar representative
to the right coordinate of pair Haar.  The bridge theorem from the preceding
unit places that vector in the orthogonal complement of the complete
left-boundary L2 sector.  The exact pair-Haar six-spatial theorem then applies
without rebuilding any product-probability geometry.

The resulting coefficients are exactly those of the literal pair-Haar
argument:

* frame coefficient `kappa_0 = 1/6`;
* random-scan Rayleigh factor `q_0 = 5/6`.

The right-boundary pullback is a linear isometry, so the norm on the right-hand
side is the genuine physical norm inherited from the Gauss-law Hilbert
submodule.

This file does not yet identify the literal pair-Haar random-scan operator with
the proof-indexed genuine ground-state random scan used by the downstream
`3 * (1 - q) / 8` transfer-gap receiver.  That operator-transport statement
is a separate additive unit.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance betaZeroPhysicalSixSpatialPackageTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance betaZeroPhysicalSixSpatialPackageCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance betaZeroPhysicalSixSpatialPackageSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance betaZeroPhysicalSixSpatialPackageMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroPhysicalSixSpatialPackageBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance betaZeroPhysicalSixSpatialPackageSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Canonical literal pair-Haar right-boundary image of a genuine physical
beta-zero top-orthogonal vector. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector
    (H N : ℕ)
    (hN : 0 < N)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN 0 (by norm_num)) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundaryL2Isometry
    H N
    (((x :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        H N) :
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))

/-- The canonical literal pair-Haar boundary image preserves the genuine
physical norm. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector_norm
    (H N : ℕ)
    (hN : 0 < N)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN 0 (by norm_num)) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector
        H N hN x‖ =
      ‖(x :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          H N)‖ := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector
  simpa using
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundaryL2Isometry
      H N).norm_map
      (((x :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          H N) :
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))

/-- The canonical literal pair-Haar boundary image of a physical beta-zero
top-orthogonal vector lies in the complete left-boundary orthogonal sector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector_mem_fst_orthogonal
    (H N : ℕ)
    (hN : 0 < N)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN 0 (by norm_num)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector
        H N hN x ∈
      (lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))ᗮ := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPairHaarRightBoundary_topOrthogonal_mem_fst_orthogonal
      H N hN x)

/-- Genuine physical beta-zero endpoint, frame form: after the canonical
right-boundary pair-Haar pullback, the exact six-spatial normalized residual
energy has coefficient `kappa_0 = 1/6` against the physical norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatialPairHaar_frame_one_six
    (H N : ℕ)
    (hN : 0 < N)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN 0 (by norm_num)) :
    (1 / 6 : ℝ) *
        ‖(x :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            H N)‖ ^ 2 ≤
      groundStateJointColorNormalizedResidualEnergy
        (fun c =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
            H N c)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector
          H N hN x) := by
  have hx :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector_mem_fst_orthogonal
      H N hN x
  have hframe :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaar_frame_one_six_of_mem_fst_orthogonal
      H N
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector
        H N hN x)
      hx
  simpa using hframe

/-- Genuine physical beta-zero endpoint, Rayleigh form: after the canonical
right-boundary pair-Haar pullback, the exact six-spatial random scan has
`q_0 = 5/6` against the physical norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatialPairHaarRandomScan_rayleigh_five_six
    (H N : ℕ)
    (hN : 0 < N)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN 0 (by norm_num)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarRandomScan
          H N
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector
            H N hN x))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector
          H N hN x) ≤
      (5 / 6 : ℝ) *
        ‖(x :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            H N)‖ ^ 2 := by
  have hx :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector_mem_fst_orthogonal
      H N hN x
  have hRayleigh :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarRandomScan_rayleigh_five_six_of_mem_fst_orthogonal
      H N
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector
        H N hN x)
      hx
  simpa using hRayleigh

/-- Packaged genuine physical beta-zero six-spatial endpoint.  The two exact
literal pair-Haar constants are exposed together on the canonical boundary
image of a physical top-orthogonal vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatialPairHaar_exact_package
    (H N : ℕ)
    (hN : 0 < N)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN 0 (by norm_num)) :
    ((1 / 6 : ℝ) *
        ‖(x :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            H N)‖ ^ 2 ≤
      groundStateJointColorNormalizedResidualEnergy
        (fun c =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
            H N c)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector
          H N hN x)) ∧
    (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarRandomScan
          H N
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector
            H N hN x))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalPairHaarBoundaryVector
          H N hN x) ≤
      (5 / 6 : ℝ) *
        ‖(x :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            H N)‖ ^ 2) := by
  exact ⟨
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatialPairHaar_frame_one_six
      H N hN x,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroPhysicalSixSpatialPairHaarRandomScan_rayleigh_five_six
      H N hN x⟩

end

end MGAP4D.MathlibAnalytic
