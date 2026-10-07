import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentSourceContrastDegeneracy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointResamplingDirichlet
import Mathlib.Tactic

/-!
# Exact single-defect factorization on the actual adjacent SU(2) orbit

PR #5239 shows that the two-input cross contrast is identically zero between
actual modes at one fixed orbit depth.  Therefore the original one-input defect
must be retained.

For a decomposable physical pair f tensor g, the observable and signed source
response from #5239 both carry the same first-slice transfer scalar.  The
original one-link defect consequently factors exactly as

  D_(f tensor g)
    = leftTransfer(f) * rightDefect(g).

Specializing with PR #5238 gives, for the unchanged actual orbit,

  D_(n,r,k)
    = left_(n,r,k) * commonRightDefect_(n,r),

where every dependence on the mode k is confined to the first scalar factor and
the right defect is common to all three modes.

The theorem is also substituted into the original resampling Dirichlet energy,
retaining the exact 1/12 normalization.  No output drift is discarded and no
posterior covariance/source-coordinate norm identification is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3SingleDefectFactorizationTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3SingleDefectFactorizationCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3SingleDefectFactorizationSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3SingleDefectFactorizationMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3SingleDefectFactorizationBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3SingleDefectFactorizationSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section GeneralCarrier

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "GaugeT" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "SliceL2" =>
  Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
local notation "PhysicalSlice" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
local notation "Obs" => jointTransferBCF H N hN beta hbeta
local notation "Resp" => sourceLinkResponse H N hN beta hbeta
local notation "Out" => outputRightLinkTilt H N hN beta hbeta

/-- The complete right-slice factor of the ORIGINAL one-input link defect.
Both the output drift and the signed source response are retained. -/
def decomposableRightLinkDifferenceFactor
    (g : PhysicalSlice) (e : Link) (z : Joint) (u : GaugeT) : ℝ :=
  (1 - Out z e u) *
      decomposableRightOutputFactor H N hN beta hbeta g z -
    Out z e u *
      decomposableRightSourceResponseFactor H N hN beta hbeta g e z u

/-- Exact factorization of the original signed defect for an arbitrary
decomposable physical pair. -/
theorem jointTransferLinkDifference_physicalPairDecomposableL2_eq_left_mul_right
    (f g : PhysicalSlice) (e : Link) (z : Joint) (u : GaugeT) :
    jointTransferLinkDifference H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N f g) e z u =
      decomposableOneSliceTransferIntegral H N beta
          (f : SliceL2) z.1 *
        decomposableRightLinkDifferenceFactor
          H N hN beta hbeta g e z u := by
  rw [jointTransferLinkDifference_eq_sourceTilt]
  rw [
    jointTransferBCF_physicalPairDecomposableL2_eq_left_mul_right
      H N hN beta hbeta f g z,
    sourceLinkResponse_physicalPairDecomposableL2_eq_left_mul_right
      H N hN beta hbeta f g e z u
  ]
  unfold decomposableRightLinkDifferenceFactor
  ring

/-- Pointwise squared form used by the original resampling Dirichlet receiver. -/
theorem jointTransferLinkDifference_physicalPairDecomposableL2_sq_eq
    (f g : PhysicalSlice) (e : Link) (z : Joint) (u : GaugeT) :
    (jointTransferLinkDifference H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N f g) e z u) ^ 2 =
      (decomposableOneSliceTransferIntegral H N beta
          (f : SliceL2) z.1) ^ 2 *
        (decomposableRightLinkDifferenceFactor
          H N hN beta hbeta g e z u) ^ 2 := by
  rw [
    jointTransferLinkDifference_physicalPairDecomposableL2_eq_left_mul_right
      H N hN beta hbeta f g e z u
  ]
  ring

end GeneralCarrier

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "GaugeT" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "SliceL2" =>
  Lp ℝ 2
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure Hn 2)
local notation "muJ" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    Hn 2 Pos (beta n) (hbeta n)
local notation "Nu" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
    Hn 2 Pos (beta n) (hbeta n)
local notation "Orbit" =>
  physicalYangMillsSU2AdjacentFinePairOrbitVector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "FrozenVec" =>
  physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- The mode-independent right factor of the actual one-link defect. -/
def fineOrbitRightLinkDifferenceFactor
    (e : Link) (z : Joint) (u : GaugeT) : ℝ :=
  decomposableRightLinkDifferenceFactor
    Hn 2 Pos (beta n) (hbeta n)
    (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r)
    e z u

/-- Every actual three-mode one-input defect factors through the same right
defect at fixed n and r.  No observable is divided by. -/
theorem fineOrbit_jointTransferLinkDifference_eq_left_mul_commonRight
    (k : Fin 3) (e : Link) (z : Joint) (u : GaugeT) :
    jointTransferLinkDifference Hn 2 Pos (beta n) (hbeta n)
        (Orbit n r k) e z u =
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
          ((physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k : _) : SliceL2) z.1 *
        fineOrbitRightLinkDifferenceFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r e z u := by
  rw [
    physicalYangMillsSU2AdjacentFinePairOrbitVector_eq_decomposable
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  ]
  exact
    jointTransferLinkDifference_physicalPairDecomposableL2_eq_left_mul_right
      Hn 2 Pos (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k)
      (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r)
      e z u

/-- Squared actual defect with all mode dependence isolated in the first
scalar factor. -/
theorem fineOrbit_jointTransferLinkDifference_sq_eq_left_sq_mul_commonRight_sq
    (k : Fin 3) (e : Link) (z : Joint) (u : GaugeT) :
    (jointTransferLinkDifference Hn 2 Pos (beta n) (hbeta n)
        (Orbit n r k) e z u) ^ 2 =
      (decomposableOneSliceTransferIntegral Hn 2 (beta n)
          ((physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k : _) : SliceL2) z.1) ^ 2 *
        (fineOrbitRightLinkDifferenceFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r e z u) ^ 2 := by
  rw [
    fineOrbit_jointTransferLinkDifference_eq_left_mul_commonRight
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k e z u
  ]
  ring

/-- The original one-link resampling Dirichlet quantity has an exact
decomposable representation.  The joint law is not factorized. -/
theorem fineOrbit_jointTransferLinkResamplingEnergy_eq_decomposable
    (k : Fin 3) (e : Link) :
    jointTransferLinkResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
        (Orbit n r k) e =
      ∫ z, ∫ u,
        (decomposableOneSliceTransferIntegral Hn 2 (beta n)
            ((physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r k : _) : SliceL2) z.1) ^ 2 *
          (fineOrbitRightLinkDifferenceFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r e z u) ^ 2
        ∂Nu z.1 z.2 e ∂muJ := by
  unfold jointTransferLinkResamplingEnergy
  apply integral_congr_ae
  filter_upwards with z
  apply integral_congr_ae
  filter_upwards with u
  exact
    fineOrbit_jointTransferLinkDifference_sq_eq_left_sq_mul_commonRight_sq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k e z u

/-- Exact 1/12 initial-energy formula for the unchanged frozen family after
the single-input tensor factorization. -/
theorem fineFrozenInitialEnergy_eq_decomposableSingleDefect
    (k : Fin 3) :
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n)
        (FrozenVec n r k) =
      (1 / 12 : ℝ) * ∑ e : Link,
        ∫ z, ∫ u,
          (decomposableOneSliceTransferIntegral Hn 2 (beta n)
              ((physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r k : _) : SliceL2) z.1) ^ 2 *
            (fineOrbitRightLinkDifferenceFactor
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r e z u) ^ 2
          ∂Nu z.1 z.2 e ∂muJ := by
  rw [
    fineFrozenInitialEnergy_eq_resampling
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  ]
  apply congrArg ((1 / 12 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro e _he
  exact
    fineOrbit_jointTransferLinkResamplingEnergy_eq_decomposable
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k e

end ActualAdjacentOrbit

end GroundStatePosteriorJoint

end

end MathlibAnalytic
end MGAP4D
