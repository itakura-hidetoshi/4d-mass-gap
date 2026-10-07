import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairTensorOrbit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateDeweightedContrast
import Mathlib.Tactic

/-!
# Degeneracy of the two-mode source contrast on the actual adjacent orbit

PR #5238 proves that every actual fine adjacent Krylov orbit vector remains
exactly decomposable,

  x_(n,r,k) = left_(n,r,k) tensor right_(n,r),

with the second-slice factor independent of the mode k.

The normalized pair-transfer observable inherits the same one-slice product
structure.  Since the signed source response modifies only the second source
slice, both the observable and the source response carry the same first-slice
scalar factor.  Hence for two modes sharing one right factor,

  O_v Resp_x - O_x Resp_v = 0.

Consequently the exact cross-multiplied defect of #5232 and its output-deweighted
version from #5233 vanish identically on pairs of actual three-mode orbit
vectors at the same n and r.

This is an obstruction result for the cross-contrast route.  It does not say
that either original one-input defect vanishes, and it does not identify a
posterior covariance with a source-coordinate norm.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section

local instance p3SourceContrastDegeneracyTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3SourceContrastDegeneracyCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3SourceContrastDegeneracySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3SourceContrastDegeneracyMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3SourceContrastDegeneracyBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3SourceContrastDegeneracySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p3SourceContrastDegeneracySpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

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
local notation "PairL2" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "mu" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
local notation "lam" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖
local notation "SqrtD" =>
  continuousJointSqrtDensity H N hN beta hbeta
local notation "Obs" =>
  jointTransferBCF H N hN beta hbeta
local notation "Resp" =>
  sourceLinkResponse H N hN beta hbeta
local notation "Out" =>
  outputRightLinkTilt H N hN beta hbeta

/-- Raw one-slice transfer integral at a fixed output boundary. -/
def decomposableOneSliceTransferIntegral
    (f : SliceL2) (B : Cfg) : ℝ :=
  ∫ A, K A B * f A ∂mu

/-- The literal pair-transfer integral factors pointwise on every decomposable
physical pair.  The input representatives are used only under the Haar
integral, via the existing a.e. external-tensor identity. -/
theorem pairTransferIntegral_physicalPairDecomposableL2
    (f g : PhysicalSlice) (z : Joint) :
    pairTransferIntegral H N beta
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N f g) z =
      decomposableOneSliceTransferIntegral H N beta
          (f : SliceL2) z.1 *
        decomposableOneSliceTransferIntegral H N beta
          (g : SliceL2) z.2 := by
  have hTensor :=
    realL2ExternalTensor_coeFn
      (μ := mu) (ν := mu)
      (f : SliceL2) (g : SliceL2)
  unfold
    pairTransferIntegral
    periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    decomposableOneSliceTransferIntegral
  calc
    (∫ y : Cfg × Cfg,
        (K y.1 z.1 * K y.2 z.2) *
          realL2ExternalTensor (f : SliceL2) (g : SliceL2) y
        ∂(mu.prod mu)) =
      ∫ y : Cfg × Cfg,
        (K y.1 z.1 * (f : SliceL2) y.1) *
          (K y.2 z.2 * (g : SliceL2) y.2)
        ∂(mu.prod mu) := by
      apply integral_congr_ae
      filter_upwards [hTensor] with y hy
      rw [hy]
      simp only [realL2ExternalTensorFunction]
      ring
    _ =
      (∫ A, K A z.1 * (f : SliceL2) A ∂mu) *
        (∫ B, K B z.2 * (g : SliceL2) B ∂mu) := by
      exact integral_prod_mul
        (fun A => K A z.1 * (f : SliceL2) A)
        (fun B => K B z.2 * (g : SliceL2) B)

/-- The actual normalized joint observable of a decomposable physical pair
has one common first-slice scalar factor. -/
theorem jointTransferBCF_physicalPairDecomposableL2_apply
    (f g : PhysicalSlice) (z : Joint) :
    Obs
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N f g) z =
      decomposableOneSliceTransferIntegral H N beta
          (f : SliceL2) z.1 *
        ((lam ^ 2)⁻¹ *
          decomposableOneSliceTransferIntegral H N beta
            (g : SliceL2) z.2 / SqrtD z) := by
  change
    ((lam ^ 2)⁻¹ *
      pairTransferIntegral H N beta
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N f g) z) / SqrtD z = _
  rw [pairTransferIntegral_physicalPairDecomposableL2
    H N beta f g z]
  ring

/-- Right-slice scalar multiplying the first-slice transfer integral in the
joint observable. -/
def decomposableRightOutputFactor
    (g : PhysicalSlice) (z : Joint) : ℝ :=
  (lam ^ 2)⁻¹ *
    decomposableOneSliceTransferIntegral H N beta
      (g : SliceL2) z.2 / SqrtD z

theorem jointTransferBCF_physicalPairDecomposableL2_eq_left_mul_right
    (f g : PhysicalSlice) (z : Joint) :
    Obs
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N f g) z =
      decomposableOneSliceTransferIntegral H N beta
          (f : SliceL2) z.1 *
        decomposableRightOutputFactor H N hN beta hbeta g z := by
  rw [jointTransferBCF_physicalPairDecomposableL2_apply
    H N hN beta hbeta f g z]
  rfl

/-- Right-slice scalar multiplying the same first-slice factor in the signed
source response. -/
def decomposableRightSourceResponseFactor
    (g : PhysicalSlice) (e : Link) (z : Joint) (u : GaugeT) : ℝ :=
  (Out z e u)⁻¹ *
      decomposableRightOutputFactor H N hN beta hbeta g
        (z.1, Function.update z.2 e u) -
    decomposableRightOutputFactor H N hN beta hbeta g z

/-- The signed one-link source response of a decomposable physical pair carries
exactly the same first-slice scalar factor as the observable. -/
theorem sourceLinkResponse_physicalPairDecomposableL2_eq_left_mul_right
    (f g : PhysicalSlice) (e : Link) (z : Joint) (u : GaugeT) :
    Resp
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N f g) e z u =
      decomposableOneSliceTransferIntegral H N beta
          (f : SliceL2) z.1 *
        decomposableRightSourceResponseFactor
          H N hN beta hbeta g e z u := by
  rw [sourceLinkResponse_eq]
  rw [
    jointTransferBCF_physicalPairDecomposableL2_eq_left_mul_right
      H N hN beta hbeta f g (z.1, Function.update z.2 e u),
    jointTransferBCF_physicalPairDecomposableL2_eq_left_mul_right
      H N hN beta hbeta f g z
  ]
  unfold decomposableRightSourceResponseFactor
  ring

/-- Two decomposable inputs sharing one right factor have identically zero
observable/source-response determinant. -/
theorem decomposable_commonRight_sourceResponse_cross_eq_zero
    (f v g : PhysicalSlice) (e : Link) (z : Joint) (u : GaugeT) :
    Obs
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N f g) z *
        Resp
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            H N v g) e z u -
      Obs
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N v g) z *
        Resp
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            H N f g) e z u = 0 := by
  rw [
    jointTransferBCF_physicalPairDecomposableL2_eq_left_mul_right
      H N hN beta hbeta f g z,
    jointTransferBCF_physicalPairDecomposableL2_eq_left_mul_right
      H N hN beta hbeta v g z,
    sourceLinkResponse_physicalPairDecomposableL2_eq_left_mul_right
      H N hN beta hbeta v g e z u,
    sourceLinkResponse_physicalPairDecomposableL2_eq_left_mul_right
      H N hN beta hbeta f g e z u
  ]
  ring

/-- Therefore the exact two-input source contrast itself vanishes for any two
decomposable inputs with a common right factor.  This does not imply either
single-input defect vanishes. -/
theorem decomposable_commonRight_jointTransferSourceContrast_eq_zero
    (f v g : PhysicalSlice) (e : Link) (z : Joint) (u : GaugeT) :
    Obs
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N v g) z *
        jointTransferLinkDifference H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            H N f g) e z u -
      Obs
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N f g) z *
        jointTransferLinkDifference H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            H N v g) e z u = 0 := by
  rw [jointTransferSourceContrast_eq]
  rw [decomposable_commonRight_sourceResponse_cross_eq_zero
    H N hN beta hbeta f v g e z u]
  ring

/-- The output-deweighted #5233 contrast also vanishes; multiplying by the
positive output inverse cannot recover information lost by the common-right
factorization. -/
theorem decomposable_commonRight_jointTransferSourceDeweightedContrast_eq_zero
    (f v g : PhysicalSlice) (e : Link) (z : Joint) (u : GaugeT) :
    jointTransferSourceDeweightedContrast H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N f g)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N v g)
        e z u = 0 := by
  unfold jointTransferSourceDeweightedContrast
  rw [
    decomposable_commonRight_jointTransferSourceContrast_eq_zero
      H N hN beta hbeta f v g e z u
  ]
  simp

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
local notation "Obs" =>
  jointTransferBCF Hn 2 Pos (beta n) (hbeta n)
local notation "Resp" =>
  sourceLinkResponse Hn 2 Pos (beta n) (hbeta n)
local notation "Orbit" =>
  physicalYangMillsSU2AdjacentFinePairOrbitVector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- The literal source-response determinant between any two actual modes at
one fixed orbit depth is zero. -/
theorem fineOrbit_sourceResponse_cross_eq_zero
    (k l : Fin 3) (e : Link) (z : Joint) (u : GaugeT) :
    Obs (Orbit n r k) z * Resp (Orbit n r l) e z u -
      Obs (Orbit n r l) z * Resp (Orbit n r k) e z u = 0 := by
  rw [
    physicalYangMillsSU2AdjacentFinePairOrbitVector_eq_decomposable
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k,
    physicalYangMillsSU2AdjacentFinePairOrbitVector_eq_decomposable
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r l
  ]
  exact
    decomposable_commonRight_sourceResponse_cross_eq_zero
      Hn 2 Pos (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)
      (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r l)
      (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
      e z u

/-- The #5232 cross-multiplied defect between any two actual modes at the same
n and r is identically zero. -/
theorem fineOrbit_jointTransferSourceContrast_eq_zero
    (k l : Fin 3) (e : Link) (z : Joint) (u : GaugeT) :
    Obs (Orbit n r l) z *
        jointTransferLinkDifference Hn 2 Pos (beta n) (hbeta n)
          (Orbit n r k) e z u -
      Obs (Orbit n r k) z *
        jointTransferLinkDifference Hn 2 Pos (beta n) (hbeta n)
          (Orbit n r l) e z u = 0 := by
  rw [
    physicalYangMillsSU2AdjacentFinePairOrbitVector_eq_decomposable
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k,
    physicalYangMillsSU2AdjacentFinePairOrbitVector_eq_decomposable
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r l
  ]
  exact
    decomposable_commonRight_jointTransferSourceContrast_eq_zero
      Hn 2 Pos (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)
      (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r l)
      (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
      e z u

/-- The #5233 deweighted contrast is equally zero on the actual orbit. -/
theorem fineOrbit_jointTransferSourceDeweightedContrast_eq_zero
    (k l : Fin 3) (e : Link) (z : Joint) (u : GaugeT) :
    jointTransferSourceDeweightedContrast Hn 2 Pos (beta n) (hbeta n)
        (Orbit n r k) (Orbit n r l) e z u = 0 := by
  rw [
    physicalYangMillsSU2AdjacentFinePairOrbitVector_eq_decomposable
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k,
    physicalYangMillsSU2AdjacentFinePairOrbitVector_eq_decomposable
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r l
  ]
  exact
    decomposable_commonRight_jointTransferSourceDeweightedContrast_eq_zero
      Hn 2 Pos (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)
      (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r l)
      (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
      e z u

end ActualAdjacentOrbit

end GroundStatePosteriorJoint

end

end MathlibAnalytic
end MGAP4D
