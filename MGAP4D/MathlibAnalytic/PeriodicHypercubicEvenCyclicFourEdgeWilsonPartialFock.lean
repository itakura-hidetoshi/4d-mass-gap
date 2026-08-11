import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeTemporalCompanionTaylor

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators InnerProduct InnerProductSpace Topology

noncomputable section

private theorem cyclicFourEdgeWilsonPartialTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

/-- One coordinate of a four-edge tuple, equipped with the exact finite Taylor
Hilbert feature of the `SU(2)` Wilson relative kernel.  The Taylor degree is
truncated independently on each edge. -/
noncomputable def specialUnitaryTwoFourEdgeCoordinateWilsonPartialFeature
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (k : Fin 4) :
    RealHilbertKernelFeature
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (fun x y =>
        specialUnitaryWilsonRelativeKernelPartial 2 beta degree (x k) (y k)) :=
  (specialUnitaryWilsonRelativeKernelPartialConcreteFeature
      2 cyclicFourEdgeWilsonPartialTwoRankPositive beta hbeta degree).comap
    (fun x => x k)

/-- Product of the four independently truncated Wilson relative kernels in the
validated cyclic pair order `(2,3)|(0,1)`.

Unlike the diagonal power kernel, this retains the full finite four-factor
multi-degree Taylor content: each of the four exponential factors carries its
own sum over degrees `0,...,degree`. -/
def specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel
    (beta : ℝ)
    (degree : ℕ)
    (x y : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  (specialUnitaryWilsonRelativeKernelPartial 2 beta degree (x 2) (y 2) *
      specialUnitaryWilsonRelativeKernelPartial 2 beta degree (x 3) (y 3)) *
    (specialUnitaryWilsonRelativeKernelPartial 2 beta degree (x 0) (y 0) *
      specialUnitaryWilsonRelativeKernelPartial 2 beta degree (x 1) (y 1))

/-- Exact Hilbert realization of the full finite four-factor Wilson Taylor
product.  It is assembled from four independent exponential-partial features,
not from a single common tensor degree. -/
noncomputable def specialUnitaryTwoCyclicFourEdgeWilsonPartialProductFeature
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ) :
    RealHilbertKernelFeature
      (Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree) := by
  let C₂ := specialUnitaryTwoFourEdgeCoordinateWilsonPartialFeature beta hbeta degree 2
  let C₃ := specialUnitaryTwoFourEdgeCoordinateWilsonPartialFeature beta hbeta degree 3
  let C₀ := specialUnitaryTwoFourEdgeCoordinateWilsonPartialFeature beta hbeta degree 0
  let C₁ := specialUnitaryTwoFourEdgeCoordinateWilsonPartialFeature beta hbeta degree 1
  simpa [specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel, C₂, C₃, C₀, C₁] using
    RealHilbertKernelFeature.mul
      (RealHilbertKernelFeature.mul C₂ C₃)
      (RealHilbertKernelFeature.mul C₀ C₁)

/-- Pull the full finite four-factor Wilson Fock feature to the four actual
shared-boundary edges of the canonical primary spatial plaquette. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonPartialFeature
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ) :
    RealHilbertKernelFeature
      ((periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (fun b c =>
        specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H c)) :=
  (specialUnitaryTwoCyclicFourEdgeWilsonPartialProductFeature beta hbeta degree).comap
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H)

/-- Pull the same full finite four-factor Wilson Fock carrier to the four actual
positive-half temporal-companion paths. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWilsonPartialFeature
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ) :
    RealHilbertKernelFeature
      ((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
        (Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (fun x z =>
        specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x)
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H z)) :=
  (specialUnitaryTwoCyclicFourEdgeWilsonPartialProductFeature beta hbeta degree).comap
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H)

/-- Boundary/open-half rectangular pairing for the complete finite four-factor
Taylor feature.  Both pullbacks use literally the same Hilbert carrier, so no
additional completion transport is required. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryOpenHalfFourEdgeWilsonPartialFeature_inner
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    inner ℝ
        ((periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonPartialFeature
          H beta hbeta degree).feature b)
        ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWilsonPartialFeature
          H beta hbeta degree).feature x) =
      specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x) := by
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonPartialFeature,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWilsonPartialFeature] using
    ((specialUnitaryTwoCyclicFourEdgeWilsonPartialProductFeature beta hbeta degree).kernel_eq_inner
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x)).symm

/-- One finite Wilson relative-kernel factor, evaluated on an actual physical
boundary edge and temporal-companion open path, is exactly `exp(-beta)` times
the finite Taylor sum of the literal companion plaquette trace. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionWilsonRelativeKernelPartial_eq_actualTraceSum
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (degree : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (k : Fin 4) :
    specialUnitaryWilsonRelativeKernelPartial 2 beta degree
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b k)
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x k) =
      Real.exp (-beta) *
        ∑ m ∈ Finset.range (degree + 1),
          (beta *
            periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace
              H b x y k) ^ m /
            (Nat.factorial m : ℝ) := by
  unfold specialUnitaryWilsonRelativeKernelPartial
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionExponentialPartialKernel_eq_sum_actualTrace
    hH degree beta b x y k]

/-- Exact finite four-factor expansion on the actual temporal companions.  It
is intentionally kept as a product of four independent finite sums; expanding
this expression yields the full rectangular multi-index set rather than only
the diagonal `(m,m,m,m)` sector. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryOpenHalfFourEdgeWilsonPartialKernel_eq_product_actualTraceSums
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (degree : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x) =
      ((Real.exp (-beta) *
          ∑ m ∈ Finset.range (degree + 1),
            (beta *
              periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace
                H b x y 2) ^ m / (Nat.factorial m : ℝ)) *
        (Real.exp (-beta) *
          ∑ m ∈ Finset.range (degree + 1),
            (beta *
              periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace
                H b x y 3) ^ m / (Nat.factorial m : ℝ))) *
      ((Real.exp (-beta) *
          ∑ m ∈ Finset.range (degree + 1),
            (beta *
              periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace
                H b x y 0) ^ m / (Nat.factorial m : ℝ)) *
        (Real.exp (-beta) *
          ∑ m ∈ Finset.range (degree + 1),
            (beta *
              periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace
                H b x y 1) ^ m / (Nat.factorial m : ℝ))) := by
  unfold specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionWilsonRelativeKernelPartial_eq_actualTraceSum
      hH beta degree b x y 2,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionWilsonRelativeKernelPartial_eq_actualTraceSum
      hH beta degree b x y 3,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionWilsonRelativeKernelPartial_eq_actualTraceSum
      hH beta degree b x y 0,
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionWilsonRelativeKernelPartial_eq_actualTraceSum
      hH beta degree b x y 1]

/-- The exact one-plaquette Wilson Boltzmann factor of an actual temporal
companion is the Wilson relative kernel of its shared boundary edge against its
positive-half open path. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionWilsonBoltzmannCentralFunction_eq_relativeKernel
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (k : Fin 4) :
    specialUnitaryWilsonBoltzmannCentralFunction 2 beta
        (periodicHypercubicPlaquetteHolonomy
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)) =
      specialUnitaryWilsonRelativeKernel 2 beta
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b k)
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x k) := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionWilsonBoltzmannCentralFunction_eq_relativeKernelExp
    hH beta b x y k]
  rw [specialUnitaryWilsonRelativeKernel_eq_trace]

/-- The complete finite four-factor Hilbert kernel converges pointwise to the
product of the four exact Wilson relative kernels. -/
theorem specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel_tendsto
    (beta : ℝ)
    (u v : Fin 4 → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Tendsto
      (fun degree => specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree u v)
      atTop
      (𝓝
        ((specialUnitaryWilsonRelativeKernel 2 beta (u 2) (v 2) *
            specialUnitaryWilsonRelativeKernel 2 beta (u 3) (v 3)) *
          (specialUnitaryWilsonRelativeKernel 2 beta (u 0) (v 0) *
            specialUnitaryWilsonRelativeKernel 2 beta (u 1) (v 1)))) := by
  exact
    ((specialUnitaryWilsonRelativeKernelPartial_tendsto 2 beta (u 2) (v 2)).mul
      (specialUnitaryWilsonRelativeKernelPartial_tendsto 2 beta (u 3) (v 3))).mul
      ((specialUnitaryWilsonRelativeKernelPartial_tendsto 2 beta (u 0) (v 0)).mul
        (specialUnitaryWilsonRelativeKernelPartial_tendsto 2 beta (u 1) (v 1)))

/-- On the actual boundary/open-half temporal companions, the full finite Fock
kernel therefore converges to the literal product of the four selected Wilson
Boltzmann plaquette factors. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryOpenHalfFourEdgeWilsonPartialKernel_tendsto_actualWilson
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    Tendsto
      (fun degree =>
        specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x))
      atTop
      (𝓝
        ((specialUnitaryWilsonBoltzmannCentralFunction 2 beta
            (periodicHypercubicPlaquetteHolonomy
              ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 2)) *
          specialUnitaryWilsonBoltzmannCentralFunction 2 beta
            (periodicHypercubicPlaquetteHolonomy
              ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 3))) *
        (specialUnitaryWilsonBoltzmannCentralFunction 2 beta
            (periodicHypercubicPlaquetteHolonomy
              ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 0)) *
          specialUnitaryWilsonBoltzmannCentralFunction 2 beta
            (periodicHypercubicPlaquetteHolonomy
              ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H 1)))) := by
  have h := specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel_tendsto beta
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x)
  simpa only [← periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionWilsonBoltzmannCentralFunction_eq_relativeKernel
      hH beta b x y] using h

end

end MathlibAnalytic
end MGAP4D
