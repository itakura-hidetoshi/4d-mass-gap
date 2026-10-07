import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairTensorOrbit
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

/-!
# Endpoint-swap equivariance of the actual adjacent pair orbit

The ordered pair-Haar carrier has a canonical endpoint swap

  (A,B) ↦ (B,A),

which preserves the product Haar probability measure.  This file packages the
corresponding lossless real-L2 pullback as a linear isometry and proves:

* a.e. pointwise action by coordinate swap;
* exact exchange of decomposable tensors f ⊗ g ↔ g ⊗ f;
* exact commutation, on every decomposable physical pair, with the normalized
  physical pair transfer;
* the same commutation for arbitrary natural powers;
* exact swap formula for the actual adjacent SU(2) Krylov orbit.

This is the carrier-level prerequisite for transferring the existing
right-boundary conditional-expectation energy to the left boundary.  No
posterior covariance estimate, hard support, or new physical hypothesis is
introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section

local instance p3PairSwapTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3PairSwapCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3PairSwapSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3PairSwapMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3PairSwapBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3PairSwapSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Endpoint swap on ordered pair-Haar L2, bundled as an exact linear isometry. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  change Lp ℝ 2 (μ.prod μ) →ₗᵢ[ℝ] Lp ℝ 2 (μ.prod μ)
  exact
    Lp.compMeasurePreservingₗᵢ ℝ Prod.swap
      (Measure.measurePreserving_swap :
        MeasurePreserving Prod.swap (μ.prod μ) (μ.prod μ))

/-- The pair-swap isometry is represented a.e. by literal coordinate swap. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry_coeFn
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry H N f =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      fun z => f z.swap := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  change
    Lp.compMeasurePreserving Prod.swap
        (Measure.measurePreserving_swap :
          MeasurePreserving Prod.swap (μ.prod μ) (μ.prod μ)) f =ᵐ[μ.prod μ]
      fun z => f z.swap
  simpa [Function.comp_def] using
    (Lp.coeFn_compMeasurePreserving f
      (Measure.measurePreserving_swap :
        MeasurePreserving Prod.swap (μ.prod μ) (μ.prod μ)))

/-- Endpoint swap exchanges the two factors of every external tensor exactly. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry_apply_externalTensor
    (H N : ℕ)
    (f g :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry H N
        (realL2ExternalTensor f g) =
      realL2ExternalTensor g f := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  apply Lp.ext
  have hSwap :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry_coeFn
      H N (realL2ExternalTensor f g)
  have hfg := realL2ExternalTensor_coeFn (μ := μ) (ν := μ) f g
  have hgf := realL2ExternalTensor_coeFn (μ := μ) (ν := μ) g f
  have hfgSwap :=
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hfg)
  filter_upwards [hSwap, hfgSwap, hgf] with z hs hfgs hgfs
  calc
    ((periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry H N)
        (realL2ExternalTensor f g)) z =
        (realL2ExternalTensor f g) z.swap := hs
    _ = realL2ExternalTensorFunction f g z.swap := hfgs
    _ = realL2ExternalTensorFunction g f z := by
      simp only [realL2ExternalTensorFunction, Prod.fst_swap, Prod.snd_swap]
      ring
    _ = (realL2ExternalTensor g f) z := hgfs.symm

/-- Swap exchanges the factors of every decomposable physical pair. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry_apply_physicalPairDecomposableL2
    (H N : ℕ)
    (f g :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N f g) =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
        H N g f := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
  exact
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry_apply_externalTensor
      H N
      (f :
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
      (g :
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- On every decomposable physical pair, endpoint swap commutes exactly with
the normalized physical pair transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_pairSwap_commute_decomposable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry H N
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            H N f g)) =
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry H N
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            H N f g)) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_physicalPairDecomposableL2,
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry_apply_physicalPairDecomposableL2,
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry_apply_physicalPairDecomposableL2,
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_physicalPairDecomposableL2
  ]

/-- Natural powers of the normalized pair transfer have the same exact swap
equivariance on decomposable physical pairs. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_pow_pairSwap_commute_decomposable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m : ℕ)
    (f g :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry H N
        ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
            H N hN beta hbeta ^ m)
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            H N f g)) =
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          H N hN beta hbeta ^ m)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry H N
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
            H N f g)) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_pow_apply_physicalPairDecomposableL2,
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry_apply_physicalPairDecomposableL2,
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry_apply_physicalPairDecomposableL2,
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_pow_apply_physicalPairDecomposableL2
  ]

/-- Exact swapped form of the actual adjacent fine Krylov orbit: the common
right factor moves to the first endpoint and the mode-dependent seed-evolved
factor moves to the second endpoint. -/
theorem physicalYangMillsSU2AdjacentFinePairOrbitVector_pairSwap_eq_decomposable
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ)
    (k : Fin 3) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry
        (halfExtent (n + 1)) 2
        (physicalYangMillsSU2AdjacentFinePairOrbitVector
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k) =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
        (halfExtent (n + 1)) 2
        (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r)
        (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k) := by
  rw [
    physicalYangMillsSU2AdjacentFinePairOrbitVector_eq_decomposable,
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairSwapLinearIsometry_apply_physicalPairDecomposableL2
  ]

end

end MathlibAnalytic
end MGAP4D
