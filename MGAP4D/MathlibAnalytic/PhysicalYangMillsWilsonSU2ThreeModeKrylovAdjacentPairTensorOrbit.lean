import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentOrbitGeometryFiniteRepresentation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2LiteralOneSidedDynamics
import Mathlib.Tactic

/-!
# Exact tensor factorization of the actual adjacent SU(2) Krylov orbit

The primary-plaquette Gram--Schmidt pair seed is exactly a decomposable
physical pair, with the mode on the first spatial slice and the constant
physical unit vector on the second slice.  The literal pair Wilson transfer is
the tensor product of the two one-slice transfers, and the normalized pair
transfer uses exactly the square of the one-slice physical top norm.

Consequently the normalized pair transfer preserves every decomposable
physical pair exactly, acting by the normalized one-slice physical transfer on
each factor.  The same statement holds for every natural power.

Specializing to the actual adjacent fine Krylov orbit gives

  orbit(n,r,k) = leftFactor(n,r,k) tensor rightFactor(n,r),

where the right factor is independent of the mode k.

This file is only an exact finite-volume tensor-structure theorem.  It does
not identify posterior covariance with a source-coordinate norm, does not
discard the output drift, and does not assert any spatial support property at
positive transfer depth.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section

local instance p3PairTensorOrbitTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3PairTensorOrbitCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3PairTensorOrbitSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3PairTensorOrbitMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3PairTensorOrbitBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3PairTensorOrbitSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p3PairTensorOrbitSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The normalized physical pair transfer acts factorwise on every
decomposable physical pair. -/
theorem
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_physicalPairDecomposableL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        H N) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N f g) =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
        H N
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta f)
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta g) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
    periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
  simp only [ContinuousLinearMap.smul_apply]
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_externalTensor
  ]
  simp only [
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply,
    Submodule.coe_smul,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_coe
  ]
  rw [realL2ExternalTensor_smul_left, realL2ExternalTensor_smul_right]
  simpa only [pow_two, smul_smul, mul_inv_rev]

/-- Every natural power of the normalized physical pair transfer continues to
act factorwise on decomposable physical pairs. -/
theorem
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_pow_apply_physicalPairDecomposableL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m : ℕ)
    (f g :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        H N) :
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        H N hN beta hbeta ^ m)
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
          H N f g) =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
        H N
        ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta ^ m) f)
        ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta ^ m) g) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      simp only [pow_succ', ContinuousLinearMap.mul_apply]
      rw [ih]
      exact
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_apply_physicalPairDecomposableL2
          H N hN beta hbeta _ _

/-- First-slice factor of the actual fine SU(2) Krylov orbit. -/
noncomputable def physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ)
    (k : Fin 3) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent (n + 1)) 2 :=
  (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta (n + 1)) (hbeta (n + 1)) ^ r)
    (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
      (halfExtent (n + 1)) k.1)

/-- Second-slice factor of the actual fine SU(2) Krylov orbit.  It is
definitionally independent of the three-mode label k. -/
noncomputable def physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent (n + 1)) 2 :=
  (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta (n + 1)) (hbeta (n + 1)) ^ r)
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
      (halfExtent (n + 1)) 2)

/-- Exact tensor factorization of the unchanged actual fine Krylov orbit.
The second factor is common to all three primary modes. -/
theorem physicalYangMillsSU2AdjacentFinePairOrbitVector_eq_decomposable
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ)
    (k : Fin 3) :
    physicalYangMillsSU2AdjacentFinePairOrbitVector
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
        (halfExtent (n + 1)) 2
        (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k)
        (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) := by
  unfold
    physicalYangMillsSU2AdjacentFinePairOrbitVector
    physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
  rw [
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2_eq_physicalDecomposable
  ]
  exact
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator_pow_apply_physicalPairDecomposableL2
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta (n + 1)) (hbeta (n + 1)) r
      (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
        (halfExtent (n + 1)) k.1)
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
        (halfExtent (n + 1)) 2)

end

end MathlibAnalytic
end MGAP4D
