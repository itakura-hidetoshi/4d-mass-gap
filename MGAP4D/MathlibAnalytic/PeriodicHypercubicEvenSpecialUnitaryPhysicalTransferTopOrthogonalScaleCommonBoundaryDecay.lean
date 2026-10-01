import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferUniformTopOrthogonalPowerDecay
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryOneSidedExcitationTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonInteractingBoundaryScaleCommonVacuumCarrier
import MGAP4D.MathlibAnalytic.RealLinearIsometryRangeIdentification
import Mathlib.Tactic

/-!
# Put all finite top-orthogonal transfer dynamics on one common interacting boundary carrier

PR #4983 gives one common geometric decay factor for the full physical
top-eigenspace-orthogonal sector at every finite scale.  The first H1 task is
to place those varying finite Hilbert spaces in one common Hilbert carrier
without assuming a false exact coarse-graining relation between periodic
Wilson Gibbs laws.

The repository already contains exactly the required isometries:

* top-orthogonal physical one-slice sector -> actual shared-boundary Haar L2;
* reciprocal-vacuum Haar L2 -> the actual interacting boundary marginal L2;
* finite marginal L2 -> one coordinate of the infinite product common L2.

Their composition embeds every finite top-orthogonal sector isometrically into
the same interacting infinite-product Hilbert space.  Conjugating the finite
transfer powers to the exact image range preserves the #4983 decay coefficient
with no volume, rank, scale, or embedding loss.

This file deliberately does NOT identify these image ranges with the
vacuum-orthogonal sector of the finite periodic OS Hilbert space.  That is a
separate compatibility statement: the periodic OS boundary vacuum and the
one-slab Perron/top sector must not be identified by name alone.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

section ScalingFamily

variable
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)

/-- The single interacting infinite-product boundary Hilbert space containing
isometric copies of every finite top-orthogonal physical one-slice sector. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryL2 :=
  Lp ℝ 2
    (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalInfiniteProduct
      halfExtent N hN beta hbeta)

/-- Exact isometric embedding of one finite physical top-orthogonal sector into
the interacting common boundary product.

The three factors are, in order:
1. the existing one-sided excitation boundary isometry;
2. reciprocal-vacuum transport to the actual interacting finite marginal;
3. coordinate pullback into the common infinite product. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTopOrthogonalToScaleCommonBoundaryLinearIsometry
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n) →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryL2
        halfExtent N hN beta hbeta :=
  (physicalYangMillsEvenPeriodicWilsonBoundaryMarginalL2ToScaleCommon
      halfExtent N hN beta hbeta n).comp
    ((periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry
        (halfExtent n) N hN (beta n) (hbeta n)).comp
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
        (halfExtent n) N hN (beta n) (hbeta n)))

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryTopOrthogonalToScaleCommonBoundaryLinearIsometry_norm
    (n : ℕ)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)) :
    ‖periodicHypercubicEvenSpecialUnitaryTopOrthogonalToScaleCommonBoundaryLinearIsometry
        halfExtent N hN beta hbeta n x‖ = ‖x‖ :=
  LinearIsometry.norm_map _ x

/-- The actual finite-scale excitation image inside the common product
carrier.  Different scales need not have equal or nested ranges. -/
abbrev
    PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundarySector
    (n : ℕ) :=
  LinearMap.range
    (periodicHypercubicEvenSpecialUnitaryTopOrthogonalToScaleCommonBoundaryLinearIsometry
      halfExtent N hN beta hbeta n).toLinearMap

/-- Canonical isometric equivalence from the finite top-orthogonal sector onto
its exact common-carrier range. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryEquiv
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n) ≃ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundarySector
        halfExtent N hN beta hbeta n :=
  realLinearIsometryEquivRange
    (periodicHypercubicEvenSpecialUnitaryTopOrthogonalToScaleCommonBoundaryLinearIsometry
      halfExtent N hN beta hbeta n)

/-- The k-step finite physical top-orthogonal transfer, transported to the
exact finite-scale range inside the common interacting product Hilbert space. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryTransferPower
    (n k : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundarySector
        halfExtent N hN beta hbeta n →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundarySector
        halfExtent N hN beta hbeta n :=
  continuousLinearMapConjugateLinearIsometryEquiv
    (periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryEquiv
      halfExtent N hN beta hbeta n)
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)) ^ k)

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryTransferPower_apply_image
    (n k : ℕ)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)) :
    periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryTransferPower
        halfExtent N hN beta hbeta n k
        (periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryEquiv
          halfExtent N hN beta hbeta n x) =
      periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryEquiv
        halfExtent N hN beta hbeta n
        (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n)) ^ k) x) := by
  exact
    continuousLinearMapConjugateLinearIsometryEquiv_apply_image
      (periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryEquiv
        halfExtent N hN beta hbeta n)
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n)) ^ k)
      x

/-- The actual k-step finite trajectory, viewed directly as a vector in the
single ambient common product L2. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryTrajectory
    (n k : ℕ)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)) :
    PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryL2
      halfExtent N hN beta hbeta :=
  periodicHypercubicEvenSpecialUnitaryTopOrthogonalToScaleCommonBoundaryLinearIsometry
    halfExtent N hN beta hbeta n
    (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)) ^ k) x)

/-- H1 common-carrier vector decay: after the exact isometric embedding, the
#4983 scale-independent geometric estimate is unchanged. -/
theorem
    periodicHypercubicEvenSpecialUnitary_topOrthogonalScaleCommonBoundaryTrajectory_norm_le
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n k : ℕ) (hk : 0 < k)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)) :
    ‖periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryTrajectory
        halfExtent N hN beta hbeta n k x‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
        ‖periodicHypercubicEvenSpecialUnitaryTopOrthogonalToScaleCommonBoundaryLinearIsometry
          halfExtent N hN beta hbeta n x‖ := by
  let I :=
    periodicHypercubicEvenSpecialUnitaryTopOrthogonalToScaleCommonBoundaryLinearIsometry
      halfExtent N hN beta hbeta n
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      (halfExtent n) N hN (beta n) (hbeta n)
  let q :=
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor
  change ‖I ((R ^ k) x)‖ ≤ q ^ k * ‖I x‖
  rw [I.norm_map, I.norm_map]
  simpa [R, q] using
    periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalTransferOperator_pow_apply_norm_le
      halfExtent N hN beta hbeta s hs hcut n k hk x

/-- The same geometric estimate holds intrinsically for every vector of the
finite-scale range subspace inside the common Hilbert carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitary_topOrthogonalScaleCommonBoundaryTransferPower_apply_norm_le
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n k : ℕ) (hk : 0 < k)
    (y :
      PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundarySector
        halfExtent N hN beta hbeta n) :
    ‖periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryTransferPower
        halfExtent N hN beta hbeta n k y‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
        ‖y‖ := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryEquiv
      halfExtent N hN beta hbeta n
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      (halfExtent n) N hN (beta n) (hbeta n)
  let q :=
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor
  have hDecay :=
    periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalTransferOperator_pow_apply_norm_le
      halfExtent N hN beta hbeta s hs hcut n k hk (E.symm y)
  change
    ‖continuousLinearMapConjugateLinearIsometryEquiv E (R ^ k) y‖ ≤
      q ^ k * ‖y‖
  rw [continuousLinearMapConjugateLinearIsometryEquiv_apply]
  calc
    ‖E ((R ^ k) (E.symm y))‖ = ‖(R ^ k) (E.symm y)‖ :=
      E.norm_map _
    _ ≤ q ^ k * ‖E.symm y‖ := by
      simpa [R, q] using hDecay
    _ = q ^ k * ‖y‖ := by
      rw [E.symm.norm_map]

/-- Operator-norm form on every finite-scale common-carrier range.  The exact
same q0^k controls all scales. -/
theorem
    periodicHypercubicEvenSpecialUnitary_topOrthogonalScaleCommonBoundaryTransferPower_norm_le
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n k : ℕ) (hk : 0 < k) :
    ‖periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryTransferPower
        halfExtent N hN beta hbeta n k‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact pow_nonneg
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor_nonneg
      k
  · intro y
    exact
      periodicHypercubicEvenSpecialUnitary_topOrthogonalScaleCommonBoundaryTransferPower_apply_norm_le
        halfExtent N hN beta hbeta s hs hcut n k hk y

/-- Audit-visible H1 common-carrier receipt.  Every finite top-orthogonal
sector has a literal isometric realization in the same interacting product L2,
and every positive transfer power obeys the same exact geometric norm bound on
its realized range. -/
structure
    PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryDecayPackage
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) : Prop where
  embeddingIsometric :
    ∀ (n : ℕ)
      (x :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          (halfExtent n) N hN (beta n) (hbeta n)),
      ‖periodicHypercubicEvenSpecialUnitaryTopOrthogonalToScaleCommonBoundaryLinearIsometry
          halfExtent N hN beta hbeta n x‖ = ‖x‖
  trajectoryDecay :
    ∀ (n k : ℕ), 0 < k →
      ∀ x :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          (halfExtent n) N hN (beta n) (hbeta n),
        ‖periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryTrajectory
            halfExtent N hN beta hbeta n k x‖ ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
            ‖periodicHypercubicEvenSpecialUnitaryTopOrthogonalToScaleCommonBoundaryLinearIsometry
              halfExtent N hN beta hbeta n x‖
  rangePowerNorm :
    ∀ (n k : ℕ), 0 < k →
      ‖periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryTransferPower
          halfExtent N hN beta hbeta n k‖ ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k

theorem
    periodicHypercubicEvenSpecialUnitary_topOrthogonalScaleCommonBoundaryDecayPackage
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryDecayPackage
      halfExtent N hN beta hbeta s hs hcut := by
  refine
    { embeddingIsometric := ?_
      trajectoryDecay := ?_
      rangePowerNorm := ?_ }
  · intro n x
    exact
      periodicHypercubicEvenSpecialUnitaryTopOrthogonalToScaleCommonBoundaryLinearIsometry_norm
        halfExtent N hN beta hbeta n x
  · intro n k hk x
    exact
      periodicHypercubicEvenSpecialUnitary_topOrthogonalScaleCommonBoundaryTrajectory_norm_le
        halfExtent N hN beta hbeta s hs hcut n k hk x
  · intro n k hk
    exact
      periodicHypercubicEvenSpecialUnitary_topOrthogonalScaleCommonBoundaryTransferPower_norm_le
        halfExtent N hN beta hbeta s hs hcut n k hk

end ScalingFamily

end

end MathlibAnalytic
end MGAP4D
