import MGAP4D.MathlibAnalytic.FiniteDimensionalGroundLiftedIntertwiningCompatibilityReduction
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeInvariantCarrierEmbedding
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- Actual one-step transfer intertwining residual on the Gauss-invariant
configuration Hilbert carriers, using the geometrically induced normalized
cross-volume embedding. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTransferIntertwiningResidualLinearMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H) :=
  finiteDimensionalTransferIntertwiningResidualLinearMap
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H).toLinearMap

/-- Actual cross-volume residual of the spectral ground-sector correction. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantGroundCorrectionIntertwiningResidualLinearMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H) :=
  finiteDimensionalGroundCorrectionIntertwiningResidualLinearMap
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H).toLinearMap

/-- Actual ground-lifted defect residual on the Gauss-invariant configuration
Hilbert carriers. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantGroundLiftedIntertwiningResidualLinearMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H) :=
  finiteDimensionalGroundLiftedIntertwiningResidualLinearMap
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H).toLinearMap

/-- Exact actual compatibility reduction on the configuration Hilbert carrier:

`ground-lifted residual = - transfer residual + ground-correction residual`.

The transfer summand is the genuine finite one-slab transfer compatibility
obligation; the second summand is the independent fixed-sector compatibility
obligation introduced by lifting the ground defect. -/
theorem finiteEvenFourTorusZ2GaugeInvariantGroundLiftedIntertwiningResidual_decomposition
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantGroundLiftedIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy =
      - finiteEvenFourTorusZ2GaugeInvariantTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy +
        finiteEvenFourTorusZ2GaugeInvariantGroundCorrectionIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy :=
  finiteDimensionalGroundLiftedIntertwiningResidual_decomposition
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H).toLinearMap

/-- Pointwise actual carrier reduction. -/
theorem finiteEvenFourTorusZ2GaugeInvariantGroundLiftedIntertwiningResidual_decomposition_apply
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GaugeInvariantGroundLiftedIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f =
      - finiteEvenFourTorusZ2GaugeInvariantTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy f +
        finiteEvenFourTorusZ2GaugeInvariantGroundCorrectionIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy f := by
  exact LinearMap.congr_fun
    (finiteEvenFourTorusZ2GaugeInvariantGroundLiftedIntertwiningResidual_decomposition
      H β energyIdentity energyNontrivial hβ hEnergy) f

/-- The transfer residual is literally the mismatch between applying the fine
actual one-slab transfer after the cross-volume embedding and embedding the
coarse actual one-slab transfer.  This exposes the genuine geometric operator
obligation beneath the spectral wrapper. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTransferIntertwiningResidual_apply
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GaugeInvariantTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f =
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        (finiteEvenFourTorusDoubleRefinement H)
        β energyIdentity energyNontrivial hβ hEnergy).operator
          (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H f) -
        finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H
          ((finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
            H β energyIdentity energyNontrivial hβ hEnergy).operator f) :=
  rfl

/-- Underlying configuration-level form of the transfer residual.  The first
term is the actual fine unfixed-gauge one-slab transfer; the second is the
normalized geometric embedding of the actual coarse one-slab transfer. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTransferIntertwiningResidual_apply_coe
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    (finiteEvenFourTorusZ2GaugeInvariantTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f).1 A =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H f).1 A -
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H
          ((finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
            H β energyIdentity energyNontrivial hβ hEnergy).operator f)).1 A := by
  rfl

/-- Orbit-probability strong obstruction evaluated on a canonical orbit image
is exactly the forward image of the actual Gauss-invariant carrier residual.
Thus no information is lost by moving the compatibility problem back to the
configuration Hilbert carrier. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_forward_eq_invariantResidual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy
        ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f) =
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement H)).forward
        (finiteEvenFourTorusZ2GaugeInvariantGroundLiftedIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy f) := by
  let Ic := finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H
  let If := finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
    (finiteEvenFourTorusDoubleRefinement H)
  let J := finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H
  let Df := finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
    (finiteEvenFourTorusDoubleRefinement H)
    β energyIdentity energyNontrivial hβ hEnergy
  let Dc := finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
    H β energyIdentity energyNontrivial hβ hEnergy
  change
    finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
        (finiteEvenFourTorusDoubleRefinement H)
        β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H
          (Ic.forward f)) -
      finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy (Ic.forward f)) =
      If.forward
        (Df (J f) - J (Dc f))
  rw [← finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_forward H f]
  rw [finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_intertwines]
  rw [finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_intertwines]
  rw [← finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_forward H (Dc f)]
  rw [← map_sub]

/-- Norm of the orbit strong obstruction on canonical orbit coordinates is
exactly the norm of the actual invariant-carrier residual. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_forward_norm
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    ‖finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy
        ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)‖ =
      ‖finiteEvenFourTorusZ2GaugeInvariantGroundLiftedIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f‖ := by
  rw [finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_forward_eq_invariantResidual]
  exact
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
      (finiteEvenFourTorusDoubleRefinement H)).forward.norm_map _

/-- Exact equivalence between vanishing of the orbit-probability obstruction
and vanishing of the actual invariant-carrier residual. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff_invariantResidual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2GaugeInvariantGroundLiftedIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 := by
  constructor
  · intro hOrbit
    apply LinearMap.ext
    intro f
    have hf := LinearMap.congr_fun hOrbit
      ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)
    rw [finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_forward_eq_invariantResidual]
      at hf
    exact
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement H)).forward.injective hf
  · intro hCarrier
    apply LinearMap.ext
    intro y
    let f :=
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).inverse y
    have hy :
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f = y :=
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward_inverse y
    rw [← hy]
    rw [finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_forward_eq_invariantResidual]
    have hf := LinearMap.congr_fun hCarrier f
    rw [hf]
    simp

/-- If both actual one-slab transfer compatibility and ground-sector correction
compatibility hold, then the full orbit-probability ground-lifted obstruction
vanishes.  This is a sufficient geometric closure theorem, not an assumption
that those two conditions already hold. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_of_transfer_and_ground
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (hTransfer :
      finiteEvenFourTorusZ2GaugeInvariantTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0)
    (hGround :
      finiteEvenFourTorusZ2GaugeInvariantGroundCorrectionIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0) :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 := by
  apply
    (finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff_invariantResidual
      H β energyIdentity energyNontrivial hβ hEnergy).2
  rw [finiteEvenFourTorusZ2GaugeInvariantGroundLiftedIntertwiningResidual_decomposition,
    hTransfer, hGround]
  simp

/-- Audit-visible Package F reduction: orbit obstruction, actual invariant
carrier residual, actual one-slab transfer residual, and the ground-sector
correction residual are all exposed in one object. -/
structure Z2FiniteEvenFourTorusCrossVolumeActualOperatorCompatibilityReductionPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  embedding :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗᵢ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H)
  embedding_eq : embedding = finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H
  transferResidual :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H)
  transferResidual_eq :
    transferResidual =
      finiteEvenFourTorusZ2GaugeInvariantTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy
  groundCorrectionResidual :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H)
  groundCorrectionResidual_eq :
    groundCorrectionResidual =
      finiteEvenFourTorusZ2GaugeInvariantGroundCorrectionIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy
  groundLiftedResidual :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H)
  groundLiftedResidual_eq :
    groundLiftedResidual =
      finiteEvenFourTorusZ2GaugeInvariantGroundLiftedIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy
  carrierDecomposition :
    groundLiftedResidual = - transferResidual + groundCorrectionResidual
  orbitCarrierEquivalence :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      groundLiftedResidual = 0
  geometricComponentsSuffice :
    transferResidual = 0 → groundCorrectionResidual = 0 →
      finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0

/-- Construct the complete actual compatibility-reduction package. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeActualOperatorCompatibilityReductionPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeActualOperatorCompatibilityReductionPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  embedding := finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H
  embedding_eq := rfl
  transferResidual :=
    finiteEvenFourTorusZ2GaugeInvariantTransferIntertwiningResidualLinearMap
      H β energyIdentity energyNontrivial hβ hEnergy
  transferResidual_eq := rfl
  groundCorrectionResidual :=
    finiteEvenFourTorusZ2GaugeInvariantGroundCorrectionIntertwiningResidualLinearMap
      H β energyIdentity energyNontrivial hβ hEnergy
  groundCorrectionResidual_eq := rfl
  groundLiftedResidual :=
    finiteEvenFourTorusZ2GaugeInvariantGroundLiftedIntertwiningResidualLinearMap
      H β energyIdentity energyNontrivial hβ hEnergy
  groundLiftedResidual_eq := rfl
  carrierDecomposition :=
    finiteEvenFourTorusZ2GaugeInvariantGroundLiftedIntertwiningResidual_decomposition
      H β energyIdentity energyNontrivial hβ hEnergy
  orbitCarrierEquivalence :=
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff_invariantResidual
      H β energyIdentity energyNontrivial hβ hEnergy
  geometricComponentsSuffice :=
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_of_transfer_and_ground
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D
