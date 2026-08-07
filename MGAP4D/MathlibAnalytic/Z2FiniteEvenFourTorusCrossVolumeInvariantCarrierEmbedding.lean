import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeIntertwiningObstructionDecomposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- Raw pullback of a coarse gauge-invariant configuration wavefunction along
the actual geometric fine-to-coarse `Z₂` configuration map.  Gauge invariance
is proved from the previously established actual gauge equivariance. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantConfigurationCoarsePullbackLinearMap
    (H : ℕ) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H) where
  toFun f :=
    ⟨WithLp.toLp 2 fun A : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H) =>
        f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A), by
      intro g A
      change
        f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H (g • A)) =
          f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A)
      rw [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_smul]
      exact f.2
        (finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap H g)
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A)⟩
  map_add' f g := by
    apply Subtype.ext
    ext A
    rfl
  map_smul' c f := by
    apply Subtype.ext
    ext A
    rfl

@[simp] theorem finiteEvenFourTorusZ2GaugeInvariantConfigurationCoarsePullbackLinearMap_apply
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    (finiteEvenFourTorusZ2GaugeInvariantConfigurationCoarsePullbackLinearMap H f).1 A =
      f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A) :=
  rfl

/-- Canonical isometric embedding of the actual coarse Gauss-invariant carrier
into the fine Gauss-invariant carrier.  It is not supplied opaquely: it is
obtained by transporting the geometrically constructed orbit-probability
pullback through the exact finite orbit Hilbert identifications. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding
    (H : ℕ) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗᵢ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H) where
  toLinearMap :=
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
      (finiteEvenFourTorusDoubleRefinement H)).inverse.toLinearMap.comp
      ((finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H).toLinearMap.comp
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward.toLinearMap)
  norm_map' := by
    intro f
    calc
      ‖(finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
          (finiteEvenFourTorusDoubleRefinement H)).inverse
          (finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H
            ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f))‖ =
        ‖finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H
            ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)‖ :=
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
          (finiteEvenFourTorusDoubleRefinement H)).inverse.norm_map _
      _ = ‖(finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f‖ :=
        (finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H).norm_map _
      _ = ‖f‖ :=
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward.norm_map _

/-- Exact defining formula for the invariant-carrier embedding. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_apply
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H f =
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement H)).inverse
        (finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H
          ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)) :=
  rfl

/-- The canonical orbit identification commutes exactly with the geometrically
induced cross-volume embedding.  This square is the bridge that allows every
orbit-probability obstruction to be pulled back to the actual Gauss-invariant
configuration Hilbert carrier. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_forward
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement H)).forward
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H f) =
      finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H
        ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f) := by
  change
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement H)).forward
      ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement H)).inverse
        (finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H
          ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f))) = _
  exact
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
      (finiteEvenFourTorusDoubleRefinement H)).forward_inverse _

/-- Conversely, transporting the orbit pullback back to the invariant carrier
is literally the canonical invariant-carrier embedding. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_inverse_pullback
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement H)).inverse
        (finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H
          ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)) =
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H f :=
  rfl

/-- The embedding has exact norm one on every vector. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_norm
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    ‖finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H f‖ = ‖f‖ :=
  (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H).norm_map f

/-- Audit-visible actual carrier embedding package. -/
structure Z2FiniteEvenFourTorusCrossVolumeInvariantCarrierEmbeddingPackage
    (H : ℕ) where
  rawConfigurationPullback :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H)
  rawConfigurationPullback_eq :
    rawConfigurationPullback =
      finiteEvenFourTorusZ2GaugeInvariantConfigurationCoarsePullbackLinearMap H
  normalizedEmbedding :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗᵢ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H)
  normalizedEmbedding_eq :
    normalizedEmbedding = finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H
  orbitSquare : ∀ f,
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement H)).forward
        (normalizedEmbedding f) =
      finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H
        ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)
  normExact : ∀ f, ‖normalizedEmbedding f‖ = ‖f‖

/-- Construct the complete actual carrier-embedding receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeInvariantCarrierEmbeddingPackage
    (H : ℕ) :
    Z2FiniteEvenFourTorusCrossVolumeInvariantCarrierEmbeddingPackage H where
  rawConfigurationPullback :=
    finiteEvenFourTorusZ2GaugeInvariantConfigurationCoarsePullbackLinearMap H
  rawConfigurationPullback_eq := rfl
  normalizedEmbedding := finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding H
  normalizedEmbedding_eq := rfl
  orbitSquare := finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_forward H
  normExact := finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_norm H

end

end MathlibAnalytic
end MGAP4D
