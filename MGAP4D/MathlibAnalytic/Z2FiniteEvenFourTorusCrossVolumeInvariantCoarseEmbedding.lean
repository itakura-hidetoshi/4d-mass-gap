import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeProbabilityCocycle
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGaugeOrbitProbabilityL2Realization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- Canonical coarse-to-fine isometric embedding on the actual Gauss-invariant
configuration Hilbert carriers.  It is not postulated independently: it is the
exact orbit-probability `L²` pullback conjugated by the already-proved
configuration/orbit Hilbert identifications. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry
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
    let Ifine := finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
      (finiteEvenFourTorusDoubleRefinement H)
    let Icoarse := finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H
    let U := finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H
    change ‖Ifine.inverse (U (Icoarse.forward f))‖ = ‖f‖
    calc
      ‖Ifine.inverse (U (Icoarse.forward f))‖ =
          ‖U (Icoarse.forward f)‖ := Ifine.inverse.norm_map _
      _ = ‖Icoarse.forward f‖ := U.norm_map _
      _ = ‖f‖ := Icoarse.forward.norm_map f

@[simp] theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry_apply
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f =
      (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement H)).inverse
        (finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry H
          ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)) :=
  rfl

/-- The invariant-carrier embedding is exactly the orbit `L²` pullback when
viewed through the fine orbit identification. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_forward_eq_orbitPullback
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement H)).forward
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f) =
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

/-- Exact inner-product preservation of the actual invariant coarse embedding. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_inner
    (H : ℕ)
    (f g : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    inner ℝ
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f)
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H g) =
      inner ℝ f g :=
  LinearIsometry.inner_map_map
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H) f g

/-- Direct two-step actual invariant coarse embedding, obtained by conjugating
the exact two-step orbit-probability pullback. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry
    (H : ℕ) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗᵢ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) where
  toLinearMap :=
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))).inverse.toLinearMap.comp
      ((finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2PullbackLinearIsometry H).toLinearMap.comp
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward.toLinearMap)
  norm_map' := by
    intro f
    let Ifine := finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
    let Icoarse := finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H
    let U := finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2PullbackLinearIsometry H
    change ‖Ifine.inverse (U (Icoarse.forward f))‖ = ‖f‖
    calc
      ‖Ifine.inverse (U (Icoarse.forward f))‖ =
          ‖U (Icoarse.forward f)‖ := Ifine.inverse.norm_map _
      _ = ‖Icoarse.forward f‖ := U.norm_map _
      _ = ‖f‖ := Icoarse.forward.norm_map f

/-- The direct two-step invariant embedding is exactly the direct two-step orbit
pullback through the fine identification. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbedding_forward_eq_orbitPullback
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))).forward
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H f) =
      finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2PullbackLinearIsometry H
        ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f) := by
  change
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))).forward
      ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))).inverse
        (finiteEvenFourTorusZ2GaugeOrbitTwoStepCoarseL2PullbackLinearIsometry H
          ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f))) = _
  exact
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))).forward_inverse _

/-- Actual invariant-carrier cocycle: sequential one-step embeddings are exactly
the direct two-step embedding.  This is the configuration-Hilbert counterpart
of the already-proved orbit-probability pullback cocycle. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_twoStep_cocycle
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry
        (finiteEvenFourTorusDoubleRefinement H)
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f) =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H f := by
  let I2 := finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification
    (finiteEvenFourTorusDoubleRefinement
      (finiteEvenFourTorusDoubleRefinement H))
  apply I2.forward.injective
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_forward_eq_orbitPullback]
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_forward_eq_orbitPullback]
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbedding_forward_eq_orbitPullback]
  exact finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry_twoStep_cocycle
    H ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f)

/-- Audit-visible actual coarse-embedding package on invariant configuration
Hilbert carriers. -/
structure Z2GaugeInvariantCrossVolumeCoarseEmbeddingPackage (H : ℕ) where
  oneStep :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗᵢ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H)
  oneStep_eq : oneStep =
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
  twoStep :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗᵢ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
  twoStep_eq : twoStep =
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
  cocycle : ∀ f,
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry
        (finiteEvenFourTorusDoubleRefinement H) (oneStep f) = twoStep f

/-- Construct the complete actual invariant coarse-embedding receipt. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantCrossVolumeCoarseEmbeddingPackage
    (H : ℕ) : Z2GaugeInvariantCrossVolumeCoarseEmbeddingPackage H where
  oneStep := finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
  oneStep_eq := rfl
  twoStep := finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
  twoStep_eq := rfl
  cocycle := finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_twoStep_cocycle H

end

end MathlibAnalytic
end MGAP4D
