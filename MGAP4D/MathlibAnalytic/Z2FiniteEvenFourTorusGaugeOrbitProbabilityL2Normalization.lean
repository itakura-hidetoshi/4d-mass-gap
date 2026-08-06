import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGaugeOrbitProbabilityL2Realization
import Mathlib.Tactic

/-!
This file separates two finite-volume normalizations that share the same
residual-gauge orbit observables: the counting-Hilbert isometry and the literal
pushforward-probability `L²` embedding.  The latter carries the exact global
factor `card(configurations)⁻¹` in squared norm.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- The unscaled quotient observable underlying an invariant finite
configuration wavefunction.  Unlike the canonical counting-Hilbert isometry,
this map preserves the literal observable value on every orbit. -/
noncomputable def finiteGroupInvariantOrbitObservableLinearMap
    (G α : Type)
    [Group G]
    [Fintype α]
    [Nonempty α]
    [MulAction G α] :
    finiteGroupInvariantSubmodule G α →ₗ[ℝ]
      (FiniteGroupOrbitQuotient G α → ℝ) where
  toFun f := fun q =>
    f.1 (finiteGroupOrbitRepresentative G α q)
  map_add' f h := by
    funext q
    rfl
  map_smul' c f := by
    funext q
    rfl

@[simp] theorem finiteGroupInvariantOrbitObservableLinearMap_apply
    (G α : Type)
    [Group G]
    [Fintype α]
    [Nonempty α]
    [MulAction G α]
    (f : finiteGroupInvariantSubmodule G α)
    (q : FiniteGroupOrbitQuotient G α) :
    finiteGroupInvariantOrbitObservableLinearMap G α f q =
      f.1 (finiteGroupOrbitRepresentative G α q) :=
  rfl

/-- Square-root-density coordinates of the literal quotient observable for the
pushforward of uniform configuration probability.  This is the genuine
same-observable probability `L²` map; it differs from the counting-Hilbert
isometry by the global finite-volume normalization. -/
noncomputable def finiteGroupInvariantToOrbitProbabilityObservableLinearMap
    (G α : Type)
    [Group G]
    [Fintype α]
    [Nonempty α]
    [MulAction G α] :
    finiteGroupInvariantSubmodule G α →ₗ[ℝ]
      FiniteProbabilityL2Carrier (FiniteGroupOrbitQuotient G α) :=
  (finiteGroupOrbitProbabilityL2Data G α).observableEmbedLinearMap.comp
    (finiteGroupInvariantOrbitObservableLinearMap G α)

@[simp] theorem finiteGroupInvariantToOrbitProbabilityObservableLinearMap_apply
    (G α : Type)
    [Group G]
    [Fintype α]
    [Nonempty α]
    [MulAction G α]
    (f : finiteGroupInvariantSubmodule G α)
    (q : FiniteGroupOrbitQuotient G α) :
    finiteGroupInvariantToOrbitProbabilityObservableLinearMap G α f q =
      Real.sqrt
          ((finiteGroupOrbitProbabilityL2Data G α).weight q) *
        f.1 (finiteGroupOrbitRepresentative G α q) :=
  rfl

/-- The literal pushforward-probability observable has exactly the uniform
configuration normalization of the ambient counting Hilbert norm. -/
theorem finiteGroupInvariantToOrbitProbabilityObservable_norm_sq
    (G α : Type)
    [Group G]
    [Fintype α]
    [Nonempty α]
    [MulAction G α]
    (f : finiteGroupInvariantSubmodule G α) :
    ‖finiteGroupInvariantToOrbitProbabilityObservableLinearMap G α f‖ ^ 2 =
      (Fintype.card α : ℝ)⁻¹ * ‖f‖ ^ 2 := by
  classical
  rw [(finiteGroupOrbitProbabilityL2Data G α).norm_sq_observableEmbed]
  change
    (∑ q : FiniteGroupOrbitQuotient G α,
      (finiteGroupOrbitMass G α q * (Fintype.card α : ℝ)⁻¹) *
        (f.1 (finiteGroupOrbitRepresentative G α q)) ^ 2) =
      (Fintype.card α : ℝ)⁻¹ * ‖f‖ ^ 2
  have horbit :
      (∑ q : FiniteGroupOrbitQuotient G α,
        finiteGroupOrbitMass G α q *
          (f.1 (finiteGroupOrbitRepresentative G α q)) ^ 2) =
        ‖f‖ ^ 2 := by
    calc
      (∑ q : FiniteGroupOrbitQuotient G α,
        finiteGroupOrbitMass G α q *
          (f.1 (finiteGroupOrbitRepresentative G α q)) ^ 2) =
        inner ℝ
          (finiteGroupInvariantToOrbitCoordinatesLinearMap G α f)
          (finiteGroupInvariantToOrbitCoordinatesLinearMap G α f) := by
            rw [PiLp.inner_apply]
            apply Finset.sum_congr rfl
            intro q _hq
            change
              finiteGroupOrbitMass G α q *
                  (f.1 (finiteGroupOrbitRepresentative G α q)) ^ 2 =
                (Real.sqrt (finiteGroupOrbitMass G α q) *
                    f.1 (finiteGroupOrbitRepresentative G α q)) *
                  (Real.sqrt (finiteGroupOrbitMass G α q) *
                    f.1 (finiteGroupOrbitRepresentative G α q))
            rw [← Real.sq_sqrt
              (le_of_lt (finiteGroupOrbitMass_pos G α q))]
            ring
      _ = inner ℝ f f :=
        finiteGroupInvariantToOrbitCoordinates_inner G α f f
      _ = ‖f‖ ^ 2 := real_inner_self_eq_norm_sq f
  calc
    (∑ q : FiniteGroupOrbitQuotient G α,
      (finiteGroupOrbitMass G α q * (Fintype.card α : ℝ)⁻¹) *
        (f.1 (finiteGroupOrbitRepresentative G α q)) ^ 2) =
      (Fintype.card α : ℝ)⁻¹ *
        ∑ q : FiniteGroupOrbitQuotient G α,
          finiteGroupOrbitMass G α q *
            (f.1 (finiteGroupOrbitRepresentative G α q)) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      ring
    _ = (Fintype.card α : ℝ)⁻¹ * ‖f‖ ^ 2 := by
      rw [horbit]

/-- The actual finite `Z₂` literal orbit-observable probability map. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitProbabilityObservableLinearMap
    (H : ℕ) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H :=
  finiteGroupInvariantToOrbitProbabilityObservableLinearMap
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)

@[simp] theorem finiteEvenFourTorusZ2GaugeOrbitProbabilityObservableLinearMap_apply
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteEvenFourTorusZ2GaugeOrbitProbabilityObservableLinearMap H f q =
      Real.sqrt
          ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data H).weight q) *
        f.1
          (finiteGroupOrbitRepresentative
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H) q) :=
  rfl

/-- Exact finite-volume normalization of the actual same-observable gauge-orbit
probability realization. -/
theorem finiteEvenFourTorusZ2GaugeOrbitProbabilityObservable_norm_sq
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    ‖finiteEvenFourTorusZ2GaugeOrbitProbabilityObservableLinearMap H f‖ ^ 2 =
      (Fintype.card
        (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ * ‖f‖ ^ 2 :=
  finiteGroupInvariantToOrbitProbabilityObservable_norm_sq
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H) f

/-- Audit-visible separation between the literal pushforward-probability map
and the canonically normalized counting-Hilbert isometry. -/
structure Z2FiniteEvenFourTorusGaugeOrbitProbabilityNormalizationPackage
    (H : ℕ) where
  literalProbabilityMap :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H
  literalProbabilityMap_eq :
    literalProbabilityMap =
      finiteEvenFourTorusZ2GaugeOrbitProbabilityObservableLinearMap H
  countingHilbertIdentification :
    RealHilbertLinearIsometricIdentification
      (FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
      (FiniteEvenFourTorusZ2GaugeOrbitProbabilityL2 H)
  countingHilbertIdentification_eq :
    countingHilbertIdentification =
      finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H
  exactProbabilityNormScaling :
    ∀ f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
      ‖literalProbabilityMap f‖ ^ 2 =
        (Fintype.card
          (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ * ‖f‖ ^ 2

/-- Construct the finite `Z₂` gauge-orbit probability normalization receipt. -/
noncomputable def z2FiniteEvenFourTorusGaugeOrbitProbabilityNormalizationPackage
    (H : ℕ) :
    Z2FiniteEvenFourTorusGaugeOrbitProbabilityNormalizationPackage H where
  literalProbabilityMap :=
    finiteEvenFourTorusZ2GaugeOrbitProbabilityObservableLinearMap H
  literalProbabilityMap_eq := rfl
  countingHilbertIdentification :=
    finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H
  countingHilbertIdentification_eq := rfl
  exactProbabilityNormScaling :=
    finiteEvenFourTorusZ2GaugeOrbitProbabilityObservable_norm_sq H

end

end MathlibAnalytic
end MGAP4D