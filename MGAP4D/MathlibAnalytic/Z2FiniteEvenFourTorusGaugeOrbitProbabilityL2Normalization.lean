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

/-- The literal pushforward-probability map is exactly the canonical
counting-Hilbert orbit coordinate map multiplied by the global square root of
the uniform configuration weight. -/
theorem finiteGroupInvariantToOrbitProbabilityObservable_eq_sqrt_inv_card_smul_coordinates
    (G α : Type)
    [Group G]
    [Fintype α]
    [Nonempty α]
    [MulAction G α]
    (f : finiteGroupInvariantSubmodule G α) :
    finiteGroupInvariantToOrbitProbabilityObservableLinearMap G α f =
      Real.sqrt ((Fintype.card α : ℝ)⁻¹) •
        finiteGroupInvariantToOrbitCoordinatesLinearMap G α f := by
  classical
  ext q
  change
    Real.sqrt
          (finiteGroupOrbitMass G α q *
            (Fintype.card α : ℝ)⁻¹) *
        f.1 (finiteGroupOrbitRepresentative G α q) =
      Real.sqrt ((Fintype.card α : ℝ)⁻¹) *
        (Real.sqrt (finiteGroupOrbitMass G α q) *
          f.1 (finiteGroupOrbitRepresentative G α q))
  rw [Real.sqrt_mul]
  · ring
  · exact le_of_lt (finiteGroupOrbitMass_pos G α q)

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
  rw [
    finiteGroupInvariantToOrbitProbabilityObservable_eq_sqrt_inv_card_smul_coordinates
      G α f,
    norm_smul,
    Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow,
    Real.sq_sqrt
  ]
  · rw [(finiteGroupInvariantToOrbitCoordinatesLinearIsometry G α).norm_map]
  · positivity

/-- Every operator transported through the canonical counting-Hilbert
identification also intertwines the literal same-observable
pushforward-probability map.  The global normalization cancels because the
transported operator is linear. -/
theorem finiteGroupInvariantToOrbitProbabilityObservable_transportOperator_intertwines
    (G α : Type)
    [Group G]
    [Fintype α]
    [Nonempty α]
    [MulAction G α]
    (A : finiteGroupInvariantSubmodule G α →L[ℝ]
      finiteGroupInvariantSubmodule G α)
    (f : finiteGroupInvariantSubmodule G α) :
    (finiteGroupInvariantOrbitProbabilityL2Identification G α).transportOperator A
        (finiteGroupInvariantToOrbitProbabilityObservableLinearMap G α f) =
      finiteGroupInvariantToOrbitProbabilityObservableLinearMap G α (A f) := by
  rw [
    finiteGroupInvariantToOrbitProbabilityObservable_eq_sqrt_inv_card_smul_coordinates
      G α f,
    finiteGroupInvariantToOrbitProbabilityObservable_eq_sqrt_inv_card_smul_coordinates
      G α (A f),
    map_smul
  ]
  exact
    congrArg
      (fun y =>
        Real.sqrt ((Fintype.card α : ℝ)⁻¹) • y)
      (RealHilbertLinearIsometricIdentification.transportOperator_apply_forward
        (finiteGroupInvariantOrbitProbabilityL2Identification G α) A f)

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

/-- Exact scalar relation between the actual same-observable probability map
and the canonical counting-Hilbert isometry. -/
theorem finiteEvenFourTorusZ2GaugeOrbitProbabilityObservable_eq_sqrt_inv_card_smul_identification
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GaugeOrbitProbabilityObservableLinearMap H f =
      Real.sqrt
          ((Fintype.card
            (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹) •
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification H).forward f := by
  change
    finiteGroupInvariantToOrbitProbabilityObservableLinearMap
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H) f =
      Real.sqrt
          ((Fintype.card
            (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹) •
        finiteGroupInvariantToOrbitCoordinatesLinearMap
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H) f
  exact
    finiteGroupInvariantToOrbitProbabilityObservable_eq_sqrt_inv_card_smul_coordinates
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H) f

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

/-- The actual ground-lifted defect intertwines not only the counting-Hilbert
orbit isometry but also the literal same-observable pushforward-probability
map. -/
theorem finiteEvenFourTorusZ2GaugeOrbitProbabilityObservableGroundLiftedDefect_intertwines
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityObservableLinearMap H f) =
      finiteEvenFourTorusZ2GaugeOrbitProbabilityObservableLinearMap H
        (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ hEnergy f) := by
  exact
    finiteGroupInvariantToOrbitProbabilityObservable_transportOperator_intertwines
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (finiteEvenFourTorusZ2GeometricDoobGroundLiftedDefect
        H β energyIdentity energyNontrivial hβ hEnergy)
      f

/-- The exact finite-volume coercivity constant `1/2` therefore holds directly
on the literal same-observable pushforward-probability image. -/
theorem finiteEvenFourTorusZ2GaugeOrbitProbabilityObservableGroundLiftedDefect_half_coercive
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    (1 / 2 : ℝ) *
        ‖finiteEvenFourTorusZ2GaugeOrbitProbabilityObservableLinearMap H f‖ ^ 2 ≤
      inner ℝ
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          (finiteEvenFourTorusZ2GaugeOrbitProbabilityObservableLinearMap H f))
        (finiteEvenFourTorusZ2GaugeOrbitProbabilityObservableLinearMap H f) :=
  finiteEvenFourTorusZ2GaugeOrbitProbabilityGroundLiftedDefect_half_coercive
    energyIdentity energyNontrivial hEnergy β hβ hβCutoff H
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityObservableLinearMap H f)

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
  exactMapRelation :
    ∀ f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
      literalProbabilityMap f =
        Real.sqrt
            ((Fintype.card
              (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹) •
          countingHilbertIdentification.forward f
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
  exactMapRelation :=
    finiteEvenFourTorusZ2GaugeOrbitProbabilityObservable_eq_sqrt_inv_card_smul_identification H
  exactProbabilityNormScaling :=
    finiteEvenFourTorusZ2GaugeOrbitProbabilityObservable_norm_sq H

end

end MathlibAnalytic
end MGAP4D
