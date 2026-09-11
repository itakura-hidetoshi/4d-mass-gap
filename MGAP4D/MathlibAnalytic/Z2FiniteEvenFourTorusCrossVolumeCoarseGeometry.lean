import MGAP4D.MathlibAnalytic.FiniteStrictProbabilityL2MeasurePreservingPullback
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGaugeOrbitProbabilityL2Normalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Canonical refinement parameter whose even-four-torus side length is
exactly twice the side length at `H`. -/
def finiteEvenFourTorusDoubleRefinement (H : ℕ) : ℕ :=
  2 * H + 1

@[simp] theorem finiteEvenFourTorusDoubleRefinement_side
    (H : ℕ) :
    (2 * finiteEvenFourTorusDoubleRefinement H + 1) + 1 =
      2 * ((2 * H + 1) + 1) := by
  simp [finiteEvenFourTorusDoubleRefinement]
  omega

/-- The coarse periodic side divides the canonical doubled side. -/
theorem finiteEvenFourTorusSide_dvd_doubleRefinement_side
    (H : ℕ) :
    ((2 * H + 1) + 1) ∣
      ((2 * finiteEvenFourTorusDoubleRefinement H + 1) + 1) := by
  use 2
  rw [finiteEvenFourTorusDoubleRefinement_side]
  omega

/-- Canonical fine-to-coarse periodic coordinate homomorphism for the doubled
side. -/
def finiteEvenFourTorusCoordinateCoarseHom
    (H : ℕ) :
    ZMod ((2 * finiteEvenFourTorusDoubleRefinement H + 1) + 1) →+*
      ZMod ((2 * H + 1) + 1) :=
  ZMod.castHom
    (finiteEvenFourTorusSide_dvd_doubleRefinement_side H)
    (ZMod ((2 * H + 1) + 1))

/-- The doubled periodic coordinate projection is surjective. -/
theorem finiteEvenFourTorusCoordinateCoarseHom_surjective
    (H : ℕ) :
    Function.Surjective
      (finiteEvenFourTorusCoordinateCoarseHom H) :=
  ZMod.castHom_surjective
    (finiteEvenFourTorusSide_dvd_doubleRefinement_side H)

/-- Fine spatial vertices project coordinatewise to coarse spatial vertices. -/
def finiteEvenFourTorusSpatialVertexCoarseMap
    (H : ℕ) :
    FiniteEvenFourTorusSpatialVertex
        (finiteEvenFourTorusDoubleRefinement H) →
      FiniteEvenFourTorusSpatialVertex H :=
  fun v =>
    ⟨fun i => finiteEvenFourTorusCoordinateCoarseHom H (v.1 i), by
      change finiteEvenFourTorusCoordinateCoarseHom H (v.1 0) = 0
      rw [v.2]
      exact map_zero _⟩

@[simp] theorem finiteEvenFourTorusSpatialVertexCoarseMap_apply
    (H : ℕ)
    (v : FiniteEvenFourTorusSpatialVertex
      (finiteEvenFourTorusDoubleRefinement H))
    (i : Fin 4) :
    (finiteEvenFourTorusSpatialVertexCoarseMap H v).1 i =
      finiteEvenFourTorusCoordinateCoarseHom H (v.1 i) :=
  rfl

/-- The actual periodic coordinate projection commutes with every spatial unit
step. -/
theorem finiteEvenFourTorusSpatialVertexCoarseMap_step
    (H : ℕ)
    (v : FiniteEvenFourTorusSpatialVertex
      (finiteEvenFourTorusDoubleRefinement H))
    (μ : FiniteEvenFourTorusSpatialDirection) :
    finiteEvenFourTorusSpatialVertexCoarseMap H
        (finiteEvenFourTorusSpatialVertexStep
          (finiteEvenFourTorusDoubleRefinement H) v μ) =
      finiteEvenFourTorusSpatialVertexStep H
        (finiteEvenFourTorusSpatialVertexCoarseMap H v) μ := by
  apply Subtype.ext
  funext i
  change
    finiteEvenFourTorusCoordinateCoarseHom H
        (v.1 i + if i = μ.1 then 1 else 0) =
      finiteEvenFourTorusCoordinateCoarseHom H (v.1 i) +
        (if i = μ.1 then 1 else 0)
  rw [map_add]
  by_cases hi : i = μ.1
  · simp [hi]
  · simp [hi]

/-- The fine-to-coarse map on spatial vertices is surjective. -/
theorem finiteEvenFourTorusSpatialVertexCoarseMap_surjective
    (H : ℕ) :
    Function.Surjective
      (finiteEvenFourTorusSpatialVertexCoarseMap H) := by
  classical
  intro v
  have hcoord := finiteEvenFourTorusCoordinateCoarseHom_surjective H
  choose w hw using fun i : Fin 4 => hcoord (v.1 i)
  let fineVertex :
      FiniteEvenFourTorusVertex
        (finiteEvenFourTorusDoubleRefinement H) :=
    fun i => if i = 0 then 0 else w i
  have htime : fineVertex 0 = 0 := by
    simp [fineVertex]
  refine ⟨⟨fineVertex, htime⟩, ?_⟩
  apply Subtype.ext
  funext i
  by_cases hi : i = 0
  · subst i
    change finiteEvenFourTorusCoordinateCoarseHom H 0 = v.1 0
    rw [map_zero, v.2]
  · change
      finiteEvenFourTorusCoordinateCoarseHom H (if i = 0 then 0 else w i) =
        v.1 i
    simpa [hi] using hw i

/-- Fine spatial links project their base vertex and retain their spatial
direction. -/
def finiteEvenFourTorusSpatialLinkCoarseMap
    (H : ℕ) :
    FiniteEvenFourTorusSpatialLink
        (finiteEvenFourTorusDoubleRefinement H) →
      FiniteEvenFourTorusSpatialLink H :=
  fun e => (finiteEvenFourTorusSpatialVertexCoarseMap H e.1, e.2)

@[simp] theorem finiteEvenFourTorusSpatialLinkCoarseMap_apply
    (H : ℕ)
    (e : FiniteEvenFourTorusSpatialLink
      (finiteEvenFourTorusDoubleRefinement H)) :
    finiteEvenFourTorusSpatialLinkCoarseMap H e =
      (finiteEvenFourTorusSpatialVertexCoarseMap H e.1, e.2) :=
  rfl

/-- The fine-to-coarse spatial-link map is surjective. -/
theorem finiteEvenFourTorusSpatialLinkCoarseMap_surjective
    (H : ℕ) :
    Function.Surjective
      (finiteEvenFourTorusSpatialLinkCoarseMap H) := by
  intro e
  rcases e with ⟨v, μ⟩
  rcases finiteEvenFourTorusSpatialVertexCoarseMap_surjective H v with
    ⟨w, hw⟩
  exact ⟨(w, μ), by simp [finiteEvenFourTorusSpatialLinkCoarseMap, hw]⟩

/-- Coarse `Z₂` spatial-link field obtained by multiplying all fine link
variables whose base vertices lie over the chosen coarse base vertex.  The
spatial direction is kept fixed. -/
noncomputable def finiteEvenFourTorusZ2SliceConfigurationCoarseMap
    (H : ℕ) :
    FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H) →
      FiniteEvenFourTorusZ2SliceConfiguration H := by
  classical
  exact fun A e =>
    ∏ v : FiniteEvenFourTorusSpatialVertex
        (finiteEvenFourTorusDoubleRefinement H),
      if finiteEvenFourTorusSpatialVertexCoarseMap H v = e.1 then
        A (v, e.2)
      else
        1

@[simp] theorem finiteEvenFourTorusZ2SliceConfigurationCoarseMap_one
    (H : ℕ) :
    finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
        (1 : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H)) = 1 := by
  classical
  funext e
  simp [finiteEvenFourTorusZ2SliceConfigurationCoarseMap]

/-- Fiber-product coarse graining is multiplicative on `Z₂` link fields. -/
theorem finiteEvenFourTorusZ2SliceConfigurationCoarseMap_mul
    (H : ℕ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    finiteEvenFourTorusZ2SliceConfigurationCoarseMap H (A * B) =
      finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A *
        finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B := by
  classical
  funext e
  unfold finiteEvenFourTorusZ2SliceConfigurationCoarseMap
  change
    (∏ v : FiniteEvenFourTorusSpatialVertex
        (finiteEvenFourTorusDoubleRefinement H),
      if finiteEvenFourTorusSpatialVertexCoarseMap H v = e.1 then
        A (v, e.2) * B (v, e.2)
      else 1) =
      (∏ v : FiniteEvenFourTorusSpatialVertex
          (finiteEvenFourTorusDoubleRefinement H),
        if finiteEvenFourTorusSpatialVertexCoarseMap H v = e.1 then
          A (v, e.2)
        else 1) *
      (∏ v : FiniteEvenFourTorusSpatialVertex
          (finiteEvenFourTorusDoubleRefinement H),
        if finiteEvenFourTorusSpatialVertexCoarseMap H v = e.1 then
          B (v, e.2)
        else 1)
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _hv
  by_cases hve : finiteEvenFourTorusSpatialVertexCoarseMap H v = e.1
  · simp [hve]
  · simp [hve]

/-- Bundled multiplicative coarse graining of finite `Z₂` spatial-link
configurations. -/
noncomputable def finiteEvenFourTorusZ2SliceConfigurationCoarseHom
    (H : ℕ) :
    FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H) →*
      FiniteEvenFourTorusZ2SliceConfiguration H where
  toFun := finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
  map_one' := finiteEvenFourTorusZ2SliceConfigurationCoarseMap_one H
  map_mul' := finiteEvenFourTorusZ2SliceConfigurationCoarseMap_mul H

/-- Coarse residual gauge field obtained by multiplying all fine gauge values
in the fiber over each coarse spatial vertex. -/
noncomputable def finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap
    (H : ℕ) :
    FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
        (finiteEvenFourTorusDoubleRefinement H) →
      FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H := by
  classical
  exact fun g v =>
    ∏ w : FiniteEvenFourTorusSpatialVertex
        (finiteEvenFourTorusDoubleRefinement H),
      if finiteEvenFourTorusSpatialVertexCoarseMap H w = v then
        g w
      else
        1

@[simp] theorem finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap_one
    (H : ℕ) :
    finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap H
        (1 : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
          (finiteEvenFourTorusDoubleRefinement H)) = 1 := by
  classical
  funext v
  simp [finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap]

/-- Fiber-product coarse graining is multiplicative on residual gauge fields. -/
theorem finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap_mul
    (H : ℕ)
    (g h : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
      (finiteEvenFourTorusDoubleRefinement H)) :
    finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap H (g * h) =
      finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap H g *
        finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap H h := by
  classical
  funext v
  unfold finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap
  change
    (∏ w : FiniteEvenFourTorusSpatialVertex
        (finiteEvenFourTorusDoubleRefinement H),
      if finiteEvenFourTorusSpatialVertexCoarseMap H w = v then
        g w * h w
      else 1) =
      (∏ w : FiniteEvenFourTorusSpatialVertex
          (finiteEvenFourTorusDoubleRefinement H),
        if finiteEvenFourTorusSpatialVertexCoarseMap H w = v then
          g w
        else 1) *
      (∏ w : FiniteEvenFourTorusSpatialVertex
          (finiteEvenFourTorusDoubleRefinement H),
        if finiteEvenFourTorusSpatialVertexCoarseMap H w = v then
          h w
        else 1)
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro w _hw
  by_cases hwv : finiteEvenFourTorusSpatialVertexCoarseMap H w = v
  · simp [hwv]
  · simp [hwv]

/-- Bundled multiplicative coarse graining of residual gauge fields. -/
noncomputable def finiteEvenFourTorusZ2ResidualSliceGaugeCoarseHom
    (H : ℕ) :
    FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
        (finiteEvenFourTorusDoubleRefinement H) →*
      FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H where
  toFun := finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap H
  map_one' := finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap_one H
  map_mul' := finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap_mul H

/-- Audit-visible first actual cross-volume geometry receipt. -/
structure Z2FiniteEvenFourTorusCrossVolumeCoarseGeometryPackage
    (H : ℕ) where
  coordinateHom :
    ZMod ((2 * finiteEvenFourTorusDoubleRefinement H + 1) + 1) →+*
      ZMod ((2 * H + 1) + 1)
  coordinateHom_eq :
    coordinateHom = finiteEvenFourTorusCoordinateCoarseHom H
  coordinateSurjective : Function.Surjective coordinateHom
  vertexMap :
    FiniteEvenFourTorusSpatialVertex
        (finiteEvenFourTorusDoubleRefinement H) →
      FiniteEvenFourTorusSpatialVertex H
  vertexMap_eq : vertexMap = finiteEvenFourTorusSpatialVertexCoarseMap H
  vertexSurjective : Function.Surjective vertexMap
  stepCompatible :
    ∀ v μ,
      vertexMap
          (finiteEvenFourTorusSpatialVertexStep
            (finiteEvenFourTorusDoubleRefinement H) v μ) =
        finiteEvenFourTorusSpatialVertexStep H (vertexMap v) μ
  linkMap :
    FiniteEvenFourTorusSpatialLink
        (finiteEvenFourTorusDoubleRefinement H) →
      FiniteEvenFourTorusSpatialLink H
  linkMap_eq : linkMap = finiteEvenFourTorusSpatialLinkCoarseMap H
  linkSurjective : Function.Surjective linkMap
  configurationHom :
    FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H) →*
      FiniteEvenFourTorusZ2SliceConfiguration H
  configurationHom_eq :
    configurationHom = finiteEvenFourTorusZ2SliceConfigurationCoarseHom H
  gaugeHom :
    FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
        (finiteEvenFourTorusDoubleRefinement H) →*
      FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H
  gaugeHom_eq :
    gaugeHom = finiteEvenFourTorusZ2ResidualSliceGaugeCoarseHom H

/-- Construct the actual doubled-torus coarse geometry package. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeCoarseGeometryPackage
    (H : ℕ) :
    Z2FiniteEvenFourTorusCrossVolumeCoarseGeometryPackage H where
  coordinateHom := finiteEvenFourTorusCoordinateCoarseHom H
  coordinateHom_eq := rfl
  coordinateSurjective :=
    finiteEvenFourTorusCoordinateCoarseHom_surjective H
  vertexMap := finiteEvenFourTorusSpatialVertexCoarseMap H
  vertexMap_eq := rfl
  vertexSurjective :=
    finiteEvenFourTorusSpatialVertexCoarseMap_surjective H
  stepCompatible :=
    finiteEvenFourTorusSpatialVertexCoarseMap_step H
  linkMap := finiteEvenFourTorusSpatialLinkCoarseMap H
  linkMap_eq := rfl
  linkSurjective :=
    finiteEvenFourTorusSpatialLinkCoarseMap_surjective H
  configurationHom := finiteEvenFourTorusZ2SliceConfigurationCoarseHom H
  configurationHom_eq := rfl
  gaugeHom := finiteEvenFourTorusZ2ResidualSliceGaugeCoarseHom H
  gaugeHom_eq := rfl

end

end MathlibAnalytic
end MGAP4D
