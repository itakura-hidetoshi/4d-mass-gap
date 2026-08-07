import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeCoarseGeometry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Spatial unit translation is a bijection of every finite even-four-torus
spatial slice. -/
theorem finiteEvenFourTorusSpatialVertexStep_bijective
    (H : ℕ)
    (μ : FiniteEvenFourTorusSpatialDirection) :
    Function.Bijective
      (fun v : FiniteEvenFourTorusSpatialVertex H =>
        finiteEvenFourTorusSpatialVertexStep H v μ) := by
  constructor
  · intro v w hvw
    apply Subtype.ext
    have h := congrArg Subtype.val hvw
    change
      v.1 + finiteFourTorusUnitStep (2 * H + 1) μ.1 =
        w.1 + finiteFourTorusUnitStep (2 * H + 1) μ.1 at h
    exact add_right_cancel h
  · intro v
    let w : FiniteEvenFourTorusSpatialVertex H :=
      ⟨v.1 - finiteFourTorusUnitStep (2 * H + 1) μ.1, by
        have h0μ : (0 : Fin 4) ≠ μ.1 := Ne.symm μ.2
        change
          (v.1 - finiteFourTorusUnitStep (2 * H + 1) μ.1) 0 = 0
        simp [finiteFourTorusUnitStep, v.2, h0μ]⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    change
      (v.1 - finiteFourTorusUnitStep (2 * H + 1) μ.1) +
          finiteFourTorusUnitStep (2 * H + 1) μ.1 =
        v.1
    exact sub_add_cancel _ _

/-- Reindex the endpoint residual-gauge factor across a fine spatial step.
The coarse spatial step compatibility proved geometrically is the only input
needed to identify the target fibre. -/
theorem finiteEvenFourTorusZ2ResidualSliceGauge_shiftedFiberProduct
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
      (finiteEvenFourTorusDoubleRefinement H))
    (v : FiniteEvenFourTorusSpatialVertex H)
    (μ : FiniteEvenFourTorusSpatialDirection) :
    (∏ w : FiniteEvenFourTorusSpatialVertex
        (finiteEvenFourTorusDoubleRefinement H),
      if finiteEvenFourTorusSpatialVertexCoarseMap H w = v then
        g (finiteEvenFourTorusSpatialVertexStep
          (finiteEvenFourTorusDoubleRefinement H) w μ)
      else 1) =
      ∏ u : FiniteEvenFourTorusSpatialVertex
          (finiteEvenFourTorusDoubleRefinement H),
        if finiteEvenFourTorusSpatialVertexCoarseMap H u =
            finiteEvenFourTorusSpatialVertexStep H v μ then
          g u
        else 1 := by
  classical
  let fineStep :=
    fun w : FiniteEvenFourTorusSpatialVertex
        (finiteEvenFourTorusDoubleRefinement H) =>
      finiteEvenFourTorusSpatialVertexStep
        (finiteEvenFourTorusDoubleRefinement H) w μ
  let targetFactor :=
    fun u : FiniteEvenFourTorusSpatialVertex
        (finiteEvenFourTorusDoubleRefinement H) =>
      if finiteEvenFourTorusSpatialVertexCoarseMap H u =
          finiteEvenFourTorusSpatialVertexStep H v μ then
        g u
      else 1
  have hFine : Function.Bijective fineStep :=
    finiteEvenFourTorusSpatialVertexStep_bijective
      (finiteEvenFourTorusDoubleRefinement H) μ
  have hCoarseInjective : Function.Injective
      (fun z : FiniteEvenFourTorusSpatialVertex H =>
        finiteEvenFourTorusSpatialVertexStep H z μ) :=
    (finiteEvenFourTorusSpatialVertexStep_bijective H μ).1
  calc
    (∏ w : FiniteEvenFourTorusSpatialVertex
        (finiteEvenFourTorusDoubleRefinement H),
      if finiteEvenFourTorusSpatialVertexCoarseMap H w = v then
        g (fineStep w)
      else 1) =
      ∏ w : FiniteEvenFourTorusSpatialVertex
          (finiteEvenFourTorusDoubleRefinement H),
        targetFactor (fineStep w) := by
      apply Finset.prod_congr rfl
      intro w _hw
      dsimp [targetFactor, fineStep]
      rw [finiteEvenFourTorusSpatialVertexCoarseMap_step H w μ]
      by_cases hwv : finiteEvenFourTorusSpatialVertexCoarseMap H w = v
      · simp [hwv]
      · have hstep :
            finiteEvenFourTorusSpatialVertexStep H
                (finiteEvenFourTorusSpatialVertexCoarseMap H w) μ ≠
              finiteEvenFourTorusSpatialVertexStep H v μ := by
          intro h
          exact hwv (hCoarseInjective h)
        simp [hwv, hstep]
    _ = ∏ u : FiniteEvenFourTorusSpatialVertex
          (finiteEvenFourTorusDoubleRefinement H),
        targetFactor u :=
      hFine.prod_comp targetFactor
    _ = ∏ u : FiniteEvenFourTorusSpatialVertex
          (finiteEvenFourTorusDoubleRefinement H),
        if finiteEvenFourTorusSpatialVertexCoarseMap H u =
            finiteEvenFourTorusSpatialVertexStep H v μ then
          g u
        else 1 := by
      rfl

/-- The corresponding product of inverse endpoint gauge factors is the inverse
of the coarse endpoint gauge fibre product. -/
theorem finiteEvenFourTorusZ2ResidualSliceGauge_shiftedFiberProduct_inv
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
      (finiteEvenFourTorusDoubleRefinement H))
    (v : FiniteEvenFourTorusSpatialVertex H)
    (μ : FiniteEvenFourTorusSpatialDirection) :
    (∏ w : FiniteEvenFourTorusSpatialVertex
        (finiteEvenFourTorusDoubleRefinement H),
      if finiteEvenFourTorusSpatialVertexCoarseMap H w = v then
        (g (finiteEvenFourTorusSpatialVertexStep
          (finiteEvenFourTorusDoubleRefinement H) w μ))⁻¹
      else 1) =
      (∏ u : FiniteEvenFourTorusSpatialVertex
          (finiteEvenFourTorusDoubleRefinement H),
        if finiteEvenFourTorusSpatialVertexCoarseMap H u =
            finiteEvenFourTorusSpatialVertexStep H v μ then
          g u
        else 1)⁻¹ := by
  have hinvSelf : ∀ x : Z2Gauge, x⁻¹ = x := by
    intro x
    fin_cases x <;> native_decide
  simpa only [hinvSelf] using
    (finiteEvenFourTorusZ2ResidualSliceGauge_shiftedFiberProduct
      H g v μ)

/-- The actual doubled-torus configuration coarse graining is exactly
equivariant for the corresponding residual-gauge fibre-product map. -/
theorem finiteEvenFourTorusZ2SliceConfigurationCoarseMap_smul
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
      (finiteEvenFourTorusDoubleRefinement H))
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    finiteEvenFourTorusZ2SliceConfigurationCoarseMap H (g • A) =
      finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap H g •
        finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A := by
  classical
  funext e
  rcases e with ⟨v, μ⟩
  change
    (∏ w : FiniteEvenFourTorusSpatialVertex
        (finiteEvenFourTorusDoubleRefinement H),
      if finiteEvenFourTorusSpatialVertexCoarseMap H w = v then
        g w * A (w, μ) *
          (g (finiteEvenFourTorusSpatialVertexStep
            (finiteEvenFourTorusDoubleRefinement H) w μ))⁻¹
      else 1) =
      (∏ w : FiniteEvenFourTorusSpatialVertex
          (finiteEvenFourTorusDoubleRefinement H),
        if finiteEvenFourTorusSpatialVertexCoarseMap H w = v then
          g w
        else 1) *
      (∏ w : FiniteEvenFourTorusSpatialVertex
          (finiteEvenFourTorusDoubleRefinement H),
        if finiteEvenFourTorusSpatialVertexCoarseMap H w = v then
          A (w, μ)
        else 1) *
      (∏ w : FiniteEvenFourTorusSpatialVertex
          (finiteEvenFourTorusDoubleRefinement H),
        if finiteEvenFourTorusSpatialVertexCoarseMap H w =
            finiteEvenFourTorusSpatialVertexStep H v μ then
          g w
        else 1)⁻¹
  rw [← finiteEvenFourTorusZ2ResidualSliceGauge_shiftedFiberProduct_inv
    H g v μ]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro w _hw
  by_cases hwv : finiteEvenFourTorusSpatialVertexCoarseMap H w = v
  · simp [hwv, mul_assoc]
  · simp [hwv]

/-- The actual doubled-torus configuration coarse hom is equivariant for the
actual residual-gauge coarse hom. -/
theorem finiteEvenFourTorusZ2SliceConfigurationCoarseHom_smul
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
      (finiteEvenFourTorusDoubleRefinement H))
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    finiteEvenFourTorusZ2SliceConfigurationCoarseHom H (g • A) =
      finiteEvenFourTorusZ2ResidualSliceGaugeCoarseHom H g •
        finiteEvenFourTorusZ2SliceConfigurationCoarseHom H A :=
  finiteEvenFourTorusZ2SliceConfigurationCoarseMap_smul H g A

/-- Actual fine-to-coarse map on residual gauge-orbit classes.  Well-definedness
is derived from the geometric gauge equivariance above, not postulated at the
Hilbert-space level. -/
noncomputable def finiteEvenFourTorusZ2GaugeOrbitCoarseMap
    (H : ℕ) :
    FiniteEvenFourTorusZ2ResidualGaugeOrbit
        (finiteEvenFourTorusDoubleRefinement H) →
      FiniteEvenFourTorusZ2ResidualGaugeOrbit H :=
  Quotient.map
    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
    (by
      intro A B hAB
      rcases hAB with ⟨g, hg⟩
      refine ⟨finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap H g, ?_⟩
      calc
        finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap H g •
            finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A =
          finiteEvenFourTorusZ2SliceConfigurationCoarseMap H (g • A) :=
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap_smul
              H g A).symm
        _ = finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B := by
          rw [hg])

@[simp] theorem finiteEvenFourTorusZ2GaugeOrbitCoarseMap_class
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    finiteEvenFourTorusZ2GaugeOrbitCoarseMap H
        (finiteGroupOrbitClass
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
            (finiteEvenFourTorusDoubleRefinement H))
          (FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H)) A) =
      finiteGroupOrbitClass
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A) :=
  rfl

/-- Audit-visible geometric descent receipt from fine configurations through
residual gauge transformations to coarse gauge orbits. -/
structure Z2FiniteEvenFourTorusCrossVolumeGaugeEquivariancePackage
    (H : ℕ) where
  configurationCoarse :
    FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H) →
      FiniteEvenFourTorusZ2SliceConfiguration H
  configurationCoarse_eq :
    configurationCoarse = finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
  gaugeCoarse :
    FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
        (finiteEvenFourTorusDoubleRefinement H) →
      FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H
  gaugeCoarse_eq :
    gaugeCoarse = finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap H
  equivariant :
    ∀ g A,
      configurationCoarse (g • A) = gaugeCoarse g • configurationCoarse A
  orbitCoarse :
    FiniteEvenFourTorusZ2ResidualGaugeOrbit
        (finiteEvenFourTorusDoubleRefinement H) →
      FiniteEvenFourTorusZ2ResidualGaugeOrbit H
  orbitCoarse_eq : orbitCoarse = finiteEvenFourTorusZ2GaugeOrbitCoarseMap H
  orbitClassCompatible :
    ∀ A,
      orbitCoarse
          (finiteGroupOrbitClass
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
              (finiteEvenFourTorusDoubleRefinement H))
            (FiniteEvenFourTorusZ2SliceConfiguration
              (finiteEvenFourTorusDoubleRefinement H)) A) =
        finiteGroupOrbitClass
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H)
          (configurationCoarse A)

/-- Construct the complete gauge-equivariant geometric descent package. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeGaugeEquivariancePackage
    (H : ℕ) :
    Z2FiniteEvenFourTorusCrossVolumeGaugeEquivariancePackage H where
  configurationCoarse := finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
  configurationCoarse_eq := rfl
  gaugeCoarse := finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap H
  gaugeCoarse_eq := rfl
  equivariant := finiteEvenFourTorusZ2SliceConfigurationCoarseMap_smul H
  orbitCoarse := finiteEvenFourTorusZ2GaugeOrbitCoarseMap H
  orbitCoarse_eq := rfl
  orbitClassCompatible := by
    intro A
    rfl

end

end MathlibAnalytic
end MGAP4D
