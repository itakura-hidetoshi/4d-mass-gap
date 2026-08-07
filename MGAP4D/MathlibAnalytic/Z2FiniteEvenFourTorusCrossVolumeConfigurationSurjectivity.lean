import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeGaugeEquivariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A chosen fine spatial vertex above each coarse spatial vertex. -/
noncomputable def finiteEvenFourTorusSpatialVertexCoarseSection
    (H : ℕ)
    (v : FiniteEvenFourTorusSpatialVertex H) :
    FiniteEvenFourTorusSpatialVertex
      (finiteEvenFourTorusDoubleRefinement H) :=
  Classical.choose
    (finiteEvenFourTorusSpatialVertexCoarseMap_surjective H v)

@[simp] theorem finiteEvenFourTorusSpatialVertexCoarseMap_section
    (H : ℕ)
    (v : FiniteEvenFourTorusSpatialVertex H) :
    finiteEvenFourTorusSpatialVertexCoarseMap H
        (finiteEvenFourTorusSpatialVertexCoarseSection H v) = v :=
  Classical.choose_spec
    (finiteEvenFourTorusSpatialVertexCoarseMap_surjective H v)

/-- Lift a coarse `Z₂` configuration by placing each coarse link value on the
single chosen fine base vertex above its coarse base vertex and setting all
other fine links to the identity. -/
noncomputable def finiteEvenFourTorusZ2SliceConfigurationCoarseSection
    (H : ℕ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H) := by
  classical
  exact fun e =>
    if e.1 =
        finiteEvenFourTorusSpatialVertexCoarseSection H
          (finiteEvenFourTorusSpatialVertexCoarseMap H e.1) then
      B (finiteEvenFourTorusSpatialVertexCoarseMap H e.1, e.2)
    else
      1

/-- The geometric coarse configuration map applied to the chosen section is
exactly the original coarse configuration. -/
theorem finiteEvenFourTorusZ2SliceConfigurationCoarseMap_section
    (H : ℕ)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
        (finiteEvenFourTorusZ2SliceConfigurationCoarseSection H B) = B := by
  classical
  funext e
  rcases e with ⟨v, μ⟩
  unfold finiteEvenFourTorusZ2SliceConfigurationCoarseMap
  let s := finiteEvenFourTorusSpatialVertexCoarseSection H v
  have hs : finiteEvenFourTorusSpatialVertexCoarseMap H s = v :=
    finiteEvenFourTorusSpatialVertexCoarseMap_section H v
  change
    (∏ w : FiniteEvenFourTorusSpatialVertex
        (finiteEvenFourTorusDoubleRefinement H),
      if finiteEvenFourTorusSpatialVertexCoarseMap H w = v then
        finiteEvenFourTorusZ2SliceConfigurationCoarseSection H B (w, μ)
      else 1) = B (v, μ)
  rw [Fintype.prod_eq_single s]
  · change
      (if finiteEvenFourTorusSpatialVertexCoarseMap H s = v then
        finiteEvenFourTorusZ2SliceConfigurationCoarseSection H B (s, μ)
      else 1) = B (v, μ)
    rw [if_pos hs]
    unfold finiteEvenFourTorusZ2SliceConfigurationCoarseSection
    have hsSelected :
        s = finiteEvenFourTorusSpatialVertexCoarseSection H
          (finiteEvenFourTorusSpatialVertexCoarseMap H s) := by
      rw [hs]
      rfl
    rw [if_pos hsSelected, hs]
  · intro w hws
    by_cases hwv : finiteEvenFourTorusSpatialVertexCoarseMap H w = v
    · rw [if_pos hwv]
      unfold finiteEvenFourTorusZ2SliceConfigurationCoarseSection
      have hnotSelected :
          w ≠ finiteEvenFourTorusSpatialVertexCoarseSection H
            (finiteEvenFourTorusSpatialVertexCoarseMap H w) := by
        rw [hwv]
        simpa [s] using hws
      rw [if_neg hnotSelected]
    · rw [if_neg hwv]

/-- The bundled doubled-torus coarse configuration hom is surjective. -/
theorem finiteEvenFourTorusZ2SliceConfigurationCoarseHom_surjective
    (H : ℕ) :
    Function.Surjective
      (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H) := by
  intro B
  refine ⟨finiteEvenFourTorusZ2SliceConfigurationCoarseSection H B, ?_⟩
  exact finiteEvenFourTorusZ2SliceConfigurationCoarseMap_section H B

/-- A matching chosen section for coarse residual gauge fields. -/
noncomputable def finiteEvenFourTorusZ2ResidualSliceGaugeCoarseSection
    (H : ℕ)
    (h : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) :
    FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
      (finiteEvenFourTorusDoubleRefinement H) := by
  classical
  exact fun w =>
    if w =
        finiteEvenFourTorusSpatialVertexCoarseSection H
          (finiteEvenFourTorusSpatialVertexCoarseMap H w) then
      h (finiteEvenFourTorusSpatialVertexCoarseMap H w)
    else
      1

/-- The residual-gauge fibre-product coarse map also has an explicit right
inverse. -/
theorem finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap_section
    (H : ℕ)
    (h : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) :
    finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap H
        (finiteEvenFourTorusZ2ResidualSliceGaugeCoarseSection H h) = h := by
  classical
  funext v
  unfold finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap
  let s := finiteEvenFourTorusSpatialVertexCoarseSection H v
  have hs : finiteEvenFourTorusSpatialVertexCoarseMap H s = v :=
    finiteEvenFourTorusSpatialVertexCoarseMap_section H v
  rw [Fintype.prod_eq_single s]
  · change
      (if finiteEvenFourTorusSpatialVertexCoarseMap H s = v then
        finiteEvenFourTorusZ2ResidualSliceGaugeCoarseSection H h s
      else 1) = h v
    rw [if_pos hs]
    unfold finiteEvenFourTorusZ2ResidualSliceGaugeCoarseSection
    have hsSelected :
        s = finiteEvenFourTorusSpatialVertexCoarseSection H
          (finiteEvenFourTorusSpatialVertexCoarseMap H s) := by
      rw [hs]
      rfl
    rw [if_pos hsSelected, hs]
  · intro w hws
    by_cases hwv : finiteEvenFourTorusSpatialVertexCoarseMap H w = v
    · rw [if_pos hwv]
      unfold finiteEvenFourTorusZ2ResidualSliceGaugeCoarseSection
      have hnotSelected :
          w ≠ finiteEvenFourTorusSpatialVertexCoarseSection H
            (finiteEvenFourTorusSpatialVertexCoarseMap H w) := by
        rw [hwv]
        simpa [s] using hws
      rw [if_neg hnotSelected]
    · rw [if_neg hwv]

/-- The bundled residual-gauge coarse hom is surjective as well. -/
theorem finiteEvenFourTorusZ2ResidualSliceGaugeCoarseHom_surjective
    (H : ℕ) :
    Function.Surjective
      (finiteEvenFourTorusZ2ResidualSliceGaugeCoarseHom H) := by
  intro h
  refine ⟨finiteEvenFourTorusZ2ResidualSliceGaugeCoarseSection H h, ?_⟩
  exact finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap_section H h

/-- Audit-visible right-inverse and surjectivity receipt for the actual fine to
coarse `Z₂` configuration and residual-gauge maps. -/
structure Z2FiniteEvenFourTorusCrossVolumeConfigurationSurjectivityPackage
    (H : ℕ) where
  configurationSection :
    FiniteEvenFourTorusZ2SliceConfiguration H →
      FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H)
  configurationSection_eq :
    configurationSection =
      finiteEvenFourTorusZ2SliceConfigurationCoarseSection H
  configurationRightInverse :
    ∀ B,
      finiteEvenFourTorusZ2SliceConfigurationCoarseHom H
          (configurationSection B) = B
  configurationSurjective :
    Function.Surjective
      (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H)
  gaugeSection :
    FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H →
      FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
        (finiteEvenFourTorusDoubleRefinement H)
  gaugeSection_eq :
    gaugeSection = finiteEvenFourTorusZ2ResidualSliceGaugeCoarseSection H
  gaugeRightInverse :
    ∀ h,
      finiteEvenFourTorusZ2ResidualSliceGaugeCoarseHom H
          (gaugeSection h) = h
  gaugeSurjective :
    Function.Surjective
      (finiteEvenFourTorusZ2ResidualSliceGaugeCoarseHom H)

/-- Construct the explicit actual cross-volume surjectivity package. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeConfigurationSurjectivityPackage
    (H : ℕ) :
    Z2FiniteEvenFourTorusCrossVolumeConfigurationSurjectivityPackage H where
  configurationSection :=
    finiteEvenFourTorusZ2SliceConfigurationCoarseSection H
  configurationSection_eq := rfl
  configurationRightInverse :=
    finiteEvenFourTorusZ2SliceConfigurationCoarseMap_section H
  configurationSurjective :=
    finiteEvenFourTorusZ2SliceConfigurationCoarseHom_surjective H
  gaugeSection := finiteEvenFourTorusZ2ResidualSliceGaugeCoarseSection H
  gaugeSection_eq := rfl
  gaugeRightInverse :=
    finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap_section H
  gaugeSurjective :=
    finiteEvenFourTorusZ2ResidualSliceGaugeCoarseHom_surjective H

end

end MathlibAnalytic
end MGAP4D
