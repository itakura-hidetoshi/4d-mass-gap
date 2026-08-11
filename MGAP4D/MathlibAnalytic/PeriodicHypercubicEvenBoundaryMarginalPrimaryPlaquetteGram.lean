import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalProbabilityMeasure
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteWilsonClassFunction
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyPositiveDensityGram
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function MeasureTheory Set
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem boundaryMarginalPrimaryPlaquetteTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance boundaryMarginalPrimaryPlaquetteTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryMarginalPrimaryPlaquetteCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryMarginalPrimaryPlaquetteSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryMarginalPrimaryPlaquetteMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryMarginalPrimaryPlaquetteBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryMarginalPrimaryPlaquetteNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance boundaryMarginalPrimaryPlaquetteHaarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance boundaryMarginalPrimaryPlaquetteBoundaryHaarOpenPos (H : ℕ) :
    Measure.IsOpenPosMeasure (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  unfold periodicHypercubicEvenBoundaryHaarMeasure
  unfold FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure
  infer_instance

/-- The canonical primary spatial plaquette cyclic holonomy is continuous as a
function of the actual reflection-fixed boundary configuration. -/
theorem continuous_periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy_two
    (H : ℕ) :
    Continuous
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2) := by
  let e := periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H
  have hEq :
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2 =
        fun b => (b (e 2))⁻¹ * (b (e 3))⁻¹ * b (e 0) * b (e 1) := by
    funext b
    unfold periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy
    rw [haarFinFourCyclicPlaquetteWord_eq]
  rw [hEq]
  fun_prop

/-- A concrete section of the canonical cyclic holonomy map: put `U` on the
first primary-plaquette fixed edge and the identity on every other boundary
edge. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomySection
    (H : ℕ)
    (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 :=
  fun e =>
    if e = periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H 0
    then U else 1

/-- The concrete boundary section is a right inverse of the cyclic holonomy. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy_section
    (H : ℕ)
    (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomySection H U) =
      U := by
  let e := periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H
  have h10 : e 1 ≠ e 0 := by
    intro h
    have := e.injective h
    norm_num at this
  have h20 : e 2 ≠ e 0 := by
    intro h
    have := e.injective h
    norm_num at this
  have h30 : e 3 ≠ e 0 := by
    intro h
    have := e.injective h
    norm_num at this
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy
  rw [haarFinFourCyclicPlaquetteWord_eq]
  simp [periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomySection,
    e, h10, h20, h30]

/-- Hence the actual primary-plaquette cyclic holonomy reads every `SU(2)`
holonomy value from some boundary configuration. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy_surjective_two
    (H : ℕ) :
    Surjective
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2) := by
  intro U
  exact ⟨
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomySection H U,
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy_section H U⟩

/-- The `SU(2)` Wilson energy of the actual canonical primary spatial
plaquette, regarded as a continuous real function on the full boundary
configuration space. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyTwoBoundaryContinuous
    (H : ℕ) :
    C(PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2, ℝ) :=
  ⟨fun b =>
      specialUnitaryWilsonPlaquetteEnergy 2
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2 b),
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      (continuous_periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy_two H)⟩

/-- The primary-plaquette Wilson energy still has infinite range on the actual
boundary configuration space.  Surjectivity of the canonical cyclic holonomy
transports the already-proved infinite `SU(2)` Wilson-energy range without any
new trigonometric calculation. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyTwoBoundaryContinuous_infiniteRange
    (H : ℕ) :
    (Set.range fun b =>
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyTwoBoundaryContinuous H b).Infinite := by
  apply specialUnitaryWilsonPlaquetteEnergy_two_infiniteRange.mono
  rintro y ⟨U, rfl⟩
  rcases
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy_surjective_two H U with
    ⟨b, hb⟩
  refine ⟨b, ?_⟩
  change specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2 b) =
    specialUnitaryWilsonPlaquetteEnergy 2 U
  rw [hb]

/-- The actual interacting finite-Wilson boundary marginal preserves finite
Gram nondegeneracy of every initial family of canonical primary-plaquette
`SU(2)` Wilson-energy powers.

This is the concrete boundary specialization of the generic positive-density
power theorem from #1646, with all density hypotheses discharged by #1648 and
all finiteness/normalization hypotheses discharged by #1649. -/
theorem periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteWilsonEnergyPower_fin_gram_det_ne_zero
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ) :
    (Matrix.gram ℝ
      (fun j : Fin (k + 1) =>
        ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalPrimaryPlaquetteTwoRankPositive beta hbeta) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyTwoBoundaryContinuous H ^
            (j : ℕ)))).det ≠ 0 := by
  let μ := periodicHypercubicEvenBoundaryHaarMeasure H 2
  let w := periodicHypercubicEvenBoundaryMarginalEffectiveDensity
    H 2 boundaryMarginalPrimaryPlaquetteTwoRankPositive beta hbeta
  haveI : IsFiniteMeasure μ := by
    dsimp [μ, periodicHypercubicEvenBoundaryHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
    infer_instance
  haveI : Measure.IsOpenPosMeasure μ := by
    dsimp [μ]
    infer_instance
  haveI : IsFiniteMeasure (μ.withDensity w) := by
    dsimp [μ, w]
    rw [periodicHypercubicEvenBoundaryHaar_withEffectiveDensity_eq_marginalMeasure]
    infer_instance
  have hGram :=
    continuousMap_infiniteRange_powerFamily_toLp_withDensity_fin_gram_det_ne_zero
      (μ := μ)
      w
      (periodicHypercubicEvenBoundaryMarginalEffectiveDensity_measurable
        H 2 boundaryMarginalPrimaryPlaquetteTwoRankPositive beta hbeta).aemeasurable
      (periodicHypercubicEvenBoundaryMarginalEffectiveDensity_ae_ne_zero
        H 2 boundaryMarginalPrimaryPlaquetteTwoRankPositive beta hbeta)
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyTwoBoundaryContinuous H)
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyTwoBoundaryContinuous_infiniteRange H)
      k
  dsimp [μ, w] at hGram
  rw [periodicHypercubicEvenBoundaryHaar_withEffectiveDensity_eq_marginalMeasure] at hGram
  exact hGram

end

end MathlibAnalytic
end MGAP4D