import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalPowerMomentWitness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProduct InnerProductSpace

noncomputable section

private theorem boundaryMarginalTraceTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance boundaryMarginalTraceTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryMarginalTraceCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryMarginalTraceSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryMarginalTraceMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryMarginalTraceBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryMarginalTraceNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance boundaryMarginalTraceHaarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance boundaryMarginalTraceBoundaryHaarOpenPos (H : ℕ) :
    Measure.IsOpenPosMeasure (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  unfold periodicHypercubicEvenBoundaryHaarMeasure
  unfold FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure
  infer_instance

/-- The normalized real trace of the canonical primary spatial plaquette,
realized on the actual boundary configuration space as `1 - E_W`. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous
    (H : ℕ) :
    C(PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2, ℝ) :=
  1 - periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyTwoBoundaryContinuous H

/-- The preceding continuous map is exactly the normalized real trace of the
canonical primary plaquette cyclic holonomy. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous_apply
    (H : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H b =
      normalizedSpecialUnitaryRealTrace 2
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2 b) := by
  change 1 - specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2 b) = _
  rw [specialUnitaryWilsonPlaquetteEnergy_eq]
  ring

/-- The normalized primary-plaquette trace has infinite range on the full
boundary configuration space.  This follows from the already-proved infinite
Wilson-energy range under the affine involution `x ↦ 1 - x`. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous_infiniteRange
    (H : ℕ) :
    (Set.range fun b =>
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H b).Infinite := by
  intro hTraceFinite
  have hEnergyInfinite :=
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyTwoBoundaryContinuous_infiniteRange H
  apply hEnergyInfinite
  apply (hTraceFinite.image fun x : ℝ => 1 - x).subset
  rintro y ⟨b, rfl⟩
  refine ⟨
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H b,
    ⟨b, rfl⟩, ?_⟩
  dsimp [periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous]
  ring

/-- Every finite initial family of normalized-trace powers remains Gram
nondegenerate in the actual interacting finite-Wilson boundary marginal. -/
theorem periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePower_fin_gram_det_ne_zero
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ) :
    (Matrix.gram ℝ
      (fun j : Fin (k + 1) =>
        ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalTraceTwoRankPositive beta hbeta) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
            (j : ℕ)))).det ≠ 0 := by
  let μ := periodicHypercubicEvenBoundaryHaarMeasure H 2
  let w := periodicHypercubicEvenBoundaryMarginalEffectiveDensity
    H 2 boundaryMarginalTraceTwoRankPositive beta hbeta
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
        H 2 boundaryMarginalTraceTwoRankPositive beta hbeta).aemeasurable
      (periodicHypercubicEvenBoundaryMarginalEffectiveDensity_ae_ne_zero
        H 2 boundaryMarginalTraceTwoRankPositive beta hbeta)
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H)
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous_infiniteRange H)
      k
  dsimp [μ, w] at hGram
  simpa only [periodicHypercubicEvenBoundaryHaar_withEffectiveDensity_eq_marginalMeasure]
    using hGram

/-- A centered nonzero normalized-trace polynomial is detected by a strictly
positive trace-power degree in the actual interacting boundary marginal. -/
theorem periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePower_exists_positiveDegree_moment_ne_zero
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) (hc : c ≠ 0)
    (hzero :
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalTraceTwoRankPositive beta hbeta) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
            (0 : ℕ)))
        (∑ j : Fin (k + 1), c j •
          ContinuousMap.toLp
            (E := ℝ) 2
            (periodicHypercubicEvenBoundaryMarginalMeasure
              H 2 boundaryMarginalTraceTwoRankPositive beta hbeta) ℝ
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
              (j : ℕ))) = 0) :
    ∃ i : Fin (k + 1), 0 < (i : ℕ) ∧
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalTraceTwoRankPositive beta hbeta) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
            (i : ℕ)))
        (∑ j : Fin (k + 1), c j •
          ContinuousMap.toLp
            (E := ℝ) 2
            (periodicHypercubicEvenBoundaryMarginalMeasure
              H 2 boundaryMarginalTraceTwoRankPositive beta hbeta) ℝ
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
              (j : ℕ))) ≠ 0 := by
  let v : Fin (k + 1) →
      Lp ℝ 2
        (periodicHypercubicEvenBoundaryMarginalMeasure
          H 2 boundaryMarginalTraceTwoRankPositive beta hbeta) :=
    fun j =>
      ContinuousMap.toLp
        (E := ℝ) 2
        (periodicHypercubicEvenBoundaryMarginalMeasure
          H 2 boundaryMarginalTraceTwoRankPositive beta hbeta) ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
          (j : ℕ))
  have hdet : (Matrix.gram ℝ v).det ≠ 0 := by
    simpa [v] using
      periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePower_fin_gram_det_ne_zero
        H beta hbeta k
  have hzero' : inner ℝ (v 0) (∑ j : Fin (k + 1), c j • v j) = 0 := by
    simpa [v] using hzero
  simpa [v] using
    gram_det_ne_zero_exists_positive_index_inner_sum_ne_zero
      v hdet c hc hzero'

/-- At strictly positive coupling, the detecting positive trace degree also
carries a strictly positive Taylor/Fock coefficient `beta^i / i!`. -/
theorem periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePower_exists_positiveTaylorDegree
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 < beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) (hc : c ≠ 0)
    (hzero :
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalTraceTwoRankPositive beta hbeta.le) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
            (0 : ℕ)))
        (∑ j : Fin (k + 1), c j •
          ContinuousMap.toLp
            (E := ℝ) 2
            (periodicHypercubicEvenBoundaryMarginalMeasure
              H 2 boundaryMarginalTraceTwoRankPositive beta hbeta.le) ℝ
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
              (j : ℕ))) = 0) :
    ∃ i : Fin (k + 1),
      0 < (i : ℕ) ∧
      0 < beta ^ (i : ℕ) / (Nat.factorial (i : ℕ) : ℝ) ∧
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalTraceTwoRankPositive beta hbeta.le) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
            (i : ℕ)))
        (∑ j : Fin (k + 1), c j •
          ContinuousMap.toLp
            (E := ℝ) 2
            (periodicHypercubicEvenBoundaryMarginalMeasure
              H 2 boundaryMarginalTraceTwoRankPositive beta hbeta.le) ℝ
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
              (j : ℕ))) ≠ 0 := by
  rcases
    periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePower_exists_positiveDegree_moment_ne_zero
      H beta hbeta.le k c hc hzero with ⟨i, hi, hmoment⟩
  refine ⟨i, hi, ?_, hmoment⟩
  exact div_pos (pow_pos hbeta _) (by positivity)

end

end MathlibAnalytic
end MGAP4D