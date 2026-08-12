import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalTraceFockFeatureMoment
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators InnerProduct InnerProductSpace ENNReal

noncomputable section

private theorem boundaryPositiveDensityTraceFockRobustnessTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryPositiveDensityTraceFockRobustnessTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryPositiveDensityTraceFockRobustnessCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryPositiveDensityTraceFockRobustnessSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryPositiveDensityTraceFockRobustnessMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryPositiveDensityTraceFockRobustnessBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryPositiveDensityTraceFockRobustnessSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance boundaryPositiveDensityTraceFockRobustnessBoundaryHaarFinite
    (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance boundaryPositiveDensityTraceFockRobustnessBoundaryHaarOpenPos
    (H : ℕ) :
    Measure.IsOpenPosMeasure (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  unfold periodicHypercubicEvenBoundaryHaarMeasure
  unfold FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure
  infer_instance

/-- Positive-degree normalized-trace moments cannot all disappear after an
arbitrary equivalent positive density change of boundary Haar measure.

The key point is that no centeredness assumption is needed for the new
measure.  We apply Gram nondegeneracy to the shifted polynomial `r * P(r)`:
its coefficient vector is `(0,c₀,...,cₖ)`, hence nonzero whenever `c` is
nonzero.  A detected degree `i` for `rP` is exactly degree `i+1 > 0` for `P`.
This is the measure-robust form needed for the actual Wilson analysis, where
the square-root vacuum transport introduces an additional strictly positive
boundary density. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial_withDensity_exists_positiveDegree_moment_ne_zero
    (H : ℕ)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hc : c ≠ 0)
    (w : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 → ℝ≥0∞)
    (hwmeas : AEMeasurable w (periodicHypercubicEvenBoundaryHaarMeasure H 2))
    (hwne : ∀ᵐ b ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2), w b ≠ 0)
    [IsFiniteMeasure
      ((periodicHypercubicEvenBoundaryHaarMeasure H 2).withDensity w)] :
    ∃ i : Fin (k + 2),
      0 < (i : ℕ) + 1 ∧
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          ((periodicHypercubicEvenBoundaryHaarMeasure H 2).withDensity w) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
            ((i : ℕ) + 1)))
        (ContinuousMap.toLp
          (E := ℝ) 2
          ((periodicHypercubicEvenBoundaryHaarMeasure H 2).withDensity w) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c)) ≠ 0 := by
  let μ := periodicHypercubicEvenBoundaryHaarMeasure H 2
  let ν := μ.withDensity w
  let r := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  let v : Fin (k + 2) → Lp ℝ 2 ν := fun j =>
    ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r ^ (j : ℕ))
  let d : Fin (k + 2) → ℝ := Fin.cases 0 c
  have hdet : (Matrix.gram ℝ v).det ≠ 0 := by
    have hGram :=
      continuousMap_infiniteRange_powerFamily_toLp_withDensity_fin_gram_det_ne_zero
        (μ := μ) w hwmeas hwne r
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous_infiniteRange H)
        (k + 1)
    simpa [μ, ν, v] using hGram
  have hd : d ≠ 0 := by
    intro hd0
    apply hc
    funext j
    have hj := congrFun hd0 j.succ
    simpa [d] using hj
  rcases gram_det_ne_zero_exists_inner_sum_ne_zero v hdet d hd with ⟨i, hi⟩
  have hshiftContinuous :
      (∑ j : Fin (k + 2), d j • (r ^ (j : ℕ))) = r * p := by
    ext b
    rw [Fin.sum_univ_succ]
    simp only [d, Fin.cases_zero, zero_smul, zero_add, Fin.cases_succ]
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      ContinuousMap.pow_apply, ContinuousMap.mul_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    simp [p, periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial,
      pow_succ]
    ring
  have hshiftLp :
      (∑ j : Fin (k + 2), d j • v j) =
        ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r * p) := by
    have hmap := congrArg
      (fun f : C(PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2, ℝ) =>
        ContinuousMap.toLp (E := ℝ) 2 ν ℝ f)
      hshiftContinuous
    simpa [v] using hmap
  have hi' :
      inner ℝ
        (ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r ^ (i : ℕ)))
        (ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r * p)) ≠ 0 := by
    simpa [v, hshiftLp] using hi
  have hinnerShift :
      inner ℝ
        (ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r ^ (i : ℕ)))
        (ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r * p)) =
      inner ℝ
        (ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r ^ ((i : ℕ) + 1)))
        (ContinuousMap.toLp (E := ℝ) 2 ν ℝ p) := by
    rw [MeasureTheory.ContinuousMap.inner_toLp,
      MeasureTheory.ContinuousMap.inner_toLp]
    apply integral_congr_ae
    filter_upwards [] with b
    simp only [ContinuousMap.pow_apply, ContinuousMap.mul_apply]
    rw [periodicHypercubicEven_real_inner_eq_mul,
      periodicHypercubicEven_real_inner_eq_mul]
    rw [pow_succ]
    ring
  refine ⟨i, Nat.succ_pos _, ?_⟩
  have htarget := hinnerShift ▸ hi'
  simpa [ν, r, p] using htarget

end

end MathlibAnalytic
end MGAP4D
