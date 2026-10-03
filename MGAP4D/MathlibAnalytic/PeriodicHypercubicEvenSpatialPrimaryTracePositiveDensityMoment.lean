import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialPrimaryTracePositiveDensityGram
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalPowerMomentWitness
import Mathlib.Tactic

/-!
# Positive-degree primary-trace moments on one spatial slice

The one-slice positive-density Gram theorem gives linear independence of every
finite initial normalized-trace power family.

As in the earlier boundary argument, shift a nonzero polynomial
`P(r)=sum c_j r^j` to `r P(r)`.  The shifted coefficient vector is still
nonzero, so Gram nondegeneracy forces one power pairing to be nonzero.  Moving
one factor of `r` across the real L2 inner product yields a strictly positive
degree detecting the original polynomial.

No centering hypothesis is needed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

local instance spatialTraceMomentTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance spatialTraceMomentCompactGroup :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance spatialTraceMomentSecondCountableGroup :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance spatialTraceMomentMeasurableGroup :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance spatialTraceMomentBorelGroup :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance spatialTraceMomentSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance spatialTraceMomentHaarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance spatialTraceMomentSpatialHaarFinite (H : ℕ) :
    IsFiniteMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance spatialTraceMomentSpatialHaarOpenPos (H : ℕ) :
    Measure.IsOpenPosMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- A finite normalized-trace polynomial on the canonical primary spatial
plaquette. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial
    (H k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ) :=
  ∑ j : Fin (k + 1), c j •
    (periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H ^
      (j : ℕ))

/-- Under any finite density which is nonzero a.e., every nonzero one-slice
primary normalized-trace polynomial is detected by a strictly positive trace
power degree. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial_withDensity_exists_positiveDegree_moment_ne_zero
    (H : ℕ)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hc : c ≠ 0)
    (w :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ENNReal)
    (hw :
      AEMeasurable w
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
    (hw_ne_zero :
      ∀ᵐ A ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2),
        w A ≠ 0)
    [IsFiniteMeasure
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w)] :
    ∃ i : Fin (k + 2),
      0 < (i : ℕ) + 1 ∧
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w) ℝ
          (periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H ^
            ((i : ℕ) + 1)))
        (ContinuousMap.toLp
          (E := ℝ) 2
          ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).withDensity w) ℝ
          (periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c)) ≠ 0 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let ν := μ.withDensity w
  let r := periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwoContinuous H
  let p := periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial H k c
  let v : Fin (k + 2) → Lp ℝ 2 ν := fun j =>
    ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r ^ (j : ℕ))
  let d : Fin (k + 2) → ℝ := Fin.cases 0 c
  have hdet : (Matrix.gram ℝ v).det ≠ 0 := by
    have hGram :=
      periodicHypercubicEvenPrimarySpatialSliceNormalizedTraceTwo_withDensity_fin_gram_det_ne_zero
        H w hw hw_ne_zero (k + 1)
    simpa [μ, ν, r, v] using hGram
  have hd : d ≠ 0 := by
    intro hd0
    apply hc
    funext j
    have hj := congrFun hd0 j.succ
    simpa [d] using hj
  rcases gram_det_ne_zero_exists_inner_sum_ne_zero v hdet d hd with
    ⟨idx, hidx⟩
  have hshiftContinuous :
      (∑ j : Fin (k + 2), d j • (r ^ (j : ℕ))) = r * p := by
    ext A
    rw [Fin.sum_univ_succ]
    simp only [d, Fin.cases_zero, zero_smul, zero_add, Fin.cases_succ]
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      ContinuousMap.pow_apply, ContinuousMap.mul_apply, smul_eq_mul]
    have hp :
        p A = ∑ j : Fin (k + 1), c j * r A ^ (j : ℕ) := by
      simp [p, r,
        periodicHypercubicEvenPrimarySpatialSliceNormalizedTracePolynomial]
    rw [hp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [Fin.val_succ]
    rw [pow_succ]
    ring
  have hshiftLp :
      (∑ j : Fin (k + 2), d j • v j) =
        ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r * p) := by
    have hmap := congrArg
      (fun f :
          C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ) =>
        ContinuousMap.toLp (E := ℝ) 2 ν ℝ f)
      hshiftContinuous
    simpa [v] using hmap
  have hi' :
      inner ℝ
        (ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r ^ (idx : ℕ)))
        (ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r * p)) ≠ 0 := by
    simpa [v, hshiftLp] using hidx
  have hinnerShift :
      inner ℝ
        (ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r ^ (idx : ℕ)))
        (ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r * p)) =
      inner ℝ
        (ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r ^ ((idx : ℕ) + 1)))
        (ContinuousMap.toLp (E := ℝ) 2 ν ℝ p) := by
    calc
      inner ℝ
          (ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r ^ (idx : ℕ)))
          (ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r * p)) =
        ∫ A, (r * p) A * (r ^ (idx : ℕ)) A ∂ν := by
          simpa using MeasureTheory.ContinuousMap.inner_toLp ν
            (r ^ (idx : ℕ)) (r * p)
      _ = ∫ A, p A * (r ^ ((idx : ℕ) + 1)) A ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with A
        simp only [ContinuousMap.mul_apply, ContinuousMap.pow_apply]
        rw [pow_succ]
        ring
      _ = inner ℝ
          (ContinuousMap.toLp (E := ℝ) 2 ν ℝ (r ^ ((idx : ℕ) + 1)))
          (ContinuousMap.toLp (E := ℝ) 2 ν ℝ p) := by
        symm
        simpa using MeasureTheory.ContinuousMap.inner_toLp ν
          (r ^ ((idx : ℕ) + 1)) p
  refine ⟨idx, Nat.succ_pos _, ?_⟩
  have htarget := hinnerShift ▸ hi'
  simpa [ν, μ, r, p] using htarget

end

end MathlibAnalytic
end MGAP4D
