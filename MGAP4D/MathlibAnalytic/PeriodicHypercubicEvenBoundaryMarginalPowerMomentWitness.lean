import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalPrimaryPlaquetteGram
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace Matrix

noncomputable section

universe u

/-- A nondegenerate finite Gram matrix detects every nonzero coefficient vector
in at least one row.

Equivalently, if `z = ∑ j, c j • v j` is a nontrivial finite combination of a
Gram-nondegenerate family, then some generating vector has nonzero inner
product with `z`.  This is the finite moment witness needed by the subsequent
Fock-degree strictness argument. -/
theorem gram_det_ne_zero_exists_inner_sum_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type u}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v : ι → V)
    (hdet : (Matrix.gram ℝ v).det ≠ 0)
    (c : ι → ℝ) (hc : c ≠ 0) :
    ∃ i : ι, inner ℝ (v i) (∑ j : ι, c j • v j) ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  have hmul : (Matrix.gram ℝ v) *ᵥ c = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.gram_apply]
    calc
      (∑ j : ι, inner ℝ (v i) (v j) * c j) =
          inner ℝ (v i) (∑ j : ι, c j • v j) := by
        simp only [inner_sum, real_inner_smul_right]
        congr 1
        funext j
        ring
      _ = 0 := hnone i
  have hdetZero : (Matrix.gram ℝ v).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hc, hmul⟩
  exact hdet hdetZero

/-- If the degree-zero row is known to vanish, Gram nondegeneracy detects a
strictly positive degree.  This is the exact finite linear-algebra statement
needed to ensure that a centered nonzero polynomial is seen by a positive
Fock/Taylor degree rather than only by the constant feature. -/
theorem gram_det_ne_zero_exists_positive_index_inner_sum_ne_zero
    {k : ℕ}
    {V : Type u}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v : Fin (k + 1) → V)
    (hdet : (Matrix.gram ℝ v).det ≠ 0)
    (c : Fin (k + 1) → ℝ) (hc : c ≠ 0)
    (hzero : inner ℝ (v 0) (∑ j : Fin (k + 1), c j • v j) = 0) :
    ∃ i : Fin (k + 1), 0 < (i : ℕ) ∧
      inner ℝ (v i) (∑ j : Fin (k + 1), c j • v j) ≠ 0 := by
  rcases gram_det_ne_zero_exists_inner_sum_ne_zero v hdet c hc with ⟨i, hi⟩
  refine ⟨i, ?_, hi⟩
  have hine : i ≠ 0 := by
    intro h
    subst i
    exact hi hzero
  omega

private theorem boundaryMarginalMomentTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance boundaryMarginalMomentTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryMarginalMomentCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryMarginalMomentSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryMarginalMomentMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryMarginalMomentBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryMarginalMomentNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Every nonzero finite polynomial combination of the canonical primary
spatial `SU(2)` Wilson-energy powers in the actual interacting boundary
marginal has a nonzero finite power moment.

The witness degree is bounded by the polynomial degree because the theorem is
extracted directly from the `(k+1) × (k+1)` Gram determinant proved in #1650. -/
theorem periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteWilsonEnergyPower_exists_moment_ne_zero
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) (hc : c ≠ 0) :
    ∃ i : Fin (k + 1),
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalMomentTwoRankPositive beta hbeta) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyTwoBoundaryContinuous H ^
            (i : ℕ)))
        (∑ j : Fin (k + 1), c j •
          ContinuousMap.toLp
            (E := ℝ) 2
            (periodicHypercubicEvenBoundaryMarginalMeasure
              H 2 boundaryMarginalMomentTwoRankPositive beta hbeta) ℝ
            (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyTwoBoundaryContinuous H ^
              (j : ℕ))) ≠ 0 := by
  let v : Fin (k + 1) →
      Lp ℝ 2
        (periodicHypercubicEvenBoundaryMarginalMeasure
          H 2 boundaryMarginalMomentTwoRankPositive beta hbeta) :=
    fun j =>
      ContinuousMap.toLp
        (E := ℝ) 2
        (periodicHypercubicEvenBoundaryMarginalMeasure
          H 2 boundaryMarginalMomentTwoRankPositive beta hbeta) ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyTwoBoundaryContinuous H ^
          (j : ℕ))
  have hdet : (Matrix.gram ℝ v).det ≠ 0 := by
    simpa [v] using
      periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteWilsonEnergyPower_fin_gram_det_ne_zero
        H beta hbeta k
  simpa [v] using gram_det_ne_zero_exists_inner_sum_ne_zero v hdet c hc

/-- Centered version: if the degree-zero boundary-marginal moment vanishes,
then a nonzero primary-plaquette polynomial is detected by some strictly
positive power degree `1 ≤ i ≤ k`.  This is the finite witness required before
inserting the strictly positive Taylor coefficient `beta^i / i!` for
`beta > 0`. -/
theorem periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteWilsonEnergyPower_exists_positiveDegree_moment_ne_zero
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) (hc : c ≠ 0)
    (hzero :
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalMomentTwoRankPositive beta hbeta) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyTwoBoundaryContinuous H ^
            (0 : ℕ)))
        (∑ j : Fin (k + 1), c j •
          ContinuousMap.toLp
            (E := ℝ) 2
            (periodicHypercubicEvenBoundaryMarginalMeasure
              H 2 boundaryMarginalMomentTwoRankPositive beta hbeta) ℝ
            (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyTwoBoundaryContinuous H ^
              (j : ℕ))) = 0) :
    ∃ i : Fin (k + 1), 0 < (i : ℕ) ∧
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalMomentTwoRankPositive beta hbeta) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyTwoBoundaryContinuous H ^
            (i : ℕ)))
        (∑ j : Fin (k + 1), c j •
          ContinuousMap.toLp
            (E := ℝ) 2
            (periodicHypercubicEvenBoundaryMarginalMeasure
              H 2 boundaryMarginalMomentTwoRankPositive beta hbeta) ℝ
            (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyTwoBoundaryContinuous H ^
              (j : ℕ))) ≠ 0 := by
  let v : Fin (k + 1) →
      Lp ℝ 2
        (periodicHypercubicEvenBoundaryMarginalMeasure
          H 2 boundaryMarginalMomentTwoRankPositive beta hbeta) :=
    fun j =>
      ContinuousMap.toLp
        (E := ℝ) 2
        (periodicHypercubicEvenBoundaryMarginalMeasure
          H 2 boundaryMarginalMomentTwoRankPositive beta hbeta) ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyTwoBoundaryContinuous H ^
          (j : ℕ))
  have hdet : (Matrix.gram ℝ v).det ≠ 0 := by
    simpa [v] using
      periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteWilsonEnergyPower_fin_gram_det_ne_zero
        H beta hbeta k
  have hzero' : inner ℝ (v 0) (∑ j : Fin (k + 1), c j • v j) = 0 := by
    simpa [v] using hzero
  simpa [v] using
    gram_det_ne_zero_exists_positive_index_inner_sum_ne_zero
      v hdet c hc hzero'

end

end MathlibAnalytic
end MGAP4D