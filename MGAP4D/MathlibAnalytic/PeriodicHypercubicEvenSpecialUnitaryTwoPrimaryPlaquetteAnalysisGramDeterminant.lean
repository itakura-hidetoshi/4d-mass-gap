import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpanSynthesis
import Mathlib.Analysis.InnerProductSpace.GramMatrix

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance su2AnalysisGramTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance su2AnalysisGramCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance su2AnalysisGramSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance su2AnalysisGramMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance su2AnalysisGramBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance su2AnalysisGramNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The first `k + 1` theorem-generated primary-plaquette boundary modes,
indexed by the finite type used by the concrete initial span. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode
    (H k : ℕ) :
    Fin (k + 1) → Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2) :=
  fun j =>
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
      H j.1

/-- The actual finite Wilson analysis images of the first `k + 1` primary-
plaquette Gram--Schmidt boundary modes. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ) :
    Fin (k + 1) → Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2) :=
  fun j =>
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
      H 2 (by norm_num) beta hbeta
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode
        H k j)

/-- The concrete finite Wilson Gram matrix of the actual analysis images.
Its entries are the finitely many inner products `⟪A g_i, A g_j⟫`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.gram ℝ
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
      H beta hbeta k)

/-- The finite actual Wilson analysis Gram matrix is automatically positive
semidefinite by Mathlib's Gram-matrix theorem. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_posSemidef
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ) :
    Matrix.PosSemidef
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
        H beta hbeta k) := by
  exact Matrix.posSemidef_gram ℝ _

/-- The finite determinant is nonzero exactly when the actual Wilson analysis
images of the first `k + 1` modes are linearly independent. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_iff
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ) :
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
        H beta hbeta k).det ≠ 0 ↔
      LinearIndependent ℝ
        (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
          H beta hbeta k) := by
  exact Matrix.det_gram_ne_zero_iff_linearIndependent

/-- Each finite Gram entry is exactly the corresponding matrix coefficient of
the actual Wilson normal operator `A† A` on the explicit primary-plaquette
Gram--Schmidt modes. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_eq_factorized_inner
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (i j : Fin (k + 1)) :
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
        H beta hbeta k i j =
      inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H 2 (by norm_num) beta hbeta
          (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode
            H k i))
        (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode
          H k j) := by
  unfold periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
  rw [Matrix.gram_apply]
  symm
  simpa [periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator,
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage] using
    periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator_inner
      H 2 (by norm_num) beta hbeta
      (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H 2 (by norm_num) beta hbeta
        (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode
          H k i))
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode
        H k j)

/-- Invariance of the explicit initial span under the actual normal operator is
already equivalent to checking the finitely many generators.  No arbitrary
vector in the span needs to be treated separately. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan_invariant_iff_generators
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ) :
    (∀ x ∈
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan H k,
      periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H 2 (by norm_num) beta hbeta x ∈
        periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan H k) ↔
      (∀ j : Fin (k + 1),
        periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
            H 2 (by norm_num) beta hbeta
            (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode
              H k j) ∈
          periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan H k) := by
  constructor
  · intro h j
    exact h _
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidt_mem_initialSpan_of_le
        H (Nat.le_of_lt_succ j.isLt))
  · intro hgen x hx
    change x ∈ Submodule.span ℝ
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialGeneratingSet
        H k) at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨j, rfl⟩
        exact hgen j
    | zero =>
        simpa using
          (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan
            H k).zero_mem
    | add u v _hu _hv huImage hvImage =>
        simpa using
          (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan
            H k).add_mem huImage hvImage
    | smul c u _hu huImage =>
        simpa using
          (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan
            H k).smul_mem c huImage

/-- Nonvanishing of the finite actual Wilson analysis Gram determinant implies
that the actual analysis operator has trivial kernel on the explicit initial
primary-plaquette span. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysis_kernel_trivial_on_initialSpan_of_gram_det_ne_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (hdet :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
        H beta hbeta k).det ≠ 0) :
    ∀ x ∈
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan H k,
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 (by norm_num) beta hbeta x = 0 → x = 0 := by
  let A := periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
    H 2 (by norm_num) beta hbeta
  let g := periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode H k
  have hLI : LinearIndependent ℝ (fun j : Fin (k + 1) => A (g j)) := by
    simpa [A, g,
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage] using
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_iff
        H beta hbeta k).mp hdet
  have hdisj :
      Disjoint (Submodule.span ℝ (Set.range g)) (LinearMap.ker A.toLinearMap) := by
    apply Submodule.range_ker_disjoint (v := g) (f := A.toLinearMap)
    simpa [Function.comp_def] using hLI
  intro x hx hAx
  have hxSpan : x ∈ Submodule.span ℝ (Set.range g) := by
    simpa [g,
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan,
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialGeneratingSet]
      using hx
  have hxKer : x ∈ LinearMap.ker A.toLinearMap := by
    change A x = 0
    exact hAx
  exact Submodule.disjoint_def.mp hdisj x hxSpan hxKer

/-- The realization frontier is now finite and explicit: generator-level
no-leakage of `A† A` together with nonzero determinant of the actual finite
analysis Gram matrix synthesizes all first `k + 1` primary-plaquette modes. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidt_forall_le_exists_synthesis_preimage_of_generators_invariant_gram_det_ne_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (hGenerators : ∀ j : Fin (k + 1),
      periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H 2 (by norm_num) beta hbeta
          (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode
            H k j) ∈
        periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan H k)
    (hdet :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
        H beta hbeta k).det ≠ 0) :
    ∀ j ≤ k,
      ∃ u : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2),
        periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
            H 2 (by norm_num) beta hbeta u =
          periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
            H j := by
  have hInvariant :=
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan_invariant_iff_generators
      H beta hbeta k).mpr hGenerators
  have hKernel :=
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysis_kernel_trivial_on_initialSpan_of_gram_det_ne_zero
      H beta hbeta k hdet
  intro j hjk
  exact
    periodicHypercubicEvenWilsonBoundaryGramFeature_exists_synthesis_preimage_of_finiteDimensional_invariant_submodule
      H 2 (by norm_num) beta hbeta
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan H k)
      hInvariant hKernel
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidt_mem_initialSpan_of_le
        H hjk)

end

end MathlibAnalytic
end MGAP4D
