import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonBoundaryFiniteInvariantSynthesis

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance su2InitialSpanTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance su2InitialSpanCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance su2InitialSpanSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance su2InitialSpanMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance su2InitialSpanBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance su2InitialSpanNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The finite generating set consisting of the first `k + 1` theorem-generated
SU(2) primary-plaquette Wilson-energy Gram--Schmidt boundary modes. -/
def periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialGeneratingSet
    (H k : ℕ) :
    Set (Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2)) :=
  Set.range fun j : Fin (k + 1) =>
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
      H j.1

/-- The Mathlib-native finite-dimensional span of the first `k + 1`
primary-plaquette Gram--Schmidt boundary modes. -/
def periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan
    (H k : ℕ) :
    Submodule ℝ (Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2)) :=
  Submodule.span ℝ
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialGeneratingSet
      H k)

noncomputable instance
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan_finiteDimensional
    (H k : ℕ) :
    FiniteDimensional ℝ
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan H k) := by
  unfold periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan
  exact FiniteDimensional.span_of_finite ℝ
    (Set.finite_range fun j : Fin (k + 1) =>
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
        H j.1)

/-- Every Gram--Schmidt mode with index `j ≤ k` belongs to the explicit initial
span `K_{H,k}`. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidt_mem_initialSpan_of_le
    (H : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
        H j ∈
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan H k := by
  unfold periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan
  apply Submodule.subset_span
  refine ⟨⟨j, ?_⟩, rfl⟩
  omega

/-- In particular, the terminal mode belongs to its own initial span. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidt_mem_initialSpan
    (H k : ℕ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
        H k ∈
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan H k :=
  periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidt_mem_initialSpan_of_le
    H (le_refl k)

/-- Exact synthesis of the terminal Gram--Schmidt mode from a lower bound on
its *explicit* initial span.

The arbitrary finite-dimensional sector `K` from the preceding layer has now
disappeared.  The remaining finite-Wilson inputs are exactly:

* invariance of `K_{H,k}` under the actual normal operator `A† A`;
* a positive quadratic lower bound for the actual analysis operator on
  `K_{H,k}`.
-/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidt_exists_synthesis_preimage_of_initialSpan_lower_bound
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (hInvariant : ∀ x ∈
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan H k,
      periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H 2 (by norm_num) beta hbeta x ∈
        periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan H k)
    (c : ℝ) (hc : 0 < c)
    (hLower : ∀ x ∈
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan H k,
      c * ‖x‖ ^ 2 ≤
        ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
            H 2 (by norm_num) beta hbeta x‖ ^ 2) :
    ∃ u : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2),
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
          H 2 (by norm_num) beta hbeta u =
        periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
          H k := by
  exact
    periodicHypercubicEvenWilsonBoundaryGramFeature_exists_synthesis_preimage_of_finiteDimensional_invariant_lower_bound
      H 2 (by norm_num) beta hbeta
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan H k)
      hInvariant c hc hLower
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidt_mem_initialSpan H k)

/-- One invariant/lower-bound estimate on `K_{H,k}` synthesizes *all* of the
first `k + 1` theorem-generated Gram--Schmidt modes. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidt_forall_le_exists_synthesis_preimage_of_initialSpan_lower_bound
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (hInvariant : ∀ x ∈
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan H k,
      periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H 2 (by norm_num) beta hbeta x ∈
        periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan H k)
    (c : ℝ) (hc : 0 < c)
    (hLower : ∀ x ∈
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan H k,
      c * ‖x‖ ^ 2 ≤
        ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
            H 2 (by norm_num) beta hbeta x‖ ^ 2) :
    ∀ j ≤ k,
      ∃ u : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2),
        periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
            H 2 (by norm_num) beta hbeta u =
          periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
            H j := by
  intro j hjk
  exact
    periodicHypercubicEvenWilsonBoundaryGramFeature_exists_synthesis_preimage_of_finiteDimensional_invariant_lower_bound
      H 2 (by norm_num) beta hbeta
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialSpan H k)
      hInvariant c hc hLower
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidt_mem_initialSpan_of_le
        H hjk)

end

end MathlibAnalytic
end MGAP4D
