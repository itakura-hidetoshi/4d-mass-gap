import MGAP4D.MathlibAnalytic.AdjointFiniteDimensionalInvariantSynthesis
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonBoundaryEigenmodeSynthesis

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance wilsonBoundaryFiniteInvariantTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance wilsonBoundaryFiniteInvariantCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance wilsonBoundaryFiniteInvariantSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance wilsonBoundaryFiniteInvariantMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance wilsonBoundaryFiniteInvariantBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance wilsonBoundaryFiniteInvariantSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- A finite-dimensional boundary-Haar sector invariant under the actual
Wilson normal operator is synthesized exactly once the actual Wilson analysis
operator has trivial kernel on that sector.

This replaces individual normal-eigenvector hypotheses by the weaker invariant
finite-sector problem. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeature_exists_synthesis_preimage_of_finiteDimensional_invariant_submodule
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (K : Submodule ℝ
      (Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)))
    [FiniteDimensional ℝ K]
    (hInvariant : ∀ x ∈ K,
      periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H N hN beta hbeta x ∈ K)
    (hKernel : ∀ x ∈ K,
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H N hN beta hbeta x = 0 → x = 0)
    {y : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)}
    (hy : y ∈ K) :
    ∃ u : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N),
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
          H N hN beta hbeta u = y := by
  let A := periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
    H N hN beta hbeta
  have hInvariantA : ∀ x ∈ K, (A† ∘L A) x ∈ K := by
    intro x hx
    simpa [A, periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator,
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator] using
      hInvariant x hx
  have hKernelA : ∀ x ∈ K, A x = 0 → x = 0 := by
    intro x hx hAx
    exact hKernel x hx hAx
  rcases
      continuousLinearMap_adjoint_exists_preimage_of_finiteDimensional_invariant_submodule
        A K hInvariantA hKernelA hy with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  simpa [A, periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator] using hu

/-- A positive quadratic lower bound only on a finite invariant sector is
sufficient for exact Wilson synthesis on that sector.

Unlike the global Lax--Milgram certificate, this does not demand a uniform
lower bound on the full infinite-dimensional boundary-Haar `L²` space. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeature_exists_synthesis_preimage_of_finiteDimensional_invariant_lower_bound
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (K : Submodule ℝ
      (Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)))
    [FiniteDimensional ℝ K]
    (hInvariant : ∀ x ∈ K,
      periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H N hN beta hbeta x ∈ K)
    (c : ℝ) (hc : 0 < c)
    (hLower : ∀ x ∈ K,
      c * ‖x‖ ^ 2 ≤
        ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
            H N hN beta hbeta x‖ ^ 2)
    {y : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)}
    (hy : y ∈ K) :
    ∃ u : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N),
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
          H N hN beta hbeta u = y := by
  apply
    periodicHypercubicEvenWilsonBoundaryGramFeature_exists_synthesis_preimage_of_finiteDimensional_invariant_submodule
      H N hN beta hbeta K hInvariant
  · intro x hx hAx
    have hle : c * ‖x‖ ^ 2 ≤ 0 := by
      simpa [hAx] using hLower x hx
    have hxnorm : ‖x‖ = 0 := by
      by_contra hxne
      have hzeroNe : (0 : ℝ) ≠ ‖x‖ := by
        intro hzero
        exact hxne (Eq.symm hzero)
      have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) hzeroNe
      have hprodpos : 0 < c * ‖x‖ ^ 2 := mul_pos hc (sq_pos_of_pos hxpos)
      exact (not_lt_of_ge hle) hprodpos
    exact norm_eq_zero.mp hxnorm
  · exact hy

/-- SU(2) specialization: once a finite-dimensional invariant sector contains
the theorem-generated primary-plaquette Gram--Schmidt mode and the actual
Wilson analysis operator has trivial kernel on that sector, the mode has an
exact open-half `L²` synthesis witness. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidt_exists_synthesis_preimage_of_finiteDimensional_invariant_submodule
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (K : Submodule ℝ
      (Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2)))
    [FiniteDimensional ℝ K]
    (hInvariant : ∀ x ∈ K,
      periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H 2 (by norm_num) beta hbeta x ∈ K)
    (hKernel : ∀ x ∈ K,
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 (by norm_num) beta hbeta x = 0 → x = 0)
    (k : ℕ)
    (hmode :
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
          H k ∈ K) :
    ∃ u : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2),
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
          H 2 (by norm_num) beta hbeta u =
        periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
          H k := by
  exact
    periodicHypercubicEvenWilsonBoundaryGramFeature_exists_synthesis_preimage_of_finiteDimensional_invariant_submodule
      H 2 (by norm_num) beta hbeta K hInvariant hKernel hmode

end

end MathlibAnalytic
end MGAP4D
