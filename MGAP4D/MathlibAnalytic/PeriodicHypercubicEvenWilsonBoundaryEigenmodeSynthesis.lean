import MGAP4D.MathlibAnalytic.AdjointEigenvectorSynthesis
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonBoundarySynthesisLaxMilgram

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance wilsonBoundaryEigenmodeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance wilsonBoundaryEigenmodeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance wilsonBoundaryEigenmodeSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance wilsonBoundaryEigenmodeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance wilsonBoundaryEigenmodeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance wilsonBoundaryEigenmodeSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- A nonzero normal eigenmode of the actual Wilson analysis operator has an
exact open-half `L²` synthesis preimage.

This is deliberately modewise.  It does not require the adjoint synthesis to
be surjective on the whole boundary-Haar `L²` space. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeature_exists_synthesis_preimage_of_factorized_eigenvector
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (y : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N))
    (lambda : ℝ) (hlambda : lambda ≠ 0)
    (hy :
      periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H N hN beta hbeta y = lambda • y) :
    ∃ u : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N),
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
          H N hN beta hbeta u = y := by
  let A := periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
    H N hN beta hbeta
  have hyA : A† (A y) = lambda • y := by
    simpa [A, periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator,
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator] using hy
  rcases
      continuousLinearMap_adjoint_exists_preimage_of_nonzero_normal_eigenvector
        A y lambda hlambda hyA with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  simpa [A, periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator] using hu

/-- Solving the actual Wilson normal equation `A† A v = y` is already enough
to synthesize `y` exactly, with the canonical witness `A v`. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeature_exists_synthesis_preimage_of_normal_equation
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (y v : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N))
    (hv :
      periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H N hN beta hbeta v = y) :
    ∃ u : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N),
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
          H N hN beta hbeta u = y := by
  refine ⟨periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
    H N hN beta hbeta v, ?_⟩
  simpa [periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator] using hv

/-- The global Lax--Milgram certificate from the preceding layer contains a
uniform quadratic lower bound for the *entire* boundary-Haar `L²` analysis
operator.

This theorem makes the strength of that conditional route explicit.  The
modewise eigenvector/normal-equation route above does not assume this global
bound. -/
theorem PeriodicHypercubicEvenWilsonBoundarySynthesisLaxMilgramCertificate.analysis_uniform_quadratic_lower_bound
    {H N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℝ} {hbeta : 0 ≤ beta}
    (C : PeriodicHypercubicEvenWilsonBoundarySynthesisLaxMilgramCertificate
      H N hN beta hbeta) :
    ∃ c : ℝ, 0 < c ∧
      ∀ f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N),
        c * ‖f‖ * ‖f‖ ≤
          ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
              H N hN beta hbeta f‖ ^ 2 := by
  rcases C.coercive with ⟨c, hc, hcoercive⟩
  refine ⟨c, hc, ?_⟩
  intro f
  calc
    c * ‖f‖ * ‖f‖ ≤ C.boundaryBilinear f f := hcoercive f
    _ = inner ℝ
        (InnerProductSpace.continuousLinearMapOfBilin
          (𝕜 := ℝ) C.boundaryBilinear f) f := by
      symm
      exact InnerProductSpace.continuousLinearMapOfBilin_apply
        C.boundaryBilinear f f
    _ = inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H N hN beta hbeta f) f := by
      rw [C.riesz_eq_factorized f]
    _ = ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H N hN beta hbeta f‖ ^ 2 :=
      periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner_self
        H N hN beta hbeta f

/-- SU(2) specialization for the theorem-generated primary-plaquette
Wilson-energy Gram--Schmidt modes.  A nonzero normal eigenvalue is sufficient
for an exact finite-Wilson synthesis witness for that mode. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidt_exists_synthesis_preimage_of_factorized_eigenvector
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ) (lambda : ℝ) (hlambda : lambda ≠ 0)
    (hmode :
      periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H 2 (by norm_num) beta hbeta
          (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
            H k) =
        lambda •
          periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
            H k) :
    ∃ u : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2),
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
          H 2 (by norm_num) beta hbeta u =
        periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
          H k := by
  exact
    periodicHypercubicEvenWilsonBoundaryGramFeature_exists_synthesis_preimage_of_factorized_eigenvector
      H 2 (by norm_num) beta hbeta
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
        H k)
      lambda hlambda hmode

end

end MathlibAnalytic
end MGAP4D
