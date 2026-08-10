import MGAP4D.MathlibAnalytic.LaxMilgramFactorizedSurjectivity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryOpenHalfAnalysisOperator
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyHaarL2GramSchmidt

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance wilsonBoundaryLaxMilgramTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance wilsonBoundaryLaxMilgramCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance wilsonBoundaryLaxMilgramSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance wilsonBoundaryLaxMilgramMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance wilsonBoundaryLaxMilgramBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance wilsonBoundaryLaxMilgramSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Coercive Riesz certificate for the actual compact-Wilson boundary Gram
factor `A† A`.

The certificate is deliberately attached to the exact operator already built
from the finite Wilson Gram kernel.  It does not assert coercivity.  Instead it
records the two facts which, if proved by a quantitative finite-Wilson estimate,
are sufficient for Lax--Milgram:

* a bounded bilinear form whose Riesz operator is exactly the actual `A† A`;
* Mathlib `IsCoercive` for that bilinear form.

No unrelated dynamical coercivity estimate is imported into this statement. -/
structure PeriodicHypercubicEvenWilsonBoundarySynthesisLaxMilgramCertificate
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) where
  boundaryBilinear :
    Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →L[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →L[ℝ] ℝ
  riesz_eq_factorized : ∀ f,
    InnerProductSpace.continuousLinearMapOfBilin
        (𝕜 := ℝ) boundaryBilinear f =
      periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
        H N hN beta hbeta f
  coercive : IsCoercive boundaryBilinear

namespace PeriodicHypercubicEvenWilsonBoundarySynthesisLaxMilgramCertificate

variable
    {H N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℝ} {hbeta : 0 ≤ beta}

/-- A coercive Riesz certificate for the actual Wilson `A† A` factor makes the
actual adjoint synthesis `A†` surjective.

This is precisely the generic factorized Lax--Milgram theorem with

`S = A†` and `A = A`.

The factorization is definitionally the already-constructed Wilson boundary
Gram factorized operator. -/
theorem synthesis_surjective
    (C : PeriodicHypercubicEvenWilsonBoundarySynthesisLaxMilgramCertificate
      H N hN beta hbeta) :
    Function.Surjective
      (periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
        H N hN beta hbeta) := by
  apply continuousLinearMap_surjective_of_laxMilgram_factorization
    (periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
      H N hN beta hbeta)
    (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
      H N hN beta hbeta)
    C.boundaryBilinear
  · intro f
    simpa [periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator]
      using C.riesz_eq_factorized f
  · exact C.coercive

/-- Every boundary-Haar `L²` vector therefore has an actual open-half `L²`
preimage under Wilson synthesis. -/
theorem exists_synthesis_preimage
    (C : PeriodicHypercubicEvenWilsonBoundarySynthesisLaxMilgramCertificate
      H N hN beta hbeta)
    (y : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    ∃ u : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N),
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
          H N hN beta hbeta u = y :=
  C.synthesis_surjective y

end PeriodicHypercubicEvenWilsonBoundarySynthesisLaxMilgramCertificate

/-- SU(2) specialization: a coercive certificate for the actual Wilson
boundary `A† A` operator gives an open-half `L²` witness for every theorem-
generated primary-plaquette Wilson-energy Gram--Schmidt boundary mode.

This removes finite-Wilson range existence as an additional mode-by-mode
assumption once the single operator coercivity certificate is available. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidt_exists_synthesis_preimage
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenWilsonBoundarySynthesisLaxMilgramCertificate
      H 2 (by norm_num) beta hbeta)
    (k : ℕ) :
    ∃ u : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2),
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
          H 2 (by norm_num) beta hbeta u =
        periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
          H k := by
  exact C.exists_synthesis_preimage
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
      H k)

end

end MathlibAnalytic
end MGAP4D
