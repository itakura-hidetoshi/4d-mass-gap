import MGAP4D.MathlibAnalytic.FiniteRealInnerProbeSeparationLinearIndependent
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeDualProbeAdjoint
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramDeterminant

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance cyclicFockGramSeparationTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFockGramSeparationCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFockGramSeparationSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFockGramSeparationMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFockGramSeparationBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFockGramSeparationNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The actual finite Wilson analysis Gram determinant is nonzero as soon as
variable-degree cyclic Fock probes separate every nontrivial finite linear
combination of the actual analysis images.

Unlike a fixed square dual-probe matrix, the detecting degree and Hilbert dual
vector may depend on the coefficient family.  This is exactly the form exposed
by the positive-degree boundary-marginal Fock witness: once its corresponding
actual Wilson pairing is shown nonzero, Mathlib linear independence closes the
finite determinant without any further matrix computation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_of_cyclicFockProbe_separates
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ)
    (hsep :
      ∀ c : Fin (k + 1) → ℝ, c ≠ 0 →
        ∃ n : ℕ,
          ∃ q : (specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert,
            inner ℝ
                (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
                  H n q)
                (∑ j : Fin (k + 1), c j •
                  periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
                    H beta hbeta k j) ≠ 0) :
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
        H beta hbeta k).det ≠ 0 := by
  apply
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_iff
      H beta hbeta k).2
  apply finite_real_inner_probe_separation_linearIndependent
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
      H beta hbeta k)
  intro c hc
  rcases hsep c hc with ⟨n, q, hq⟩
  exact
    ⟨periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
        H n q,
      hq⟩

/-- Positive-degree specialization of the cyclic-Fock separation criterion.
The degree-zero sector may therefore be excluded explicitly, matching the
centered boundary-marginal witness and the strictly positive Wilson Taylor
coefficients available when `beta > 0`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_of_positiveDegree_cyclicFockProbe_separates
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ)
    (hsep :
      ∀ c : Fin (k + 1) → ℝ, c ≠ 0 →
        ∃ n : ℕ, 0 < n ∧
          ∃ q : (specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert,
            inner ℝ
                (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
                  H n q)
                (∑ j : Fin (k + 1), c j •
                  periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
                    H beta hbeta k j) ≠ 0) :
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
        H beta hbeta k).det ≠ 0 := by
  apply
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_of_cyclicFockProbe_separates
      H beta hbeta k
  intro c hc
  rcases hsep c hc with ⟨n, _hn, q, hq⟩
  exact ⟨n, q, hq⟩

end

end MathlibAnalytic
end MGAP4D