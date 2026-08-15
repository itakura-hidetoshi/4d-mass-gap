import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryActualPlaquetteAlgebraGramClosure
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryRawActualAnalysisBochnerContinuousMap
import Mathlib.Analysis.Convex.Integral
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology

noncomputable section

private theorem boundaryRawActualAnalysisPlaquetteClosureTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance boundaryRawActualAnalysisPlaquetteClosureNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryRawActualAnalysisPlaquetteClosureTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryRawActualAnalysisPlaquetteClosureCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryRawActualAnalysisPlaquetteClosureSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryRawActualAnalysisPlaquetteClosureMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryRawActualAnalysisPlaquetteClosureBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance boundaryRawActualAnalysisPlaquetteClosureSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance boundaryRawActualAnalysisPlaquetteClosureBoundaryHaarProbability (H : ℕ) :
    IsProbabilityMeasure (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  unfold periodicHypercubicEvenBoundaryHaarMeasure
  unfold FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure
  infer_instance

/-- Every boundary point contributes a `C(X,ℝ)`-valued raw-analysis integrand
lying in the closure of the same boundary-independent actual plaquette algebra.

The only extra operation beyond the fixed-boundary Gram-feature closure theorem
is multiplication by the real scalar `p(b) * psi_boundary(b)`, and the
subalgebra closure is closed under real scalar multiplication. -/
theorem
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMapIntegrand_mem_actualPlaquetteAlgebra_topologicalClosure
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMapIntegrand
        H beta hbeta k c b ∈
      (periodicHypercubicEvenBoundaryActualPlaquetteAlgebra
        H 2 boundaryRawActualAnalysisPlaquetteClosureTwoRankPositive).topologicalClosure := by
  let A := periodicHypercubicEvenBoundaryActualPlaquetteAlgebra
    H 2 boundaryRawActualAnalysisPlaquetteClosureTwoRankPositive
  have hK :
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMapSU2
          H beta hbeta b ∈ A.topologicalClosure := by
    simpa [A,
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMapSU2] using
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMap_mem_actualPlaquetteAlgebra_topologicalClosure
        H 2 boundaryRawActualAnalysisPlaquetteClosureTwoRankPositive beta hbeta b)
  change
    (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b *
        periodicHypercubicEvenBoundaryVacuumMoment
          H 2 boundaryRawActualAnalysisBochnerTwoRankPositive beta hbeta b) •
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureContinuousMapSU2
        H beta hbeta b ∈ A.topologicalClosure
  exact A.topologicalClosure.smul_mem hK _

/-- The full explicit normalized-trace raw actual-analysis continuous function
lies in the sup-norm closure of the actual boundary-independent plaquette
algebra.

This closes the C⁰ boundary-integration step without an abstract density
hypothesis.  The proof uses Mathlib's `Convex.integral_mem`: boundary Haar is a
probability measure, the closed subalgebra is convex, every pointwise Bochner
integrand belongs to it, and the integrand is already proved Bochner
integrable. -/
theorem
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMap_mem_actualPlaquetteAlgebra_topologicalClosure
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMap
        H beta hbeta k c ∈
      (periodicHypercubicEvenBoundaryActualPlaquetteAlgebra
        H 2 boundaryRawActualAnalysisPlaquetteClosureTwoRankPositive).topologicalClosure := by
  let A := periodicHypercubicEvenBoundaryActualPlaquetteAlgebra
    H 2 boundaryRawActualAnalysisPlaquetteClosureTwoRankPositive
  let Phi :=
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMapIntegrand
      H beta hbeta k c
  let mu := periodicHypercubicEvenBoundaryHaarMeasure H 2
  have hConvex : Convex ℝ (A.topologicalClosure : Set
      C(PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2, ℝ)) :=
    A.topologicalClosure.toSubmodule.convex
  have hClosed : IsClosed (A.topologicalClosure : Set
      C(PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2, ℝ)) :=
    Subalgebra.isClosed_topologicalClosure A
  have hMem : ∀ᵐ b ∂mu, Phi b ∈ A.topologicalClosure := by
    filter_upwards [] with b
    simpa [Phi, A] using
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMapIntegrand_mem_actualPlaquetteAlgebra_topologicalClosure
        H beta hbeta k c b
  have hInt : Integrable Phi mu := by
    simpa [Phi, mu] using
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisContinuousMapIntegrand_integrable
        H beta hbeta k c
  have hBochner :
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBochnerContinuousMap
          H beta hbeta k c ∈ A.topologicalClosure := by
    change (∫ b, Phi b ∂mu) ∈ A.topologicalClosure
    exact hConvex.integral_mem hClosed hMem hInt
  rw [periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBochnerContinuousMap_eq_existing]
    at hBochner
  simpa [A] using hBochner

end

end MathlibAnalytic
end MGAP4D
