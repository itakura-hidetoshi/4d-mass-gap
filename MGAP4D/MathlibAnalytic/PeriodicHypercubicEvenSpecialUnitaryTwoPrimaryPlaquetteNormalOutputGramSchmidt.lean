import MGAP4D.MathlibAnalytic.AdjointNormalImageLinearIndependent
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramDeterminant
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance su2NormalOutputTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance su2NormalOutputCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance su2NormalOutputSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance su2NormalOutputMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance su2NormalOutputBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance su2NormalOutputNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The actual Wilson normal outputs `A† A g_j` of the first `k + 1`
primary-plaquette Gram--Schmidt boundary modes. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutput
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ) :
    Fin (k + 1) → Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2) :=
  fun j =>
    periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
      H 2 (by norm_num) beta hbeta
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode
        H k j)

/-- Every actual normal output is already an exact synthesis output, with the
canonical open-half witness `A g_j`. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutput_eq_synthesis_analysisImage
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (j : Fin (k + 1)) :
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutput
        H beta hbeta k j =
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
        H 2 (by norm_num) beta hbeta
        (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
          H beta hbeta k j) := by
  rfl

/-- Nonvanishing of the finite actual analysis Gram determinant already makes
the normal-output family `A† A g_j` linearly independent.  No normal-invariance
or no-leakage condition is needed. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutput_linearIndependent_of_analysisGram_det_ne_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (hdet :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
        H beta hbeta k).det ≠ 0) :
    LinearIndependent ℝ
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutput
        H beta hbeta k) := by
  let A := periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
    H 2 (by norm_num) beta hbeta
  let g := periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode
    H k
  have hg : LinearIndependent ℝ g := by
    have hfull :=
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2_orthonormal
        H).linearIndependent
    have hsub := hfull.comp (fun j : Fin (k + 1) => j.1) (by
      intro i j hij
      exact Fin.ext hij)
    simpa [g,
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode]
      using hsub
  have hAg : LinearIndependent ℝ (fun j : Fin (k + 1) => A (g j)) := by
    have h :=
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_iff
        H beta hbeta k).mp hdet
    simpa [A, g,
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage,
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode]
      using h
  have hnormal :=
    continuousLinearMap_adjoint_comp_self_linearIndependent_of_map_linearIndependent
      A g hg hAg
  simpa [A, g,
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutput,
    periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator,
    periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator,
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteGramSchmidtInitialMode]
    using hnormal

/-- Mathlib Gram--Schmidt orthonormalization of the *actual synthesis outputs*
`A† A g_j`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ) :
    Fin (k + 1) → Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2) :=
  InnerProductSpace.gramSchmidtNormed ℝ
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutput
      H beta hbeta k)

/-- A nonzero finite Wilson analysis Gram determinant theorem-generates an
orthonormal boundary-Haar family directly from actual normal/synthesis outputs.
No invariant-subspace or global-surjectivity assumption appears. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt_orthonormal_of_analysisGram_det_ne_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (hdet :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
        H beta hbeta k).det ≠ 0) :
    Orthonormal ℝ
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
        H beta hbeta k) := by
  exact InnerProductSpace.gramSchmidtNormed_orthonormal
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutput_linearIndependent_of_analysisGram_det_ne_zero
      H beta hbeta k hdet)

/-- Each normalized normal-output Gram--Schmidt vector lies in the finite span
of the preceding actual normal outputs. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt_mem_normalOutput_span_Iic
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (j : Fin (k + 1)) :
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
        H beta hbeta k j ∈
      Submodule.span ℝ
        (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutput
          H beta hbeta k '' Set.Iic j) := by
  rw [periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt,
    InnerProductSpace.gramSchmidtNormed]
  exact Submodule.smul_mem _ _
    (InnerProductSpace.gramSchmidt_mem_span ℝ
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutput
        H beta hbeta k)
      (le_refl j))

/-- Consequently every theorem-generated orthonormalized normal-output vector
remains in the exact range of the actual Wilson synthesis operator `A†`.
This is the invariance-free finite synthesis statement. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt_mem_synthesis_range
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (j : Fin (k + 1)) :
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
        H beta hbeta k j ∈
      (periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
        H 2 (by norm_num) beta hbeta).range := by
  apply (Submodule.span_le.2 ?_)
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt_mem_normalOutput_span_Iic
      H beta hbeta k j)
  rintro y ⟨i, _hi, rfl⟩
  refine ⟨periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
    H beta hbeta k i, ?_⟩
  exact
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutput_eq_synthesis_analysisImage
      H beta hbeta k i).symm

/-- Explicit existence form: every normal-output Gram--Schmidt mode has an
actual open-half `L²` synthesis preimage. -/
theorem periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt_exists_synthesis_preimage
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (j : Fin (k + 1)) :
    ∃ u : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2),
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
          H 2 (by norm_num) beta hbeta u =
        periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
          H beta hbeta k j := by
  exact
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt_mem_synthesis_range
      H beta hbeta k j

end

end MathlibAnalytic
end MGAP4D
