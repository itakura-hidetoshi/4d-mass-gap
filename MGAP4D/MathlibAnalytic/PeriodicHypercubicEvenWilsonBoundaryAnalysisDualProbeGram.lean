import MGAP4D.MathlibAnalytic.FiniteRealInnerProbeGramNondegeneracy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonBoundaryAnalysisBetaZeroAllFiniteGramSingular
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PrimaryPlaquetteNormalOutputProjectivePhysicalReadout

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance dualProbeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance dualProbeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance dualProbeSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance dualProbeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance dualProbeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance dualProbeSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem dualProbeSU2RankPositive : 0 < (2 : ℕ) := by
  norm_num

/-- Finite dual-probe Gram matrix for the actual SU(2) Wilson analysis images.

For probes `q_i` in open-half Haar `L²`, the `j`-th coordinate vector is

`i ↦ ⟪q_i, A g_j⟫`.

The matrix below is the ordinary Gram matrix of those finite coordinate
vectors.  It is intentionally finite-dimensional: proving its determinant is
nonzero is enough to prove nondegeneracy of the full Hilbert-space analysis
images. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbeGramMatrix
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (probe : Fin (k + 1) →
      Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2)) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  finiteRealInnerProbeGramMatrix probe
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
      H beta hbeta k)

/-- A nonzero dual-probe Gram determinant implies nonvanishing of the actual
finite Wilson analysis Gram determinant.

Thus the infinite-dimensional nondegeneracy problem may be discharged by any
finite family of open-half probes whose pairing-coordinate vectors separate
the first `k + 1` analysis images. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_of_dualProbeGram_det_ne_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (probe : Fin (k + 1) →
      Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2))
    (hprobe :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbeGramMatrix
        H beta hbeta k probe).det ≠ 0) :
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
      H beta hbeta k).det ≠ 0 := by
  have h :=
    gram_det_ne_zero_of_finiteRealInnerProbeGramMatrix_det_ne_zero
      probe
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
        H beta hbeta k)
      hprobe
  simpa [periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbeGramMatrix,
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix]
    using h

/-- For a family containing at least two modes, nondegeneracy of a finite
probe Gram matrix already forces strict positivity of the Wilson coupling.
No new `0 < beta` assumption is introduced. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbeGramMatrix_det_ne_zero_implies_beta_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ) (hk : 1 ≤ k)
    (probe : Fin (k + 1) →
      Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2))
    (hprobe :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbeGramMatrix
        H beta hbeta k probe).det ≠ 0) :
    0 < beta := by
  exact
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_implies_beta_pos
      H beta hbeta k hk
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_of_dualProbeGram_det_ne_zero
        H beta hbeta k probe hprobe)

/-- The dual-probe determinant also directly theorem-generates the #1639
orthonormal normal-output family inside the actual Wilson synthesis range. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt_orthonormal_of_dualProbeGram_det_ne_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (probe : Fin (k + 1) →
      Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2))
    (hprobe :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbeGramMatrix
        H beta hbeta k probe).det ≠ 0) :
    Orthonormal ℝ
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
        H beta hbeta k) := by
  exact
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt_orthonormal_of_analysisGram_det_ne_zero
      H beta hbeta k
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_of_dualProbeGram_det_ne_zero
        H beta hbeta k probe hprobe)

/-- Scale-sequence form: a nonzero finite dual-probe determinant at scale `n`
automatically yields `0 < beta n` whenever at least two modes are probed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbeGramMatrix_det_ne_zero_implies_scale_beta_pos
    (H : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (n k : ℕ) (hk : 1 ≤ k)
    (probe : Fin (k + 1) →
      Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure (H n) 2))
    (hprobe :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbeGramMatrix
        (H n) (beta n) (hbeta n) k probe).det ≠ 0) :
    0 < beta n :=
  periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbeGramMatrix_det_ne_zero_implies_beta_pos
    (H n) (beta n) (hbeta n) k hk probe hprobe

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 dualProbeSU2RankPositive beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}

/-- A finite dual-probe determinant is sufficient for orthonormality of the
#1639 normal-output family after the existing boundary-Haar/projective
isometry. -/
theorem
    primaryPlaquetteNormalOutputGramSchmidt_projective_orthonormal_of_dualProbeGram_det_ne_zero
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (n k : ℕ)
    (probe : Fin (k + 1) →
      Lp ℝ 2
        (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) 2))
    (hprobe :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbeGramMatrix
        (halfExtent n) (beta n) (hbeta n) k probe).det ≠ 0) :
    Orthonormal ℝ
      ((R.boundaryHaarProjectiveL2Isometry n) ∘
        periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
          (halfExtent n) (beta n) (hbeta n) k) := by
  exact
    R.primaryPlaquetteNormalOutputGramSchmidt_projective_orthonormal_of_analysisGram_det_ne_zero
      n k
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_of_dualProbeGram_det_ne_zero
        (halfExtent n) (beta n) (hbeta n) k probe hprobe)

/-- Fixed-scale physical/projective closure with the infinite-dimensional Gram
determinant replaced by a finite dual-probe determinant.

The only remaining physical-range input is the already-isolated #1640
condition that the finitely many `A g_i` lie in the coherent positive-half
`L²` range.  No global synthesis surjectivity, invariant-sector hypothesis, or
strict-coupling assumption is added. -/
theorem
    primaryPlaquetteNormalOutputGramSchmidt_exists_physicalHilbert_projective_orthonormal_family_of_dualProbeGram_det_ne_zero
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (probe : Fin (k + 1) →
      Lp ℝ 2
        (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) 2))
    (hprobe :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbeGramMatrix
        (halfExtent n) (beta n) (hbeta n) k probe).det ≠ 0)
    (hAnalysisRange : ∀ i : Fin (k + 1),
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
          (halfExtent n) (beta n) (hbeta n) k i ∈
        (Q.positiveHalfL2LinearMap hInvariant n).range) :
    ∃ psi : Fin (k + 1) →
        PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
          S D halfExtent 2 dualProbeSU2RankPositive beta hbeta
          Q.toWeakStarBridge hInvariant n,
      (∀ j : Fin (k + 1),
        R.finiteOSMarginalLinearIsometry hInvariant n (psi j) =
          R.boundaryHaarProjectiveL2Isometry n
            (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
              (halfExtent n) (beta n) (hbeta n) k j)) ∧
      Orthonormal ℝ
        (fun j : Fin (k + 1) =>
          R.finiteOSMarginalLinearIsometry hInvariant n (psi j)) := by
  exact
    R.primaryPlaquetteNormalOutputGramSchmidt_exists_physicalHilbert_projective_orthonormal_family
      hInvariant n k
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_of_dualProbeGram_det_ne_zero
        (halfExtent n) (beta n) (hbeta n) k probe hprobe)
      hAnalysisRange

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

end

end MathlibAnalytic
end MGAP4D
