import MGAP4D.MathlibAnalytic.FiniteRealInnerProbePairingMatrixNondegeneracy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonBoundaryAnalysisDualProbeGram

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance pairingProbeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance pairingProbeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance pairingProbeSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance pairingProbeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance pairingProbeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance pairingProbeSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem pairingProbeSU2RankPositive : 0 < (2 : ℕ) := by
  norm_num

/-- The direct finite pairing matrix between arbitrary open-half Haar `L²`
probes `q_i` and the first `k+1` actual SU(2) Wilson analysis images `A g_j`:

`B i j = ⟪q_i, A g_j⟫_ℝ`.

This is the finite matrix intended for explicit one-link tensor-degree,
character, or cylinder calculations. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (probe : Fin (k + 1) →
      Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2)) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  finiteRealInnerProbePairingMatrix probe
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
      H beta hbeta k)

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix_apply
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (probe : Fin (k + 1) →
      Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2))
    (i j : Fin (k + 1)) :
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix
        H beta hbeta k probe i j =
      inner ℝ (probe i)
        (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
          H beta hbeta k j) :=
  rfl

/-- A nonzero direct pairing determinant is already sufficient for the #1638
actual Wilson analysis Gram determinant to be nonzero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_of_dualProbePairingMatrix_det_ne_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (probe : Fin (k + 1) →
      Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2))
    (hpair :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix
        H beta hbeta k probe).det ≠ 0) :
    (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix
      H beta hbeta k).det ≠ 0 := by
  have h :=
    gram_det_ne_zero_of_finiteRealInnerProbePairingMatrix_det_ne_zero
      probe
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
        H beta hbeta k)
      hpair
  simpa [periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix,
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix]
    using h

/-- For at least two primary-plaquette modes, a nonzero direct pairing
determinant forces strict positivity of the Wilson coupling.  Strict positivity
is therefore still derived, not assumed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix_det_ne_zero_implies_beta_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ) (hk : 1 ≤ k)
    (probe : Fin (k + 1) →
      Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2))
    (hpair :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix
        H beta hbeta k probe).det ≠ 0) :
    0 < beta := by
  exact
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_implies_beta_pos
      H beta hbeta k hk
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_of_dualProbePairingMatrix_det_ne_zero
        H beta hbeta k probe hpair)

/-- The same direct pairing criterion theorem-generates the #1639 orthonormal
normal-output Gram--Schmidt family in the actual Wilson synthesis range. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt_orthonormal_of_dualProbePairingMatrix_det_ne_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (k : ℕ)
    (probe : Fin (k + 1) →
      Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2))
    (hpair :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix
        H beta hbeta k probe).det ≠ 0) :
    Orthonormal ℝ
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
        H beta hbeta k) := by
  exact
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt_orthonormal_of_analysisGram_det_ne_zero
      H beta hbeta k
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_of_dualProbePairingMatrix_det_ne_zero
        H beta hbeta k probe hpair)

/-- Scale-sequence form of strict coupling positivity from a direct finite
pairing determinant. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix_det_ne_zero_implies_scale_beta_pos
    (H : ℕ → ℕ) (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (n k : ℕ) (hk : 1 ≤ k)
    (probe : Fin (k + 1) →
      Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure (H n) 2))
    (hpair :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix
        (H n) (beta n) (hbeta n) k probe).det ≠ 0) :
    0 < beta n :=
  periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix_det_ne_zero_implies_beta_pos
    (H n) (beta n) (hbeta n) k hk probe hpair

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 pairingProbeSU2RankPositive beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}

/-- Direct-pairing version of the fixed-scale projective orthonormality
criterion. -/
theorem
    primaryPlaquetteNormalOutputGramSchmidt_projective_orthonormal_of_dualProbePairingMatrix_det_ne_zero
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (n k : ℕ)
    (probe : Fin (k + 1) →
      Lp ℝ 2
        (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) 2))
    (hpair :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix
        (halfExtent n) (beta n) (hbeta n) k probe).det ≠ 0) :
    Orthonormal ℝ
      ((R.boundaryHaarProjectiveL2Isometry n) ∘
        periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteNormalOutputGramSchmidt
          (halfExtent n) (beta n) (hbeta n) k) := by
  exact
    R.primaryPlaquetteNormalOutputGramSchmidt_projective_orthonormal_of_analysisGram_det_ne_zero
      n k
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_of_dualProbePairingMatrix_det_ne_zero
        (halfExtent n) (beta n) (hbeta n) k probe hpair)

/-- Direct-pairing version of the #1641 fixed-scale physical/projective
closure.  The only additional input remains the finite positive-half range
condition isolated in #1640. -/
theorem
    primaryPlaquetteNormalOutputGramSchmidt_exists_physicalHilbert_projective_orthonormal_family_of_dualProbePairingMatrix_det_ne_zero
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (probe : Fin (k + 1) →
      Lp ℝ 2
        (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) 2))
    (hpair :
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisDualProbePairingMatrix
        (halfExtent n) (beta n) (hbeta n) k probe).det ≠ 0)
    (hAnalysisRange : ∀ i : Fin (k + 1),
      periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisImage
          (halfExtent n) (beta n) (hbeta n) k i ∈
        (Q.positiveHalfL2LinearMap hInvariant n).range) :
    ∃ psi : Fin (k + 1) →
        PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
          S D halfExtent 2 pairingProbeSU2RankPositive beta hbeta
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
      (periodicHypercubicEvenSpecialUnitaryTwoPrimaryPlaquetteAnalysisGramMatrix_det_ne_zero_of_dualProbePairingMatrix_det_ne_zero
        (halfExtent n) (beta n) (hbeta n) k probe hpair)
      hAnalysisRange

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

end

end MathlibAnalytic
end MGAP4D
