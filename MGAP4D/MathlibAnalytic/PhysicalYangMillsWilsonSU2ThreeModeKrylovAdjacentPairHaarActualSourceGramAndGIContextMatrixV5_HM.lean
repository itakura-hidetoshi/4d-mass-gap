import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualGIFiniteDetectorPhysicalRankCriterionV5_HL
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# P4-Q2-HM: true physical Haar-L2 source Gram versus actual finite Wilson GI matrix

HL reduces physical source separation to equality of ranks of two finite
linear maps: the genuine fine-right physical source synthesis S and the
finite-context original interacting Wilson GI expectation-gap detector D_F.

HM builds TWO DISTINCT matrices on that same actual coefficient domain:
* Q_ij = real Haar-L² inner product of the ACTUAL physical fine-right
  gauge-invariant Krylov modes v_i and v_j, NOT the pair-Haar residual Gram;
* M_xj = the true original TWO-INTERACTING-WILSON-posterior GI
  expectation gap of mode v_j at a physical link and pair boundary x,
  for x in the FINITE exact GI context certificate from HK.

A generic mathlib Gram quadratic identity identifies ker(Q.mulVecLin)
exactly with the genuine physical synthesis kernel, even for dependent
physical modes and arbitrarily nonnegative fine beta. Using rank-nullity
we prove rank Q = finrank(range S).

The entrywise original GI detector modal formula from HF shows
M.mulVecLin = D_F and hence rank M = finrank(range D_F).

As a consequence, for every selected HK exact context certificate,

  ker S = K   iff  Q.rank = M.rank,

and the STRICT physical Gram rank excess Q.rank > M.rank is equivalent
to a nonzero physical source invisible to ALL selected actual Wilson GI
evaluations. This is a true finite matrix RANK CERTIFICATE, not a proof
that the two matrix ranks coincide in the interacting Wilson theory.

No synthetic Haar posterior, source-mode independence, numeric ranks,
context cardinality bound, GL integral coercivity, H1-C3, Hamiltonian,
volume uniformity, or continuum 4D Yang--Mills mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace ENNReal BigOperators

noncomputable section
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 900000

local instance p4Q2HM_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HM_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HM_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HM_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HM_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2HM_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Real linear synthesis of any finite family in a genuine
inner-product space. This abstraction keeps elaborate physical
Haar-L² definitions OUTSIDE the Gram kernel calculation. -/
noncomputable def p4Q2HM_finiteInnerSourceSynthesis
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) : (ι → ℝ) →ₗ[ℝ] E where
  toFun a := ∑ j, a j • v j
  map_add' := by
    intro a b
    change (∑ j, (a j + b j) • v j) =
      (∑ j, a j • v j) + (∑ j, b j • v j)
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c a
    change (∑ j, (c * a j) • v j) =
      c • (∑ j, a j • v j)
    simp only [mul_smul, Finset.smul_sum]

/-- Gram multiplication vanishes precisely when the corresponding
REAL finite physical-vector synthesis vanishes. The forward direction
uses the ORIGINAL inner product and mathlib's
Matrix.star_dotProduct_gram_mulVec, not a separate detector. -/
theorem p4Q2HM_gram_mulVec_zero_iff_synthesis_zero
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a : ι → ℝ) :
    (Matrix.gram ℝ v).mulVec a = 0 ↔
      p4Q2HM_finiteInnerSourceSynthesis v a = 0 := by
  constructor
  · intro hQa
    have hQuadratic :=
      Matrix.star_dotProduct_gram_mulVec v a a
    rw [hQa] at hQuadratic
    have hInnerZero :
        ⟪∑ j, a j • v j, ∑ j, a j • v j⟫_ℝ = 0 := by
      simpa using hQuadratic.symm
    change (∑ j, a j • v j) = 0
    exact inner_self_eq_zero.mp hInnerZero
  · intro hSa
    have hSource : (∑ j, a j • v j) = 0 := hSa
    funext i
    calc
      ((Matrix.gram ℝ v).mulVec a) i =
          ⟪v i, ∑ j, a j • v j⟫_ℝ := by
            simp [Matrix.mulVec, dotProduct, Matrix.gram_apply,
              inner_sum, real_inner_smul_right, mul_comm]
      _ = 0 := by rw [hSource]; exact inner_zero_right _

/-- The usual real Gram's ACTUAL matrix kernel is exactly the kernel
of the finite physical source linear map. No independence premise. -/
theorem p4Q2HM_gram_mulVecLin_ker_eq_synthesis_ker
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) :
    (Matrix.gram ℝ v).mulVecLin.ker =
      (p4Q2HM_finiteInnerSourceSynthesis v).ker := by
  ext a
  exact p4Q2HM_gram_mulVec_zero_iff_synthesis_zero v a

/-- The rank of a finite real physical Gram matrix equals the dimension
of the actual physical finite-source span, NOT the dimension of an
unrelated pair-Haar residual Gram. -/
theorem p4Q2HM_gram_rank_eq_synthesis_finrank
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) :
    (Matrix.gram ℝ v).rank =
      Module.finrank ℝ ↥(p4Q2HM_finiteInnerSourceSynthesis v).range := by
  have hQ := LinearMap.finrank_range_add_finrank_ker
    (Matrix.gram ℝ v).mulVecLin
  have hS := LinearMap.finrank_range_add_finrank_ker
    (p4Q2HM_finiteInnerSourceSynthesis v)
  rw [p4Q2HM_gram_mulVecLin_ker_eq_synthesis_ker v] at hQ
  change Module.finrank ℝ ↥(Matrix.gram ℝ v).mulVecLin.range =
    Module.finrank ℝ ↥(p4Q2HM_finiteInnerSourceSynthesis v).range
  omega

section ActualRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Coeff" => Fin (r + 1) → ℝ
local notation "Pair" => Cfg × Cfg
local notation "Context" => Link × Pair
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "FiniteDetector" =>
  p4Q2HK_actualRightFiniteGIContextDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "JointKernel" =>
  p4Q2HG_actualRightGIJointModalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- Real Haar-L² Gram of the ACTUAL gauge-invariant fine-right Krylov
physical source modes. Distinct from the previously studied physical
residual/pair-Haar Gram matrix. -/
noncomputable def p4Q2HM_actualRightPhysicalHaarL2SourceGram :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  Matrix.gram ℝ (fun j : Fin (r + 1) => RightFactor n (j : ℕ))

theorem p4Q2HM_actualRightPhysicalHaarL2SourceGram_apply
    (i j : Fin (r + 1)) :
    p4Q2HM_actualRightPhysicalHaarL2SourceGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i j =
      ⟪RightFactor n (i : ℕ), RightFactor n (j : ℕ)⟫_ℝ := rfl

/-- Positivity belongs to the true physical Haar-L² source Gram,
without requiring independent source modes. -/
theorem p4Q2HM_actualRightPhysicalHaarL2SourceGram_posSemidef :
    Matrix.PosSemidef
      (p4Q2HM_actualRightPhysicalHaarL2SourceGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r) := by
  exact Matrix.posSemidef_gram ℝ
    (fun j : Fin (r + 1) => RightFactor n (j : ℕ))

/-- Physical Gram rank equals the ACTUAL Haar-L² source synthesis rank.
This is true even for collapsed fine-beta-zero source modes. -/
theorem p4Q2HM_actualRightPhysicalHaarL2SourceGram_rank_eq_source :
    (p4Q2HM_actualRightPhysicalHaarL2SourceGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r).rank = Module.finrank ℝ ↥(PhysicalSource).range := by
  let v : Fin (r + 1) → Phys := fun j => RightFactor n (j : ℕ)
  have hPhysical :
      p4Q2HM_finiteInnerSourceSynthesis v = PhysicalSource := by
    ext a
    rfl
  change (Matrix.gram ℝ v).rank =
    Module.finrank ℝ ↥(PhysicalSource).range
  rw [← hPhysical]
  exact p4Q2HM_gram_rank_eq_synthesis_finrank v

/-- A FINITE *entrywise* real matrix of actual two-interacting-Wilson
GI posterior expectation differences at the genuine SU(2) contexts
selected by HK, not an independent-Haar substitute. -/
noncomputable def p4Q2HM_actualRightOriginalGIContextMatrix
    (s : Finset Context) : Matrix s (Fin (r + 1)) ℝ :=
  fun x j =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n)
      (RightFactor n (j : ℕ)) x.1.1 x.1.2

theorem p4Q2HM_actualRightOriginalGIContextMatrix_apply
    (s : Finset Context) (x : s) (j : Fin (r + 1)) :
    p4Q2HM_actualRightOriginalGIContextMatrix
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s x j =
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n)
      (RightFactor n (j : ℕ)) x.1.1 x.1.2 := rfl

/-- Matrix times coefficients IS EXACTLY HK's finite authentic GI
Wilson modal linear detector, for arbitrary fine beta>=0. -/
theorem p4Q2HM_actualRightOriginalGIContextMatrix_mulVec_eq_detector
    (s : Finset Context) (a : Coeff) :
    (p4Q2HM_actualRightOriginalGIContextMatrix
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s).mulVec a = FiniteDetector s a := by
  funext x
  change
    (∑ j : Fin (r + 1),
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n)
        (RightFactor n (j : ℕ)) x.1.1 x.1.2 * a j) =
    p4Q2GY_modalTransferLinear r
      (fun j : Fin (r + 1) =>
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n)
          (RightFactor n (j : ℕ)) x.1.1 x.1.2) a
  rw [p4Q2GY_modalTransferLinear_apply]
  apply Finset.sum_congr rfl
  intro j _hj
  exact mul_comm _ _

/-- The genuine original GI matrix induces exactly HK's physical
finite two-posterior detector as a real linear map. -/
theorem p4Q2HM_actualRightOriginalGIContextMatrix_mulVecLin_eq_detector
    (s : Finset Context) :
    (p4Q2HM_actualRightOriginalGIContextMatrix
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s).mulVecLin = FiniteDetector s := by
  ext a
  exact p4Q2HM_actualRightOriginalGIContextMatrix_mulVec_eq_detector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r s a

/-- Matrix.rank of the literal original Wilson GI expectation-gap
matrix equals the finite detector image dimension proved in HL. -/
theorem p4Q2HM_actualRightOriginalGIContextMatrix_rank_eq_detector
    (s : Finset Context) :
    (p4Q2HM_actualRightOriginalGIContextMatrix
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s).rank = Module.finrank ℝ ↥(FiniteDetector s).range := by
  change Module.finrank ℝ
    ↥((p4Q2HM_actualRightOriginalGIContextMatrix
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s).mulVecLin).range = Module.finrank ℝ ↥(FiniteDetector s).range
  rw [p4Q2HM_actualRightOriginalGIContextMatrix_mulVecLin_eq_detector]

/-- A concrete FINITE-MATRIX necessary-and-sufficient test for physical
source separation at genuine original Wilson GI contexts. Neither
matrix rank is asserted to equal the other unconditionally. -/
theorem p4Q2HM_actualRight_sourceSeparation_iff_originalGI_matrixRanksEq
    (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    (PhysicalSource).ker = JointKernel ↔
      (p4Q2HM_actualRightPhysicalHaarL2SourceGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r).rank =
      (p4Q2HM_actualRightOriginalGIContextMatrix
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s).rank := by
  rw [p4Q2HM_actualRightPhysicalHaarL2SourceGram_rank_eq_source,
      p4Q2HM_actualRightOriginalGIContextMatrix_rank_eq_detector]
  exact p4Q2HL_actualRight_sourceSeparation_iff_finiteGIRankEq
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r s hExact

/-- The original GI matrix rank cannot exceed the genuinely synthesized
physical source Haar-L² Gram rank, regardless of linear dependencies
among the positive-fine-coupling Krylov sources. -/
theorem p4Q2HM_actualRight_originalGIMatrix_rank_le_physicalSourceGram
    (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    (p4Q2HM_actualRightOriginalGIContextMatrix
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s).rank ≤
    (p4Q2HM_actualRightPhysicalHaarL2SourceGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r).rank := by
  rw [p4Q2HM_actualRightPhysicalHaarL2SourceGram_rank_eq_source,
      p4Q2HM_actualRightOriginalGIContextMatrix_rank_eq_detector]
  have hLe :=
    p4Q2HL_actualRight_sourceKernel_le_exactFiniteGIKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r s hExact
  exact p4Q2HL_abstract_detector_rank_le_source_rank
    PhysicalSource (FiniteDetector s) hLe

/-- A strictly higher TRUE physical Haar-L² Gram matrix rank than the
true original GI context matrix rank is equivalent to a NONZERO
physical signed Krylov source invisible to the entire chosen GI
Wilson context family. -/
theorem p4Q2HM_actualRight_originalGIMatrix_rankLoss_iff_invisiblePhysicalSource
    (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    ((p4Q2HM_actualRightOriginalGIContextMatrix
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s).rank <
     (p4Q2HM_actualRightPhysicalHaarL2SourceGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r).rank) ↔
      ∃ a : Coeff, PhysicalSource a ≠ 0 ∧ FiniteDetector s a = 0 := by
  rw [p4Q2HM_actualRightPhysicalHaarL2SourceGram_rank_eq_source,
      p4Q2HM_actualRightOriginalGIContextMatrix_rank_eq_detector]
  exact p4Q2HL_actualRight_finiteGIRankLoss_iff_invisiblePhysicalSource
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r s hExact

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HM_finiteInnerSourceSynthesis
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HM_gram_mulVec_zero_iff_synthesis_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HM_gram_mulVecLin_ker_eq_synthesis_ker
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HM_gram_rank_eq_synthesis_finrank
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HM_actualRightPhysicalHaarL2SourceGram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HM_actualRightPhysicalHaarL2SourceGram_posSemidef
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HM_actualRightPhysicalHaarL2SourceGram_rank_eq_source
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HM_actualRightOriginalGIContextMatrix
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HM_actualRightOriginalGIContextMatrix_mulVec_eq_detector
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HM_actualRightOriginalGIContextMatrix_mulVecLin_eq_detector
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HM_actualRightOriginalGIContextMatrix_rank_eq_detector
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HM_actualRight_sourceSeparation_iff_originalGI_matrixRanksEq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HM_actualRight_originalGIMatrix_rank_le_physicalSourceGram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HM_actualRight_originalGIMatrix_rankLoss_iff_invisiblePhysicalSource
