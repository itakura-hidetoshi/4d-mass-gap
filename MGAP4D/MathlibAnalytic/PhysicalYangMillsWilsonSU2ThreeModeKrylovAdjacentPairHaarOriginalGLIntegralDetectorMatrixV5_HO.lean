import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualSourceGramAndGIContextMatrixV5_HM
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# P4-Q2-HO: the genuine GL integral detector matrix

Construct the mixed ORIGINAL two-Wilson-posterior GI integral, not a
replacement conditional law or a finite-sample surrogate. Polarization
of GL's already integrable signed-source squares proves mixed
integrability without a new measurability or denominator-bound premise.

The resulting symmetric bilinear form has the exact matrix entries
  B_ij = sum_e integral Delta_i(z) * Delta_j(z) / q_e(z) d(pair-Haar)(z).
Its quadratic value is precisely the original GL spatial mass, with NO
extra residual-energy comparison prefactor. At positive frozen beta,
ker B is exactly the all-context GI kernel K. On every HK exact finite
context certificate its rank equals the rank of HM's actual GI matrix.

All constructions retain nonnegative fine beta(n+1) independently of
positive frozen beta(n). No mode independence, source separation,
positive source-frame constant, uniformity in volume or depth, H1-C3,
Hamiltonian, or continuum Yang--Mills mass gap is asserted. HN is not
imported: the construction depends only on the verified HM ancestry.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace ENNReal BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 900000

namespace GroundStatePosteriorJoint

section WeightedIntegral

variable {X E : Type*} [MeasurableSpace X]
variable [AddCommGroup E] [Module ℝ E]
variable (μ : Measure X) (L : X → E →ₗ[ℝ] ℝ) (q : X → ℝ)

/-- Polarization supplies mixed integrability from integrability of
ALL signed squares. No measurability of q is added as a premise. -/
theorem p4Q2HO_weighted_mixed_integrable
    (hSq : ∀ a : E, Integrable (fun x => (L x a)^2 / q x) μ)
    (a b : E) : Integrable (fun x => L x a * L x b / q x) μ := by
  have h := (((hSq (a + b)).sub (hSq a)).sub (hSq b)).const_mul (1 / 2 : ℝ)
  apply h.congr
  filter_upwards with x
  simp only [Pi.sub_apply, map_add, div_eq_mul_inv]
  ring

/-- The actual weighted mixed integral, before bundling bilinearity. -/
noncomputable def p4Q2HO_weightedIntegralPair (a b : E) : ℝ :=
  ∫ x, L x a * L x b / q x ∂μ

theorem p4Q2HO_weightedIntegralPair_symm (a b : E) :
    p4Q2HO_weightedIntegralPair μ L q a b =
      p4Q2HO_weightedIntegralPair μ L q b a := by
  unfold p4Q2HO_weightedIntegralPair
  apply integral_congr_ae
  filter_upwards with x
  rw [mul_comm (L x a) (L x b)]

theorem p4Q2HO_weightedIntegralPair_add_left
    (hSq : ∀ a : E, Integrable (fun x => (L x a)^2 / q x) μ)
    (a b c : E) :
    p4Q2HO_weightedIntegralPair μ L q (a + b) c =
      p4Q2HO_weightedIntegralPair μ L q a c +
      p4Q2HO_weightedIntegralPair μ L q b c := by
  unfold p4Q2HO_weightedIntegralPair
  simp only [map_add, add_mul, add_div]
  exact integral_add
    (p4Q2HO_weighted_mixed_integrable μ L q hSq a c)
    (p4Q2HO_weighted_mixed_integrable μ L q hSq b c)

theorem p4Q2HO_weightedIntegralPair_smul_left
    (t : ℝ) (a b : E) :
    p4Q2HO_weightedIntegralPair μ L q (t • a) b =
      t * p4Q2HO_weightedIntegralPair μ L q a b := by
  unfold p4Q2HO_weightedIntegralPair
  simp only [map_smul, smul_eq_mul, mul_assoc, mul_div_assoc]
  exact integral_const_mul t (fun x => L x a * L x b / q x)

/-- The weighted integral is a genuine real bilinear form; the only
analytic premise is the verified integrability of signed squares. -/
noncomputable def p4Q2HO_weightedIntegralBilin
    (hSq : ∀ a : E, Integrable (fun x => (L x a)^2 / q x) μ) :
    LinearMap.BilinForm ℝ E where
  toFun a :=
    { toFun := fun b => p4Q2HO_weightedIntegralPair μ L q a b
      map_add' := by
        intro b c
        rw [p4Q2HO_weightedIntegralPair_symm μ L q a (b + c),
          p4Q2HO_weightedIntegralPair_add_left μ L q hSq b c a,
          p4Q2HO_weightedIntegralPair_symm μ L q b a,
          p4Q2HO_weightedIntegralPair_symm μ L q c a]
      map_smul' := by
        intro t b
        change p4Q2HO_weightedIntegralPair μ L q a (t • b) =
          t * p4Q2HO_weightedIntegralPair μ L q a b
        rw [p4Q2HO_weightedIntegralPair_symm μ L q a (t • b),
          p4Q2HO_weightedIntegralPair_smul_left μ L q t b a,
          p4Q2HO_weightedIntegralPair_symm μ L q b a] }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro c
    change p4Q2HO_weightedIntegralPair μ L q (a + b) c =
      p4Q2HO_weightedIntegralPair μ L q a c +
      p4Q2HO_weightedIntegralPair μ L q b c
    exact p4Q2HO_weightedIntegralPair_add_left μ L q hSq a b c
  map_smul' := by
    intro t a
    apply LinearMap.ext
    intro b
    change p4Q2HO_weightedIntegralPair μ L q (t • a) b =
      t * p4Q2HO_weightedIntegralPair μ L q a b
    exact p4Q2HO_weightedIntegralPair_smul_left μ L q t a b

theorem p4Q2HO_weightedIntegralBilin_apply
    (hSq : ∀ a : E, Integrable (fun x => (L x a)^2 / q x) μ)
    (a b : E) :
    p4Q2HO_weightedIntegralBilin μ L q hSq a b =
      ∫ x, L x a * L x b / q x ∂μ := rfl

end WeightedIntegral

/-- Use the fixed mathlib bilinear-form/matrix equivalence rather than
manually expanding double coefficient sums. -/
theorem p4Q2HO_realBilin_matrix_pairing
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : LinearMap.BilinForm ℝ (ι → ℝ)) (a b : ι → ℝ) :
    star a ⬝ᵥ ((LinearMap.BilinForm.toMatrix' F) *ᵥ b) = F a b := by
  simpa only [Matrix.toBilin'_toMatrix', star_trivial] using
    (Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix' F) a b).symm

local instance p4Q2HO_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HO_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HO_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HO_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HO_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2HO_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

section ActualRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "Coeff" => Fin (r + 1) → ℝ
local notation "μH" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2
local notation "Detector" =>
  p4Q2HF_actualRightGIModalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "Gap" =>
  p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap Hn (beta n) (hbeta n)
local notation "Variance" =>
  p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq Hn (beta n) (hbeta n)
local notation "JointKernel" =>
  p4Q2HG_actualRightGIJointModalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- The abstract square-integrability premise is discharged for EVERY
actual signed coefficient using GL, with the frozen coupling positive. -/
theorem p4Q2HO_actualRight_originalGI_square_integrable
    (hFrozen : 0 < beta n) (e : Link) (a : Coeff) :
    Integrable (fun z : Pair => ((Detector e z) a)^2 / Variance z.2 e) μH := by
  have h := p4Q2GL_originalWilsonSignedExpectationGapSquareDivVariance_integrable
    Hn (beta n) hFrozen
    (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e
  apply h.congr
  filter_upwards with z
  rw [p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a e z]

/-- In particular, the genuine mixed GI integrands need NO new
integrability assumption, even for dependent physical modes. -/
theorem p4Q2HO_actualRight_originalGI_mixed_integrable
    (hFrozen : 0 < beta n) (e : Link) (a b : Coeff) :
    Integrable
      (fun z : Pair => (Detector e z) a * (Detector e z) b / Variance z.2 e) μH :=
  p4Q2HO_weighted_mixed_integrable μH (Detector e)
    (fun z : Pair => Variance z.2 e)
    (p4Q2HO_actualRight_originalGI_square_integrable
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r hFrozen e) a b

/-- The ORIGINAL GL spatial integral, polarized into a bilinear form. -/
noncomputable def p4Q2HO_actualRightOriginalGLBilinear
    (hFrozen : 0 < beta n) : LinearMap.BilinForm ℝ Coeff :=
  ∑ e : Link, p4Q2HO_weightedIntegralBilin μH (Detector e)
    (fun z : Pair => Variance z.2 e)
    (p4Q2HO_actualRight_originalGI_square_integrable
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r hFrozen e)

local notation "GLForm" =>
  p4Q2HO_actualRightOriginalGLBilinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- Both arguments of the form are the actual physical source sums,
and both posterior measures are the original interacting Wilson laws. -/
theorem p4Q2HO_actualRightOriginalGLBilinear_apply
    (hFrozen : 0 < beta n) (a b : Coeff) :
    GLForm hFrozen a b =
      ∑ e : Link, ∫ z : Pair,
        Gap (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z *
        Gap (∑ j : Fin (r + 1), b j • RightFactor n (j : ℕ)) e z /
          Variance z.2 e ∂μH := by
  simp only [p4Q2HO_actualRightOriginalGLBilinear, LinearMap.sum_apply,
    p4Q2HO_weightedIntegralBilin_apply]
  apply Finset.sum_congr rfl
  intro e _he
  apply integral_congr_ae
  filter_upwards with z
  rw [p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a e z,
    p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r b e z]

theorem p4Q2HO_actualRightOriginalGLBilinear_symm
    (hFrozen : 0 < beta n) (a b : Coeff) :
    GLForm hFrozen a b = GLForm hFrozen b a := by
  rw [p4Q2HO_actualRightOriginalGLBilinear_apply,
    p4Q2HO_actualRightOriginalGLBilinear_apply]
  apply Finset.sum_congr rfl
  intro e _he
  apply integral_congr_ae
  filter_upwards with z
  rw [mul_comm]

/-- The genuine integral is nonnegative on the diagonal; no positive
physical-source separation constant is assumed or inferred. -/
theorem p4Q2HO_actualRightOriginalGLBilinear_self_nonneg
    (hFrozen : 0 < beta n) (a : Coeff) : 0 ≤ GLForm hFrozen a a := by
  rw [p4Q2HO_actualRightOriginalGLBilinear_apply]
  apply Finset.sum_nonneg
  intro e _he
  apply integral_nonneg
  intro z
  exact div_nonneg (mul_self_nonneg _)
    (p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
      Hn (beta n) hFrozen z.2 e).le

/-- The matrix of the ORIGINAL integrated GL detector, NOT the source
Haar Gram, residual Gram, local density variance, or finite SOS Gram. -/
noncomputable def p4Q2HO_actualRightOriginalGLIntegralMatrix
    (hFrozen : 0 < beta n) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  LinearMap.BilinForm.toMatrix' (GLForm hFrozen)

local notation "GLMatrix" =>
  p4Q2HO_actualRightOriginalGLIntegralMatrix
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- Exact original mixed-moment entries, with no residual-energy prefactor. -/
theorem p4Q2HO_actualRightOriginalGLIntegralMatrix_apply
    (hFrozen : 0 < beta n) (i j : Fin (r + 1)) :
    GLMatrix hFrozen i j =
      ∑ e : Link, ∫ z : Pair,
        Gap (RightFactor n (i : ℕ)) e z * Gap (RightFactor n (j : ℕ)) e z /
          Variance z.2 e ∂μH := by
  rw [p4Q2HO_actualRightOriginalGLIntegralMatrix,
    LinearMap.BilinForm.toMatrix'_apply,
    p4Q2HO_actualRightOriginalGLBilinear_apply]
  have hSingle (k : Fin (r + 1)) :
      (∑ l : Fin (r + 1), (Pi.single k 1 : Coeff) l •
        RightFactor n (l : ℕ)) = RightFactor n (k : ℕ) := by
    simp [Pi.single_apply, ite_smul]
  rw [hSingle i, hSingle j]

theorem p4Q2HO_actualRightOriginalGLIntegralMatrix_pairing
    (hFrozen : 0 < beta n) (a b : Coeff) :
    star a ⬝ᵥ ((GLMatrix hFrozen) *ᵥ b) = GLForm hFrozen a b :=
  p4Q2HO_realBilin_matrix_pairing (GLForm hFrozen) a b

/-- The matrix quadratic value is EXACTLY GL's original spatial mass.
The factor (1/2)*norm(T)^(-2)*exp(-16*beta) is not part of this identity. -/
theorem p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
    (hFrozen : 0 < beta n) (a : Coeff) :
    star a ⬝ᵥ ((GLMatrix hFrozen) *ᵥ a) =
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Finset.univ : Finset Link) := by
  rw [p4Q2HO_actualRightOriginalGLIntegralMatrix_pairing,
    p4Q2HO_actualRightOriginalGLBilinear_apply]
  simp only [p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass,
    p4Q2GL_originalWilsonSignedExpectationGapSquareDivVarianceLinkMean, pow_two]

theorem p4Q2HO_actualRightOriginalGLIntegralMatrix_posSemidef
    (hFrozen : 0 < beta n) : (GLMatrix hFrozen).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.ext
    intro i j
    change star (GLMatrix hFrozen j i) = GLMatrix hFrozen i j
    simp only [star_trivial, p4Q2HO_actualRightOriginalGLIntegralMatrix,
      LinearMap.BilinForm.toMatrix'_apply]
    exact p4Q2HO_actualRightOriginalGLBilinear_symm
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r hFrozen _ _
  · intro a
    rw [p4Q2HO_actualRightOriginalGLIntegralMatrix_pairing]
    exact p4Q2HO_actualRightOriginalGLBilinear_self_nonneg
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r hFrozen a

/-- The kernel of the TRUE integral matrix is exactly the all-context
GI detector kernel. This is NOT an assertion that it equals ker(Source). -/
theorem p4Q2HO_actualRightOriginalGLIntegralMatrix_ker_eq_jointKernel
    (hFrozen : 0 < beta n) :
    (GLMatrix hFrozen).mulVecLin.ker = JointKernel := by
  apply Submodule.ext
  intro a
  constructor
  · intro ha
    have hZero : (GLMatrix hFrozen) *ᵥ a = 0 := (LinearMap.mem_ker).mp ha
    apply (p4Q2HI_actualRightGLMass_zero_iff_GI_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r hFrozen a).mp
    rw [← p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r hFrozen a,
      hZero, dotProduct_zero]
  · intro ha
    have hAll := (p4Q2HG_actualRightGIJointModalKernel_mem_iff
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a).mp ha
    apply (LinearMap.mem_ker).mpr
    change (GLMatrix hFrozen) *ᵥ a = 0
    apply dotProduct_eq_zero
    intro b
    rw [dotProduct_comm]
    have hPair := p4Q2HO_actualRightOriginalGLIntegralMatrix_pairing
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r hFrozen b a
    rw [star_trivial] at hPair
    rw [hPair, p4Q2HO_actualRightOriginalGLBilinear_apply]
    simp only [hAll, mul_zero, zero_div, integral_zero, Finset.sum_const_zero]

/-- Every exact HK finite-context detector has the SAME kernel as the
original GL integral matrix, without assuming physical-source injectivity. -/
theorem p4Q2HO_actualRightOriginalGLIntegralMatrix_ker_eq_finiteGI
    (hFrozen : 0 < beta n) (s : Finset (Link × Pair))
    (hExact : (p4Q2HK_actualRightFiniteGIContextDetector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r s).ker =
      JointKernel) :
    (GLMatrix hFrozen).mulVecLin.ker =
      (p4Q2HM_actualRightOriginalGIContextMatrix
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r s).mulVecLin.ker := by
  rw [p4Q2HO_actualRightOriginalGLIntegralMatrix_ker_eq_jointKernel,
    p4Q2HM_actualRightOriginalGIContextMatrix_mulVecLin_eq_detector]
  exact hExact.symm

/-- The matrix rank of the original integral detector equals the rank
of the actual finite GI detector, not necessarily the physical source rank. -/
theorem p4Q2HO_actualRightOriginalGLIntegralMatrix_rank_eq_finiteGI
    (hFrozen : 0 < beta n) (s : Finset (Link × Pair))
    (hExact : (p4Q2HK_actualRightFiniteGIContextDetector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r s).ker =
      JointKernel) :
    (GLMatrix hFrozen).rank =
      (p4Q2HM_actualRightOriginalGIContextMatrix
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r s).rank := by
  let M := p4Q2HM_actualRightOriginalGIContextMatrix
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r s
  have hB := LinearMap.finrank_range_add_finrank_ker (GLMatrix hFrozen).mulVecLin
  have hM := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hK := p4Q2HO_actualRightOriginalGLIntegralMatrix_ker_eq_finiteGI
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r hFrozen s hExact
  change (GLMatrix hFrozen).mulVecLin.ker = M.mulVecLin.ker at hK
  rw [hK] at hB
  change Module.finrank ℝ ↥(GLMatrix hFrozen).mulVecLin.range =
    Module.finrank ℝ ↥M.mulVecLin.range
  omega

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_weighted_mixed_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_weightedIntegralPair_add_left
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_weightedIntegralPair_smul_left
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_weightedIntegralBilin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_realBilin_matrix_pairing
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_actualRight_originalGI_square_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_actualRight_originalGI_mixed_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_actualRightOriginalGLBilinear
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_actualRightOriginalGLBilinear_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_actualRightOriginalGLBilinear_symm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_actualRightOriginalGLBilinear_self_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_actualRightOriginalGLIntegralMatrix
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_actualRightOriginalGLIntegralMatrix_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_actualRightOriginalGLIntegralMatrix_pairing
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_actualRightOriginalGLIntegralMatrix_posSemidef
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_actualRightOriginalGLIntegralMatrix_ker_eq_jointKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_actualRightOriginalGLIntegralMatrix_ker_eq_finiteGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HO_actualRightOriginalGLIntegralMatrix_rank_eq_finiteGI
