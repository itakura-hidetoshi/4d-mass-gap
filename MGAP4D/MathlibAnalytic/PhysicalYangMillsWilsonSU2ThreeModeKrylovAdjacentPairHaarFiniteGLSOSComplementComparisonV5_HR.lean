import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLSOSPositiveCommonComplementV5_HQ
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# P4-Q2-HR: finite-volume comparison of actual Wilson detector quadratic forms

This file proves a finite-dimensional analytic lemma: every continuous
positive real quadratic homogeneous function has a strictly positive
lower and finite upper Euclidean-norm-square bound. The unit sphere of
a finite-dimensional real normed space is compact, including the
zero-dimensional case where its sphere is empty.

Apply this lemma to TWO DIFFERENT true Wilson detector quadratic forms:
B, the original interacting-posterior GL pair-Haar integral Gram, and
R=MᵀM, the finite original two-posterior squared GI context Gram.
HQ has proved strict positivity on the common real coefficient-space
complement W of the all-link/all-boundary GI joint kernel K.
The resulting c,C are allowed to depend on the actual finite lattice,
Krylov depth, frozen beta and chosen genuine physical contexts.

Neither K=ker(physical source synthesis), a GI anchor, nor
volume/spacing/depth-uniform constants are assumed or concluded.
No H1-C3, continuum Hamiltonian or four-dimensional mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace ENNReal BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 950000

namespace GroundStatePosteriorJoint

/-- Compact-unit-sphere lower and upper bounds for a strictly positive
continuous real quadratic-homogeneous function, including E=0.
This has no gauge-theory or Wilson-model assumptions. -/
theorem p4Q2HR_continuous_pos_quadratic_norm_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (q : E → ℝ) (hContinuous : Continuous q)
    (hHom : ∀ (c : ℝ) (x : E), q (c • x) = c ^ 2 * q x)
    (hPos : ∀ x : E, x ≠ 0 → 0 < q x) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      ∀ x : E, m * ‖x‖ ^ 2 ≤ q x ∧ q x ≤ M * ‖x‖ ^ 2 := by
  let S : Set E := Metric.sphere (0 : E) 1
  have hCompact : IsCompact S := by
    dsimp [S]
    exact isCompact_sphere _ _
  have hSphereNorm (x : E) (hx : x ∈ S) : ‖x‖ = 1 := by
    simpa [S, Metric.mem_sphere] using hx
  have hSpherePos : ∀ x ∈ S, 0 < q x := by
    intro x hx
    have hxne : x ≠ 0 := by
      intro he
      have hn := hSphereNorm x hx
      rw [he] at hn
      norm_num at hn
    exact hPos x hxne
  obtain ⟨m, hm, hmLower⟩ :=
    hCompact.exists_forall_le' hContinuous.continuousOn hSpherePos
  have hImage : IsCompact (q '' S) :=
    hCompact.image_of_continuousOn hContinuous.continuousOn
  obtain ⟨U, hU⟩ : BddAbove (q '' S) := hImage.bddAbove
  have hUpperSphere (x : E) (hx : x ∈ S) : q x ≤ max U 1 :=
    (hU (Set.mem_image_of_mem q hx)).trans (le_max_left U 1)
  refine ⟨m, max U 1, hm,
    lt_of_lt_of_le zero_lt_one (le_max_right U 1), ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    have hqZero : q (0 : E) = 0 := by
      have h := hHom 0 (0 : E)
      simpa using h
    simp [hqZero]
  · have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let u : E := (‖x‖⁻¹ : ℝ) • x
    have huNorm : ‖u‖ = 1 := by
      simp [u, norm_smul, hnx]
    have huSphere : u ∈ S := by
      simpa [S, Metric.mem_sphere] using huNorm
    have hScaled : (‖x‖ : ℝ) • u = x := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ hnx, one_smul]
    have hQuad : q x = ‖x‖ ^ 2 * q u := by
      calc
        q x = q ((‖x‖ : ℝ) • u) := by rw [hScaled]
        _ = ‖x‖ ^ 2 * q u := hHom _ _
    constructor
    · calc
        m * ‖x‖ ^ 2 ≤ q u * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hmLower u huSphere) (sq_nonneg _)
        _ = q x := by rw [hQuad]; ring
    · calc
        q x = q u * ‖x‖ ^ 2 := by rw [hQuad]; ring
        _ ≤ max U 1 * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hUpperSphere u huSphere) (sq_nonneg _)

/-- Any pair of strictly positive, continuous, degree-two homogeneous
quadratic energies on a real finite-dimensional normed space admits
strict finite positive comparison constants. They need not be uniform
as the space or the two physical forms change. -/
theorem p4Q2HR_finiteDimensional_positive_quadratics_comparable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (qB qR : E → ℝ)
    (hContB : Continuous qB) (hContR : Continuous qR)
    (hHomB : ∀ (c : ℝ) (x : E), qB (c • x) = c ^ 2 * qB x)
    (hHomR : ∀ (c : ℝ) (x : E), qR (c • x) = c ^ 2 * qR x)
    (hPosB : ∀ x : E, x ≠ 0 → 0 < qB x)
    (hPosR : ∀ x : E, x ≠ 0 → 0 < qR x) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ x : E, c * qR x ≤ qB x ∧ qB x ≤ C * qR x := by
  obtain ⟨mB, MB, hmB, hMB, hB⟩ :=
    p4Q2HR_continuous_pos_quadratic_norm_bounds qB hContB hHomB hPosB
  obtain ⟨mR, MR, hmR, hMR, hR⟩ :=
    p4Q2HR_continuous_pos_quadratic_norm_bounds qR hContR hHomR hPosR
  let c0 : ℝ := mB / MR
  let C0 : ℝ := MB / mR
  have hc0 : 0 < c0 := div_pos hmB hMR
  have hC0 : 0 < C0 := div_pos hMB hmR
  have hc : 0 < min c0 1 := lt_min hc0 zero_lt_one
  have hC : 1 ≤ max C0 1 := le_max_right _ _
  refine ⟨min c0 1, max C0 1, hc,
    (min_le_right _ _).trans hC, ?_⟩
  intro x
  have hRnonneg : 0 ≤ qR x :=
    (mul_nonneg hmR.le (sq_nonneg _)).trans (hR x).1
  have hLower : c0 * qR x ≤ qB x := by
    calc
      c0 * qR x ≤ c0 * (MR * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hR x).2 hc0.le
      _ = mB * ‖x‖ ^ 2 := by
        dsimp [c0]
        field_simp [ne_of_gt hMR]
      _ ≤ qB x := (hB x).1
  have hUpper : qB x ≤ C0 * qR x := by
    calc
      qB x ≤ MB * ‖x‖ ^ 2 := (hB x).2
      _ = C0 * (mR * ‖x‖ ^ 2) := by
        dsimp [C0]
        field_simp [ne_of_gt hmR]
      _ ≤ C0 * qR x :=
        mul_le_mul_of_nonneg_left (hR x).1 hC0.le
  constructor
  · exact (mul_le_mul_of_nonneg_right (min_le_left c0 1) hRnonneg).trans hLower
  · exact hUpper.trans
      (mul_le_mul_of_nonneg_right (le_max_left C0 1) hRnonneg)

/-- The actual finite real matrix quadratic value is a continuous
finite polynomial on its real coordinate space. -/
theorem p4Q2HR_realMatrix_quad_continuous
    {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) :
    Continuous (fun a : ι → ℝ => star a ⬝ᵥ (M *ᵥ a)) := by
  classical
  simp only [star_trivial, dotProduct, Matrix.mulVec]
  fun_prop

/-- Real matrix quadratic values scale exactly by c² on every vector.
No positivity or symmetry of the matrix is needed. -/
theorem p4Q2HR_realMatrix_quad_smul
    {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    (c : ℝ) (a : ι → ℝ) :
    star (c • a) ⬝ᵥ (M *ᵥ (c • a)) =
      c ^ 2 * (star a ⬝ᵥ (M *ᵥ a)) := by
  simp only [star_trivial, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring

local instance p4Q2HR_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HR_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HR_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HR_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HR_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2HR_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

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
local notation "Context" => Link × Pair
local notation "JointKernel" =>
  p4Q2HG_actualRightGIJointModalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "FiniteDetector" =>
  p4Q2HK_actualRightFiniteGIContextDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "B" =>
  p4Q2HO_actualRightOriginalGLIntegralMatrix
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "R" =>
  p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- Explicit finite-real-constant comparison on the quotient representative
W of the authentic all-context GI kernel, for the original Wilson GL
integral B and the finite authentic GI-squared detector R. The constants
may depend on the full fixed physical finite model and chosen contexts. -/
theorem p4Q2HR_actualRight_Wilson_GL_SOS_comparison_on_complement
    (hFrozen : 0 < beta n) (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel)
    (W : Submodule ℝ Coeff) (hCompl : IsCompl JointKernel W) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ w : W,
        c * (star (w : Coeff) ⬝ᵥ ((R s) *ᵥ (w : Coeff))) ≤
          star (w : Coeff) ⬝ᵥ ((B hFrozen) *ᵥ (w : Coeff)) ∧
        star (w : Coeff) ⬝ᵥ ((B hFrozen) *ᵥ (w : Coeff)) ≤
          C * (star (w : Coeff) ⬝ᵥ ((R s) *ᵥ (w : Coeff))) := by
  let qB : W → ℝ := fun w =>
    star (w : Coeff) ⬝ᵥ ((B hFrozen) *ᵥ (w : Coeff))
  let qR : W → ℝ := fun w =>
    star (w : Coeff) ⬝ᵥ ((R s) *ᵥ (w : Coeff))
  have hcB : Continuous qB := by
    exact (p4Q2HR_realMatrix_quad_continuous (B hFrozen)).comp continuous_subtype_val
  have hcR : Continuous qR := by
    exact (p4Q2HR_realMatrix_quad_continuous (R s)).comp continuous_subtype_val
  have hhB (c : ℝ) (w : W) : qB (c • w) = c ^ 2 * qB w := by
    simpa only [qB, Submodule.coe_smul] using
      (p4Q2HR_realMatrix_quad_smul (B hFrozen) c (w : Coeff))
  have hhR (c : ℝ) (w : W) : qR (c • w) = c ^ 2 * qR w := by
    simpa only [qR, Submodule.coe_smul] using
      (p4Q2HR_realMatrix_quad_smul (R s) c (w : Coeff))
  have hpB (w : W) (hw : w ≠ 0) : 0 < qB w :=
    p4Q2HQ_actualRight_GLGram_pos_on_complement
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen W hCompl w hw
  have hpR (w : W) (hw : w ≠ 0) : 0 < qR w :=
    p4Q2HQ_actualRight_SOSGram_pos_on_complement
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s hExact W hCompl w hw
  exact p4Q2HR_finiteDimensional_positive_quadratics_comparable
    qB qR hcB hcR hhB hhR hpB hpR

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HR_continuous_pos_quadratic_norm_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HR_finiteDimensional_positive_quadratics_comparable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HR_realMatrix_quad_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HR_realMatrix_quad_smul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HR_actualRight_Wilson_GL_SOS_comparison_on_complement
