import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLSOSPositiveCommonComplementV5_HQ
import Mathlib.Tactic

/-!
# P4-Q2-HS: exact original Wilson quadratic detector descent by its kernel

This file proves a general matrix quadratic kernel-invariance lemma:
for a Hermitian real matrix M, adding a vector from ker(M.mulVecLin)
does not change the quadratic value star(a) ⬝ᵥ (M *ᵥ a).

Apply this directly to the genuinely interacting Wilson pair-posterior
GL outer pair-Haar integral Gram B (HO) and the finite genuine
two-posterior sum-of-squares Gram R=MᵀM (HN).
The only quotient being formed is the **GI detector quotient E/K**,
not an asserted physical source quotient E/ker S.

In particular, adding an all-context GI-null signed right-Krylov
coefficient to any coefficient does not change either true detector
energy. Together with HQ this prepares promotion of finite positive
comparison on a complement to all signed coefficient directions.
No physical source separation, volume/scale uniformity, H1-C3,
Hamiltonian, or continuum mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace ENNReal BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 950000

local instance p4Q2HS_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HS_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HS_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HS_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HS_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2HS_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- A true real Hermitian matrix quadratic form is invariant under
adding a kernel vector: no rank/injectivity hypothesis is needed. -/
theorem p4Q2HS_realHermitian_quad_add_kernel
    {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    (hHerm : M.IsHermitian) (k a : ι → ℝ)
    (hk : M *ᵥ k = 0) :
    star (k + a) ⬝ᵥ (M *ᵥ (k + a)) =
      star a ⬝ᵥ (M *ᵥ a) := by
  have hTranspose : Mᵀ = M := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hHerm.eq
  have hRow : k ᵥ* M = 0 := by
    rw [← hTranspose, Matrix.vecMul_transpose]
    exact hk
  calc
    star (k + a) ⬝ᵥ (M *ᵥ (k + a)) =
        (k + a) ⬝ᵥ (M *ᵥ a) := by
          simp only [star_trivial, Matrix.mulVec_add, hk, zero_add]
    _ = k ⬝ᵥ (M *ᵥ a) + a ⬝ᵥ (M *ᵥ a) := by
          rw [add_dotProduct]
    _ = a ⬝ᵥ (M *ᵥ a) := by
          rw [Matrix.dotProduct_mulVec, hRow]
          simp
    _ = star a ⬝ᵥ (M *ᵥ a) := by
          simp only [star_trivial]

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

/-- Every all-context GI-null coefficient is invisible to the ORIGINAL
GL integral quadratic form, even in mixed signed source combinations. -/
theorem p4Q2HS_actualRight_GL_quad_add_jointKernel
    (hFrozen : 0 < beta n)
    (k : Coeff) (hk : k ∈ JointKernel) (a : Coeff) :
    star (k + a) ⬝ᵥ ((B hFrozen) *ᵥ (k + a)) =
      star a ⬝ᵥ ((B hFrozen) *ᵥ a) := by
  have hkB : k ∈ (B hFrozen).mulVecLin.ker := by
    rw [p4Q2HO_actualRightOriginalGLIntegralMatrix_ker_eq_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen]
    exact hk
  have hkVec : (B hFrozen) *ᵥ k = 0 := (LinearMap.mem_ker).mp hkB
  exact p4Q2HS_realHermitian_quad_add_kernel (B hFrozen)
    (p4Q2HO_actualRightOriginalGLIntegralMatrix_posSemidef
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen).isHermitian k a hkVec

/-- For an HK exact physical finite SU(2) context certificate, adding
a common GI-null coefficient also leaves the genuine finite SOS
detector energy unchanged. This requires no Haar surrogate. -/
theorem p4Q2HS_actualRight_SOS_quad_add_jointKernel
    (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel)
    (k : Coeff) (hk : k ∈ JointKernel) (a : Coeff) :
    star (k + a) ⬝ᵥ ((R s) *ᵥ (k + a)) =
      star a ⬝ᵥ ((R s) *ᵥ a) := by
  have hkR : k ∈ (R s).mulVecLin.ker := by
    rw [p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_ker_eq_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s hExact]
    exact hk
  have hkVec : (R s) *ᵥ k = 0 := (LinearMap.mem_ker).mp hkR
  exact p4Q2HS_realHermitian_quad_add_kernel (R s)
    (p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_posSemidef
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s).isHermitian k a hkVec

/-- One genuine finite Wilson context family witnesses simultaneous
invariance of both true detector energies under ALL GI-null directions. -/
theorem p4Q2HS_actualRight_exists_finite_Wilson_jointKernel_invariance
    (hFrozen : 0 < beta n) :
    ∃ s : Finset Context,
      (FiniteDetector s).ker = JointKernel ∧
      ∀ (k a : Coeff), k ∈ JointKernel →
        (star (k + a) ⬝ᵥ ((B hFrozen) *ᵥ (k + a)) =
           star a ⬝ᵥ ((B hFrozen) *ᵥ a)) ∧
        (star (k + a) ⬝ᵥ ((R s) *ᵥ (k + a)) =
           star a ⬝ᵥ ((R s) *ᵥ a)) := by
  obtain ⟨s, hs⟩ :=
    p4Q2HK_actualRightFiniteGIContextDetector_ker_eq_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  refine ⟨s, hs, ?_⟩
  intro k a hk
  exact ⟨
    p4Q2HS_actualRight_GL_quad_add_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen k hk a,
    p4Q2HS_actualRight_SOS_quad_add_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s hs k hk a⟩

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HS_realHermitian_quad_add_kernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HS_actualRight_GL_quad_add_jointKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HS_actualRight_SOS_quad_add_jointKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HS_actualRight_exists_finite_Wilson_jointKernel_invariance
