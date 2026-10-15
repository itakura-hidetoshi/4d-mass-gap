import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualRightAllDepthZeroCoefficientPosteriorWitnessV5_GX
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-!
# P4-Q2-GY: genuine Wilson modal-transfer evaluation and a codimension-one hyperplane

For every actual finite right-Krylov depth r and true frozen beta(n), form the
finite coefficient linear functional whose j-th weight is the ORIGINAL
one-slab Wilson transfer of the ACTUAL fine physical right-Krylov mode j,
evaluated at a concrete physical right boundary B.

The constant physical zero-depth source of GV/GX supplies a strictly
positive zeroth weight, for EVERY actual right boundary, independent of
the true fine beta(n+1). Hence the modal transfer functional is
nonzero and surjective, has a proper codimension-one kernel, and the
complement of that modal kernel is open. Give an explicit decomposition
along its physical depth-zero coefficient vector.

The modal map is defined by finite sums of exact Wilson-transfer samples.
Its identification, for ALL coefficient vectors, with the original
integral of the combined physical source is a further linearity/descent
bridge; it is NOT silently postulated. The two are already identified
at the exact depth-zero coefficient witness by GX. Likewise this modal
hyperplane is NOT asserted to be the GI two-posterior expectation-gap
kernel, the true posterior squared-response zero-locus, or a uniform
source-frame. H1-C3 and the continuum mass gap remain separate.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

namespace GroundStatePosteriorJoint

section FiniteModalAlgebra

/-- Finite linear extension of a family of genuine scalar transfer
samples. This generic algebra is kept independent of the gigantic
concrete Wilson configuration type to avoid repeated whnf expansion. -/
def p4Q2GY_modalTransferLinear
    (r : ℕ) (w : Fin (r + 1) → ℝ) :
    (Fin (r + 1) → ℝ) →ₗ[ℝ] ℝ :=
  { toFun := fun a => ∑ j : Fin (r + 1), a j * w j
    map_add' := by
      intro a b
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro c a
      simp [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum] }

theorem p4Q2GY_modalTransferLinear_apply
    (r : ℕ) (w a : Fin (r + 1) → ℝ) :
    p4Q2GY_modalTransferLinear r w a =
      ∑ j : Fin (r + 1), a j * w j := rfl

/-- At the actual GX finite-depth delta-zero coefficient, the modal
functional evaluates the genuine zeroth Wilson transfer sample. -/
theorem p4Q2GY_modalTransferLinear_anchor
    (r : ℕ) (w : Fin (r + 1) → ℝ) :
    p4Q2GY_modalTransferLinear r w
      (p4Q2GX_rightZeroCoefficient r) = w 0 := by
  change (∑ j : Fin (r + 1),
    (if j = 0 then (1 : ℝ) else 0) * w j) = w 0
  simp

theorem p4Q2GY_modalTransferLinear_anchor_pos
    (r : ℕ) (w : Fin (r + 1) → ℝ) (hw : 0 < w 0) :
    0 < p4Q2GY_modalTransferLinear r w
      (p4Q2GX_rightZeroCoefficient r) := by
  rw [p4Q2GY_modalTransferLinear_anchor]
  exact hw

/-- A positive true zeroth sample makes the entire real coefficient
linear functional surjective onto ℝ, with no all-coefficient source frame. -/
theorem p4Q2GY_modalTransferLinear_surjective
    (r : ℕ) (w : Fin (r + 1) → ℝ) (hw : 0 < w 0) :
    Function.Surjective (p4Q2GY_modalTransferLinear r w) := by
  let L := p4Q2GY_modalTransferLinear r w
  let z := p4Q2GX_rightZeroCoefficient r
  have hz : 0 < L z :=
    p4Q2GY_modalTransferLinear_anchor_pos r w hw
  intro y
  refine ⟨(y / L z) • z, ?_⟩
  change L ((y / L z) • z) = y
  rw [map_smul, smul_eq_mul]
  exact div_mul_cancel₀ y (ne_of_gt hz)

/-- The modal transfer kernel is a proper real submodule. -/
theorem p4Q2GY_modalTransferLinear_ker_ne_top
    (r : ℕ) (w : Fin (r + 1) → ℝ) (hw : 0 < w 0) :
    (p4Q2GY_modalTransferLinear r w).ker ≠ ⊤ := by
  let L := p4Q2GY_modalTransferLinear r w
  let z := p4Q2GX_rightZeroCoefficient r
  have hz : 0 < L z :=
    p4Q2GY_modalTransferLinear_anchor_pos r w hw
  intro htop
  have hzMem : z ∈ L.ker := by
    rw [htop]
    trivial
  have hzZero : L z = 0 := (LinearMap.mem_ker).mp hzMem
  exact (ne_of_gt hz) hzZero

/-- Every coefficient vector has an explicit decomposition into a
modal-transfer-null vector plus its zeroth-mode direction. -/
theorem p4Q2GY_modalTransferLinear_kernel_split
    (r : ℕ) (w : Fin (r + 1) → ℝ) (hw : 0 < w 0)
    (a : Fin (r + 1) → ℝ) :
    ∃ k : Fin (r + 1) → ℝ,
      k ∈ (p4Q2GY_modalTransferLinear r w).ker ∧
        ∃ t : ℝ, a = k + t • p4Q2GX_rightZeroCoefficient r := by
  let L := p4Q2GY_modalTransferLinear r w
  let z := p4Q2GX_rightZeroCoefficient r
  have hz : 0 < L z :=
    p4Q2GY_modalTransferLinear_anchor_pos r w hw
  let t : ℝ := L a / L z
  refine ⟨a - t • z, ?_, t, ?_⟩
  · change L (a - t • z) = 0
    rw [map_sub, map_smul, smul_eq_mul]
    change L a - (L a / L z) * L z = 0
    rw [div_mul_cancel₀ _ (ne_of_gt hz)]
    exact sub_self _
  · exact (sub_add_cancel a (t • z)).symm

/-- Finite-dimensional rank-nullity: exact modal-kernel codimension one.
This says NOTHING about the unproved full physical-source transfer
linearization or any Wilson Gram lower eigenvalue. -/
theorem p4Q2GY_modalTransferLinear_kernel_finrank
    (r : ℕ) (w : Fin (r + 1) → ℝ) (hw : 0 < w 0) :
    Module.finrank ℝ ↥(p4Q2GY_modalTransferLinear r w).ker = r := by
  let L := p4Q2GY_modalTransferLinear r w
  have hSurj : Function.Surjective L :=
    p4Q2GY_modalTransferLinear_surjective r w hw
  have hRange : L.range = ⊤ := LinearMap.range_eq_top.mpr hSurj
  have hRangeDim : Module.finrank ℝ ↥L.range = 1 := by
    rw [hRange]
    simp
  have hDim : Module.finrank ℝ (Fin (r + 1) → ℝ) = r + 1 := by
    simp
  have hRank :
      Module.finrank ℝ ↥L.range + Module.finrank ℝ ↥L.ker =
        Module.finrank ℝ (Fin (r + 1) → ℝ) :=
    LinearMap.finrank_range_add_finrank_ker L
  change Module.finrank ℝ ↥L.ker = r
  omega

/-- The nonzero modal transfer locus is open in the actual
finite-dimensional real coefficient topology. -/
theorem p4Q2GY_modalTransferLinear_detected_isOpen
    (r : ℕ) (w : Fin (r + 1) → ℝ) :
    IsOpen {a : Fin (r + 1) → ℝ |
      p4Q2GY_modalTransferLinear r w a ≠ 0} := by
  let L := p4Q2GY_modalTransferLinear r w
  have hc : Continuous (fun a : Fin (r + 1) → ℝ => L a) :=
    L.continuous_of_finiteDimensional
  have ho : IsOpen (({0} : Set ℝ)ᶜ) :=
    (isClosed_singleton : IsClosed ({0} : Set ℝ)).isOpen_compl
  simpa using ho.preimage hc

end FiniteModalAlgebra

section ActualRightKrylov

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- Real modal transfer coefficients are the ACTUAL original-Wilson
one-slab transfer values of the actual fine physical right-Krylov
factors. Only the finite coefficient extension is new algebra. -/
def p4Q2GY_actualRightWilsonModalTransfer (B : Cfg) :
    (Fin (r + 1) → ℝ) →ₗ[ℝ] ℝ :=
  p4Q2GY_modalTransferLinear r
    (fun j => decomposableOneSliceTransferIntegral Hn 2 (beta n)
      (RightFactor n (j : ℕ)) B)

/-- The exact GX zero-coefficient physical source has positive
zero-depth ORIGINAL Wilson transfer at EVERY physical right B. -/
theorem p4Q2GY_actualRightWilsonModalTransfer_anchor_pos (B : Cfg) :
    0 < p4Q2GY_actualRightWilsonModalTransfer
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r B (p4Q2GX_rightZeroCoefficient r) := by
  change 0 <
    p4Q2GY_modalTransferLinear r
      (fun j => decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (RightFactor n (j : ℕ)) B)
      (p4Q2GX_rightZeroCoefficient r)
  rw [p4Q2GY_modalTransferLinear_anchor]
  exact p4Q2GV_actualFineRightZeroMode_transferIntegral_pos
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n B

theorem p4Q2GY_actualRightWilsonModalTransfer_surjective (B : Cfg) :
    Function.Surjective
      (p4Q2GY_actualRightWilsonModalTransfer
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r B) := by
  exact p4Q2GY_modalTransferLinear_surjective r
    (fun j => decomposableOneSliceTransferIntegral Hn 2 (beta n)
      (RightFactor n (j : ℕ)) B)
    (p4Q2GV_actualFineRightZeroMode_transferIntegral_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n B)

/-- At EVERY physical right boundary B the actual modal Wilson
coefficient kernel is a codimension-one real hyperplane. -/
theorem p4Q2GY_actualRightWilsonModalTransfer_kernel_finrank (B : Cfg) :
    Module.finrank ℝ
      ↥(p4Q2GY_actualRightWilsonModalTransfer
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r B).ker = r := by
  exact p4Q2GY_modalTransferLinear_kernel_finrank r
    (fun j => decomposableOneSliceTransferIntegral Hn 2 (beta n)
      (RightFactor n (j : ℕ)) B)
    (p4Q2GV_actualFineRightZeroMode_transferIntegral_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n B)

/-- At any finite right Krylov depth, the modal nonzero detector
coefficients form an open set in the real coefficient space. -/
theorem p4Q2GY_actualRightWilsonModalTransfer_detected_isOpen (B : Cfg) :
    IsOpen {a : Fin (r + 1) → ℝ |
      p4Q2GY_actualRightWilsonModalTransfer
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r B a ≠ 0} := by
  exact p4Q2GY_modalTransferLinear_detected_isOpen r
    (fun j => decomposableOneSliceTransferIntegral Hn 2 (beta n)
      (RightFactor n (j : ℕ)) B)

/-- The actual physical zeroth-source modal transfer is positive
regardless of r or the right background, while full signed-source
transfer linearization remains a separate unverified bridge. -/
theorem p4Q2GY_actualRightWilsonModalTransfer_detected_nonempty
    (B : Cfg) :
    ∃ a : Fin (r + 1) → ℝ,
      p4Q2GY_actualRightWilsonModalTransfer
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r B a ≠ 0 := by
  refine ⟨p4Q2GX_rightZeroCoefficient r, ?_⟩
  exact ne_of_gt (p4Q2GY_actualRightWilsonModalTransfer_anchor_pos
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r B)

end ActualRightKrylov
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GY_modalTransferLinear_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GY_modalTransferLinear_anchor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GY_modalTransferLinear_anchor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GY_modalTransferLinear_surjective
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GY_modalTransferLinear_ker_ne_top
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GY_modalTransferLinear_kernel_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GY_modalTransferLinear_kernel_finrank
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GY_modalTransferLinear_detected_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GY_actualRightWilsonModalTransfer_anchor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GY_actualRightWilsonModalTransfer_surjective
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GY_actualRightWilsonModalTransfer_kernel_finrank
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GY_actualRightWilsonModalTransfer_detected_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GY_actualRightWilsonModalTransfer_detected_nonempty
