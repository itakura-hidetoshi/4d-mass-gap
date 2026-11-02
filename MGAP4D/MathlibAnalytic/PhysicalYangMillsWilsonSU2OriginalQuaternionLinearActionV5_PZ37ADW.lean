import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSphereIsometricActionV5_PZ37ADV
import Mathlib.Analysis.Quaternion
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADW — genuine SU(2) as unit quaternions and real-linear isometries

After ADV, the exact missing route to normalized Mathlib S³ surface-measure
invariance is a *real-four-dimensional orthogonal extension* of each ORIGINAL
SU(2) left action. This file constructs its algebraic core in Mathlib's
genuine quaternion division algebra.

For each original special-unitary matrix
  [a, -conj(b); b, conj(a)]
we take the quaternion q = (re a, im a, re b, -im b).
The minus sign in the FOURTH coordinate is essential: matrix
multiplication agrees with quaternion multiplication only under this
precise convention. We prove the quaternion has norm ONE, that the
assignment preserves the identity and multiplication, and that left
multiplication by this literal quaternion is a REAL-linear isometry.
Its inverse is left multiplication by the original g⁻¹ quaternion.

These statements are all about the SAME original SU(2) and canonical
Mathlib quaternions, not a second physical gauge group. Identifying
the induced quaternion orthogonal transformation with ADV's original
sphere action and deriving invariance of the independent Mathlib
toSphere surface measure are STILL SEPARATE OPEN proofs. No false
Haar equality, unconditional radius floor, or mass-gap assertion.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators ComplexConjugate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "H4" => Quaternion ℝ

/-- The FOUR REAL components of the exact original SU(2) first column,
interpreted inside Mathlib's genuine quaternions. The fourth-coordinate
sign implements the SU(2) matrix convention of ADR/ADS. -/
def p4Q2PZ37ADW_originalQuaternion (g : G) : H4 :=
  ⟨((g : Mat) 0 0).re, ((g : Mat) 0 0).im,
    ((g : Mat) 1 0).re, -((g : Mat) 1 0).im⟩

/-- The quaternionic squared norm is ONE using ADR's original
special-unitary first-column certificate, with no new group assumption. -/
theorem p4Q2PZ37ADW_originalQuaternion_normSq_one (g : G) :
    Quaternion.normSq (p4Q2PZ37ADW_originalQuaternion g) = 1 := by
  have h := p4Q2PZ37ADR_originalFirstColumn_normSq_one g
  simp only [Complex.normSq_apply] at h
  simp only [p4Q2PZ37ADW_originalQuaternion, Quaternion.normSq_def']
  nlinarith only [h]

/-- The true quaternion representing each original SU(2) element
has norm exactly one, not just a nonzero uncalibrated norm. -/
theorem p4Q2PZ37ADW_originalQuaternion_norm_one (g : G) :
    ‖p4Q2PZ37ADW_originalQuaternion g‖ = 1 := by
  have hs := p4Q2PZ37ADW_originalQuaternion_normSq_one g
  rw [Quaternion.normSq_eq_norm_mul_self] at hs
  have hn : 0 ≤ ‖p4Q2PZ37ADW_originalQuaternion g‖ := norm_nonneg _
  nlinarith only [hs, hn]

/-- Actual identity matrix corresponds to the literal quaternion identity. -/
theorem p4Q2PZ37ADW_originalQuaternion_one :
    p4Q2PZ37ADW_originalQuaternion (1 : G) = (1 : H4) := by
  apply Quaternion.ext <;>
    norm_num [p4Q2PZ37ADW_originalQuaternion,
      Quaternion.re_one, Quaternion.imI_one,
      Quaternion.imJ_one, Quaternion.imK_one]

/-- The original SU(2) matrix multiplication is *exactly*
quaternion multiplication under the proven sign convention. -/
theorem p4Q2PZ37ADW_originalQuaternion_mul (g h : G) :
    p4Q2PZ37ADW_originalQuaternion (g * h) =
      p4Q2PZ37ADW_originalQuaternion g *
        p4Q2PZ37ADW_originalQuaternion h := by
  let a : ℂ := (g : Mat) 0 0
  let b : ℂ := (g : Mat) 1 0
  let c : ℂ := (h : Mat) 0 0
  let d : ℂ := (h : Mat) 1 0
  have hg : (g : Mat) = !![a, -conj b; b, conj a] := by
    simpa [a, b] using p4Q2PZ37ADR_originalMatrix_fromFirstColumn g
  have hh : (h : Mat) = !![c, -conj d; d, conj c] := by
    simpa [c, d] using p4Q2PZ37ADR_originalMatrix_fromFirstColumn h
  have h00 : (((g * h : G) : Mat) 0 0) = a * c - conj b * d := by
    change (((g : Mat) * (h : Mat)) 0 0) = _
    rw [hg, hh]
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have h10 : (((g * h : G) : Mat) 1 0) = b * c + conj a * d := by
    change (((g : Mat) * (h : Mat)) 1 0) = _
    rw [hg, hh]
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hQ :
      p4Q2PZ37ADW_originalQuaternion (g * h) =
        (⟨(a * c - conj b * d).re,
          (a * c - conj b * d).im,
          (b * c + conj a * d).re,
          -(b * c + conj a * d).im⟩ : H4) := by
    apply Quaternion.ext <;>
      simp [p4Q2PZ37ADW_originalQuaternion, h00, h10]
  rw [hQ]
  apply Quaternion.ext
  all_goals
    simp [p4Q2PZ37ADW_originalQuaternion,
      Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul,
      Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.conj_re, Complex.conj_im,
      a, b, c, d]
    <;> ring

/-- Original true SU(2) group multiplication yields a single
canonical monoid homomorphism into real quaternions. -/
def p4Q2PZ37ADW_originalQuaternionHom : G →* H4 where
  toFun := p4Q2PZ37ADW_originalQuaternion
  map_one' := p4Q2PZ37ADW_originalQuaternion_one
  map_mul' := p4Q2PZ37ADW_originalQuaternion_mul

/-- Left multiplication by an ACTUAL original SU(2) quaternion
is a real-linear map of Mathlib's four-dimensional division algebra. -/
def p4Q2PZ37ADW_originalQuaternionLeftLinear (g : G) : H4 →ₗ[ℝ] H4 where
  toFun x := p4Q2PZ37ADW_originalQuaternion g * x
  map_add' x y := mul_add _ x y
  map_smul' r x := Algebra.mul_smul_comm r
    (p4Q2PZ37ADW_originalQuaternion g) x

/-- The same original-group quaternion multiplication acts as a
genuine real-linear ISOMETRY, not merely a bounded operator. -/
noncomputable def p4Q2PZ37ADW_originalQuaternionLeftIsometry (g : G) :
    H4 →ₗᵢ[ℝ] H4 :=
  { p4Q2PZ37ADW_originalQuaternionLeftLinear g with
    norm_map' := by
      intro x
      change ‖p4Q2PZ37ADW_originalQuaternion g * x‖ = ‖x‖
      rw [norm_mul, p4Q2PZ37ADW_originalQuaternion_norm_one, one_mul] }

/-- Inverse SU(2) left multiplication gives BOTH inverse linear
transformations. Their product uses no additional quaternion axioms. -/
noncomputable def p4Q2PZ37ADW_originalQuaternionLeftLinearIsometryEquiv
    (g : G) : H4 ≃ₗᵢ[ℝ] H4 :=
  LinearIsometryEquiv.ofLinearIsometry
    (p4Q2PZ37ADW_originalQuaternionLeftIsometry g)
    (p4Q2PZ37ADW_originalQuaternionLeftIsometry g⁻¹)
    (by
      apply LinearMap.ext
      intro x
      change
        p4Q2PZ37ADW_originalQuaternion g *
          (p4Q2PZ37ADW_originalQuaternion g⁻¹ * x) = x
      rw [← mul_assoc, ← p4Q2PZ37ADW_originalQuaternion_mul,
        mul_inv_cancel, p4Q2PZ37ADW_originalQuaternion_one, one_mul])
    (by
      apply LinearMap.ext
      intro x
      change
        p4Q2PZ37ADW_originalQuaternion g⁻¹ *
          (p4Q2PZ37ADW_originalQuaternion g * x) = x
      rw [← mul_assoc, ← p4Q2PZ37ADW_originalQuaternion_mul,
        inv_mul_cancel, p4Q2PZ37ADW_originalQuaternion_one, one_mul])

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADW_originalQuaternion_normSq_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADW_originalQuaternion_norm_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADW_originalQuaternion_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADW_originalQuaternion_mul
