import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalDepthTwoKrylovSchurResidualV5_OO
import Mathlib.Tactic

/-!
# P4-Q2-OP — exact genuine Wilson depth-two GI / physical source kernel reduction

OO constructs a TRUE signed depth-two Krylov Schur coefficient residual,
using two original interacting-Wilson posterior GI contexts, not a
surrogate source or a fabricated finite-rank detector.

This module proves that when the actual leading two-column Wilson minor
is nonzero (unconditionally supplied on a small-positive-fine interval
by OM/OO), EVERY coefficient annihilated by those two genuine GI rows
is a scalar multiple of the ACTUAL Schur residual. Thus the whole
original GI kernel and the original Gauss-law Hilbert synthesis kernel
are each contained in this same single genuine residual line.

It also proves the EXACT nondegeneracy criteria:
* all-context GI injectivity at actual depth two iff SOME THIRD actual
  original two-posterior GI link/context detects this Schur residual;
* actual depth-two physical Gauss-law source injectivity iff the
  genuine synthesized Schur residual physical Hilbert vector is nonzero.
No third mode independence, third-row nonzero, or rank-three
assumption is introduced. The dichotomy is the precise OPEN physics
obstruction, not a claim that it is already discharged.

Original frozen and fine Wilson couplings are distinct. The actual two
interacting posterior laws, FF receiver, original physical Wilson
transfer and Perron half-density are unchanged.
No Dobrushin / independent-Haar surrogate, sorry, admit, or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OP_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OP_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OP_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OP_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OP_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- EXACT real coefficient Schur elimination: for ANY actual two-row
modal system, each vector simultaneously annihilated by the two rows
is proportional to the literal depth-two Schur coefficient after
multiplication by its leading determinant. No rank hypothesis is
needed for this scaled identity. -/
theorem p4Q2OP_twoRows_null_scaledSchur
    (D D' : (Fin (2 + 1) → ℝ) →ₗ[ℝ] ℝ)
    (a : Fin (2 + 1) → ℝ)
    (hD : D a = 0) (hD' : D' a = 0) :
    p4Q2OO_depthTwoLeadingMinor D D' • a =
      a 2 • p4Q2OO_depthTwoSchurResidual D D' := by
  let u := p4Q2GX_rightZeroCoefficient 2
  let v := p4Q2OO_depthTwoFirstCoefficient
  let w := p4Q2OO_depthTwoSecondCoefficient
  let delta : ℝ := p4Q2OO_depthTwoLeadingMinor D D'
  let A : ℝ := D w * D' v - D v * D' w
  let B : ℝ := D u * D' w - D w * D' u
  have hDec := p4Q2OO_depthTwo_coeff_decompose a
  have h0 : a 0 * D u + a 1 * D v + a 2 * D w = 0 := by
    have h := hD
    rw [hDec, map_add, map_add, map_smul, map_smul, map_smul] at h
    simpa only [smul_eq_mul] using h
  have h1 : a 0 * D' u + a 1 * D' v + a 2 * D' w = 0 := by
    have h := hD'
    rw [hDec, map_add, map_add, map_smul, map_smul, map_smul] at h
    simpa only [smul_eq_mul] using h
  have hA : delta * a 0 + A * a 2 = 0 := by
    change (D u * D' v - D v * D' u) * a 0 +
      (D w * D' v - D v * D' w) * a 2 = 0
    calc
      _ = (a 0 * D u + a 1 * D v + a 2 * D w) * D' v -
          (a 0 * D' u + a 1 * D' v + a 2 * D' w) * D v := by ring
      _ = 0 := by rw [h0, h1]; ring
  have hB : delta * a 1 + B * a 2 = 0 := by
    change (D u * D' v - D v * D' u) * a 1 +
      (D u * D' w - D w * D' u) * a 2 = 0
    calc
      _ = (a 0 * D' u + a 1 * D' v + a 2 * D' w) * D u -
          (a 0 * D u + a 1 * D v + a 2 * D w) * D' u := by ring
      _ = 0 := by rw [h1, h0]; ring
  have ha0 : delta * a 0 = -(A * a 2) :=
    (eq_neg_iff_add_eq_zero).2 hA
  have ha1 : delta * a 1 = -(B * a 2) :=
    (eq_neg_iff_add_eq_zero).2 hB
  funext j
  fin_cases j
  · dsimp [delta, A, u, v, w] at ha0
    simp [p4Q2OO_depthTwoSchurResidual,
      p4Q2OO_depthTwoFirstCoefficient,
      p4Q2OO_depthTwoSecondCoefficient,
      p4Q2GX_rightZeroCoefficient,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul] <;>
      nlinarith [ha0]
  · dsimp [delta, B, u, v, w] at ha1
    simp [p4Q2OO_depthTwoSchurResidual,
      p4Q2OO_depthTwoFirstCoefficient,
      p4Q2OO_depthTwoSecondCoefficient,
      p4Q2GX_rightZeroCoefficient,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul] <;>
      nlinarith [ha1]
  · simp [p4Q2OO_depthTwoSchurResidual,
      p4Q2OO_depthTwoFirstCoefficient,
      p4Q2OO_depthTwoSecondCoefficient,
      p4Q2GX_rightZeroCoefficient,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul] <;>
      ring

/-- Once the genuine first-two minor is nonzero, the exact COMMON
kernel of those TWO selected GI rows is the SINGLE explicit Schur
residual line. This is a coefficient-space identity, not rank-three
physical source injectivity. -/
theorem p4Q2OP_twoRows_commonKernel_iff_schurLine
    (D D' : (Fin (2 + 1) → ℝ) →ₗ[ℝ] ℝ)
    (hMinor : p4Q2OO_depthTwoLeadingMinor D D' ≠ 0)
    (a : Fin (2 + 1) → ℝ) :
    (D a = 0 ∧ D' a = 0) ↔
      ∃ c : ℝ, a = c • p4Q2OO_depthTwoSchurResidual D D' := by
  constructor
  · rintro ⟨h0, h1⟩
    let delta : ℝ := p4Q2OO_depthTwoLeadingMinor D D'
    let r := p4Q2OO_depthTwoSchurResidual D D'
    have hdelta : delta ≠ 0 := hMinor
    have hScaled : delta • a = a 2 • r :=
      p4Q2OP_twoRows_null_scaledSchur D D' a h0 h1
    refine ⟨a 2 / delta, ?_⟩
    calc
      a = (1 : ℝ) • a := by simp
      _ = (delta⁻¹ * delta) • a := by rw [inv_mul_cancel₀ hdelta]
      _ = delta⁻¹ • (delta • a) := by rw [smul_smul]
      _ = delta⁻¹ • (a 2 • r) := by rw [hScaled]
      _ = (a 2 / delta) • r := by simp [smul_smul, div_eq_mul_inv, mul_comm]
  · rintro ⟨c, rfl⟩
    constructor
    · rw [map_smul, p4Q2OO_depthTwoSchurResidual_firstRow_null, smul_zero]
    · rw [map_smul, p4Q2OO_depthTwoSchurResidual_secondRow_null, smul_zero]

section ActualWilsonPhysicalDepthTwo

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "M" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Full" => p4Q2HJ_actualRightGIContinuousDetector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n

/-- At actual original Wilson link/context pair e,z and e',z',
EVERY depth-two coefficient invisible to both genuine signed GI
receivers is precisely a scalar multiple of the true OO residual. -/
theorem p4Q2OP_actualDepthTwo_twoOriginalGIrows_kernel_iff_schurLine
    (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OO_depthTwoLeadingMinor (M 2 e z) (M 2 e' z') ≠ 0)
    (a : Fin (2 + 1) → ℝ) :
    (M 2 e z a = 0 ∧ M 2 e' z' a = 0) ↔
      ∃ c : ℝ,
        a = c • p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z') := by
  exact p4Q2OP_twoRows_commonKernel_iff_schurLine
    (M 2 e z) (M 2 e' z') hMinor a

/-- The ORIGINAL complete continuous two-posterior GI detector
kernel at true depth two lies INSIDE one explicit Schur residual line
whenever the actual original first-two minor is nonzero. -/
theorem p4Q2OP_actualDepthTwo_fullGI_kernel_le_schurLine
    (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OO_depthTwoLeadingMinor (M 2 e z) (M 2 e' z') ≠ 0)
    (a : Fin (2 + 1) → ℝ)
    (hPhi : Full 2 a = 0) :
    ∃ c : ℝ,
      a = c • p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z') := by
  have hAt0 := congrArg (fun g : Link → C(Pair, ℝ) => g e z) hPhi
  have hAt1 := congrArg (fun g : Link → C(Pair, ℝ) => g e' z') hPhi
  have h0 : M 2 e z a = 0 := by
    simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
      Pi.zero_apply, ContinuousMap.zero_apply] using hAt0
  have h1 : M 2 e' z' a = 0 := by
    simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
      Pi.zero_apply, ContinuousMap.zero_apply] using hAt1
  exact (p4Q2OP_actualDepthTwo_twoOriginalGIrows_kernel_iff_schurLine
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n e e' z z' hMinor a).mp ⟨h0, h1⟩

/-- The ORIGINAL true Gauss-law Hilbert synthesis kernel is also
contained in the same one-dimensional Schur line, by the existing
physical-source-to-GI-kernel implication HJ.
No converse, artificial receiver coverage, or physical rank 3. -/
theorem p4Q2OP_actualDepthTwo_physicalSource_kernel_le_schurLine
    (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OO_depthTwoLeadingMinor (M 2 e z) (M 2 e' z') ≠ 0)
    (a : Fin (2 + 1) → ℝ)
    (hSource : S 2 a = 0) :
    ∃ c : ℝ,
      a = c • p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z') := by
  have hFull : Full 2 a = 0 :=
    (LinearMap.mem_ker).mp
      ((p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 2) ((LinearMap.mem_ker).mpr hSource))
  exact p4Q2OP_actualDepthTwo_fullGI_kernel_le_schurLine
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n e e' z z' hMinor a hFull

/-- The true depth-two Gauss-law physical source map is injective
IF AND ONLY IF its exactly constructed original Wilson Schur residual
physical Hilbert vector is nonzero. This closes the logical rank
obstruction without asserting that the still-open nonzero fact holds. -/
theorem p4Q2OP_actualDepthTwo_physicalSource_injective_iff_schurNonzero
    (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OO_depthTwoLeadingMinor (M 2 e z) (M 2 e' z') ≠ 0) :
    Function.Injective (S 2) ↔
      S 2 (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) ≠ 0 := by
  let r := p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')
  have hr : r ≠ 0 :=
    p4Q2OO_depthTwoSchurResidual_ne_zero_of_leadingMinor
      (M 2 e z) (M 2 e' z') hMinor
  constructor
  · intro hInj hZero
    apply hr
    apply hInj
    simpa only [map_zero] using hZero
  · intro hNonzero a b hab
    have hSource : S 2 (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    obtain ⟨c, hc⟩ :=
      p4Q2OP_actualDepthTwo_physicalSource_kernel_le_schurLine
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n e e' z z' hMinor (a - b) hSource
    have hCSource : c • (S 2 r) = 0 := by
      simpa only [hc, map_smul] using hSource
    have hcZero : c = 0 := by
      by_contra hcNe
      have hInv := congrArg (fun f : Phys => (c⁻¹ : ℝ) • f) hCSource
      have hRZero : S 2 r = 0 := by
        simpa only [smul_smul, inv_mul_cancel₀ hcNe, one_smul,
          smul_zero] using hInv
      exact hNonzero hRZero
    have hDiff : a - b = 0 := by
      simp only [hc, hcZero, zero_smul]
    exact sub_eq_zero.mp hDiff

/-- The entire original two-posterior GI detector is injective at
depth two IF AND ONLY IF a THIRD **genuine** original Wilson link and
boundary context (not one assumed detector) produces a nonzero
signed physical response of the same actual OO Schur residual. -/
theorem p4Q2OP_actualDepthTwo_fullGI_injective_iff_exists_actualThirdRow
    (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OO_depthTwoLeadingMinor (M 2 e z) (M 2 e' z') ≠ 0) :
    Function.Injective (Full 2) ↔
      ∃ e'' : Link, ∃ z'' : Pair,
        M 2 e'' z''
          (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) ≠ 0 := by
  let r := p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')
  have hr : r ≠ 0 :=
    p4Q2OO_depthTwoSchurResidual_ne_zero_of_leadingMinor
      (M 2 e z) (M 2 e' z') hMinor
  constructor
  · intro hInj
    have hFullNe : Full 2 r ≠ 0 := by
      intro hZero
      apply hr
      apply hInj
      simpa only [map_zero] using hZero
    by_contra hNo
    push Not at hNo
    have hFullZero : Full 2 r = 0 := by
      funext link
      apply ContinuousMap.ext
      intro context
      have h := hNo link context
      simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
        Pi.zero_apply, ContinuousMap.zero_apply] using h
    exact hFullNe hFullZero
  · rintro ⟨e'', z'', hThird⟩
    intro a b hab
    have hDiffZero : Full 2 (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    obtain ⟨c, hCoeff⟩ :=
      p4Q2OP_actualDepthTwo_fullGI_kernel_le_schurLine
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n e e' z z' hMinor (a - b) hDiffZero
    have hAtThird := congrArg
      (fun g : Link → C(Pair, ℝ) => g e'' z'') hDiffZero
    have hThirdZero : M 2 e'' z'' (a - b) = 0 := by
      simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
        Pi.zero_apply, ContinuousMap.zero_apply] using hAtThird
    have hProductZero : c * M 2 e'' z'' r = 0 := by
      simpa only [hCoeff, map_smul, smul_eq_mul] using hThirdZero
    have hcZero : c = 0 :=
      (mul_eq_zero.mp hProductZero).resolve_right hThird
    have hDiff : a - b = 0 := by
      simp only [hCoeff, hcZero, zero_smul]
    exact sub_eq_zero.mp hDiff

/-- A genuinely nonzero THIRD original Wilson GI response would
force BOTH full signed GI separation AND original physical Hilbert
source injectivity (since ker S ≤ ker Full). Conditional on the
actual physical nonzero response, never on an artificial rank. -/
theorem p4Q2OP_actualDepthTwo_actualThirdGI_nonzero_implies_bothInjective
    (e e' e'' : Link) (z z' z'' : Pair)
    (hMinor : p4Q2OO_depthTwoLeadingMinor (M 2 e z) (M 2 e' z') ≠ 0)
    (hThird :
      M 2 e'' z''
        (p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) ≠ 0) :
    Function.Injective (Full 2) ∧ Function.Injective (S 2) := by
  have hPhi : Function.Injective (Full 2) :=
    (p4Q2OP_actualDepthTwo_fullGI_injective_iff_exists_actualThirdRow
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e e' z z' hMinor).mpr ⟨e'', z'', hThird⟩
  refine ⟨hPhi, ?_⟩
  intro a b hab
  apply hPhi
  have hDiffSource : S 2 (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hDiffFull : Full 2 (a - b) = 0 :=
    (LinearMap.mem_ker).mp
      ((p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 2) ((LinearMap.mem_ker).mpr hDiffSource))
  exact sub_eq_zero.mp (by
    simpa only [map_sub] using hDiffFull)

/-- UNCONDITIONAL original-Wilson finite-H small-positive-fine theorem:
the actual depth-two physical coefficient kernel AND the full
two-posterior GI kernel are confined to the SAME ONE-DIMENSIONAL
Schur line. Their potential nontriviality is precisely the
third-mode physics left open after ON, not an unrestricted
two-dimensional unidentified GI/source obstruction. -/
theorem p4Q2OP_actualDepthTwo_smallFine_bothKernels_containedInSchurLine
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ z z' : Pair, ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        (∀ a : Fin (2 + 1) → ℝ,
          Full 2 a = 0 →
            ∃ c : ℝ,
              a = c •
                p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z')) ∧
        (∀ a : Fin (2 + 1) → ℝ,
          S 2 a = 0 →
            ∃ c : ℝ,
              a = c •
                p4Q2OO_depthTwoSchurResidual (M 2 e z) (M 2 e' z'))) := by
  obtain ⟨z, z', delta, hDelta, hSmall⟩ :=
    p4Q2OO_actualDepthTwo_exists_nonzeroLeadingMinor_smallFine
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨z, z', delta, hDelta, ?_⟩
  intro ht hlt
  have hMinor := hSmall ht hlt
  constructor
  · intro a hZero
    exact p4Q2OP_actualDepthTwo_fullGI_kernel_le_schurLine
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e e' z z' hMinor a hZero
  · intro a hZero
    exact p4Q2OP_actualDepthTwo_physicalSource_kernel_le_schurLine
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e e' z z' hMinor a hZero

end ActualWilsonPhysicalDepthTwo
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OP_twoRows_null_scaledSchur
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OP_twoRows_commonKernel_iff_schurLine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OP_actualDepthTwo_twoOriginalGIrows_kernel_iff_schurLine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OP_actualDepthTwo_fullGI_kernel_le_schurLine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OP_actualDepthTwo_physicalSource_kernel_le_schurLine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OP_actualDepthTwo_physicalSource_injective_iff_schurNonzero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OP_actualDepthTwo_fullGI_injective_iff_exists_actualThirdRow
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OP_actualDepthTwo_actualThirdGI_nonzero_implies_bothInjective
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OP_actualDepthTwo_smallFine_bothKernels_containedInSchurLine
