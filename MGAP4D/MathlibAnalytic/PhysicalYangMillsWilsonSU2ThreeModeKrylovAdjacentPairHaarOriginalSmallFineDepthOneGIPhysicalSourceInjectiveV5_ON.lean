import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSmallFineKrylovTwoContextMinorV5_OM
import Mathlib.Tactic

/-!
# P4-Q2-ON — exact positive-fine depth-one GI and physical source injectivity

OM has UNCONDITIONALLY constructed genuine original-Wilson two-context
GI nonzero minors for the physical ZERO and FIRST right-Krylov modes
at a sufficiently small positive fine coupling, for every finite
spatial H and every fixed positive frozen coupling.

This file does NOT assume rank or physical source injectivity.
Instead it explicitly solves the ACTUAL 2x2 original GI response
system for arbitrary signed depth-one coefficients, using OM's
already-proved nonzero determinant and the exact actual coefficient
basis. Any coefficient killed by the two genuine original interacting
Wilson GI receiver rows MUST be zero. Therefore the REAL HJ
all-context original GI detector and the REAL HJ Gauss-law physical
source synthesis are both INJECTIVE on the entire depth-one Krylov
coefficient space throughout the same proven small-positive-fine
window. The full physical source coefficient pair U, T_fine U is
therefore genuinely linearly independent and GI-separated.

No all-positive-fine coupling, arbitrary r>1 GI coefficient-frame,
uniform-in-H numerical coercivity U0, common fine/coarse endpoint,
H1-C3 or continuum 4D Yang--Mills mass gap is claimed.

The original Wilson two interacting posteriors, true physical
Gauss-law Hilbert, FF signed receiver, Perron half-density and
distinct frozen/fine Wilson couplings are never altered.
No independent-Haar conditional, artificial rank hypothesis,
Dobrushin, sorry/admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2ON_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2ON_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2ON_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2ON_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2ON_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- An explicit genuine two-column determinant computation gives
a ZERO common kernel for ANY TWO real linear functionals on the
two-dimensional genuine depth-one coefficient space. This theorem
requires only the ACTUAL nonzero determinant, not any assumed rank.
The 0/1 selectors are literally the basis of Fin (1+1)→ℝ. -/
theorem p4Q2ON_abstract_twoRows_commonKernel_eq_zero
    (D D' : (Fin (1 + 1) → ℝ) →ₗ[ℝ] ℝ)
    (hMinor : D (p4Q2GX_rightZeroCoefficient 1) *
          D' p4Q2IS_depthOneCoefficient -
        D p4Q2IS_depthOneCoefficient *
          D' (p4Q2GX_rightZeroCoefficient 1) ≠ 0)
    (a : Fin (1 + 1) → ℝ)
    (hD : D a = 0) (hD' : D' a = 0) :
    a = 0 := by
  let u := p4Q2GX_rightZeroCoefficient 1
  let v := p4Q2IS_depthOneCoefficient
  let det : ℝ := D u * D' v - D v * D' u
  have hdet : det ≠ 0 := hMinor
  obtain ⟨x, y, hxy⟩ := p4Q2IS_depthOne_coeff_decompose a
  have h0 : x * D u + y * D v = 0 := by
    have h := hD
    rw [hxy, map_add, map_smul, map_smul] at h
    simpa only [smul_eq_mul] using h
  have h1 : x * D' u + y * D' v = 0 := by
    have h := hD'
    rw [hxy, map_add, map_smul, map_smul] at h
    simpa only [smul_eq_mul] using h
  have hxProd : x * det = 0 := by
    calc
      x * det =
          (x * D u + y * D v) * D' v -
          (x * D' u + y * D' v) * D v := by ring
      _ = 0 := by rw [h0, h1]; ring
  have hyProd : y * det = 0 := by
    calc
      y * det =
          (x * D' u + y * D' v) * D u -
          (x * D u + y * D v) * D' u := by ring
      _ = 0 := by rw [h1, h0]; ring
  have hx : x = 0 := (mul_eq_zero.mp hxProd).resolve_right hdet
  have hy : y = 0 := (mul_eq_zero.mp hyProd).resolve_right hdet
  calc
    a = x • u + y • v := hxy
    _ = 0 := by rw [hx, hy]; simp

section OriginalTwoPhysicalRows
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "First" => p4Q2IS_depthOneCoefficient
local notation "Zero" => p4Q2GX_rightZeroCoefficient
local notation "M" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Full" => p4Q2HJ_actualRightGIContinuousDetector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n

/-- Any actual nonzero two-context OM/OJ original Wilson GI minor
gives an INJECTIVE pair of true HF physical modal GI receiver rows
on every signed depth-one coefficient vector. -/
theorem p4Q2ON_twoActualWilsonRows_commonKernel_eq_zero
    (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OJ_originalCrossContextModalMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 1 e e' z z' First ≠ 0)
    (a : Fin (1 + 1) → ℝ)
    (h0 : M 1 e z a = 0)
    (h1 : M 1 e' z' a = 0) :
    a = 0 := by
  exact p4Q2ON_abstract_twoRows_commonKernel_eq_zero
    (M 1 e z) (M 1 e' z') hMinor a h0 h1

/-- The HJ complete TRUE two-interacting-Wilson-posterior GI
detector is injective at depth ONE as soon as OM constructs an
actual original nonzero two-context minor. No rank axiom. -/
theorem p4Q2ON_actualDepthOne_fullGIDetector_injective_of_minor
    (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OJ_originalCrossContextModalMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 1 e e' z z' First ≠ 0) :
    Function.Injective (Full 1) := by
  have hKernel (a : Fin (1 + 1) → ℝ) (ha : Full 1 a = 0) :
      a = 0 := by
    have hAt0 := congrArg
      (fun g : Link → C(Pair, ℝ) => g e z) ha
    have hAt1 := congrArg
      (fun g : Link → C(Pair, ℝ) => g e' z') ha
    have h0 : M 1 e z a = 0 := by
      simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
        Pi.zero_apply, ContinuousMap.zero_apply] using hAt0
    have h1 : M 1 e' z' a = 0 := by
      simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
        Pi.zero_apply, ContinuousMap.zero_apply] using hAt1
    exact p4Q2ON_twoActualWilsonRows_commonKernel_eq_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e e' z z' hMinor a h0 h1
  intro a b h
  apply sub_eq_zero.mp
  apply hKernel
  rw [map_sub, h, sub_self]

/-- The ORIGINAL Gauss-law physical Hilbert Krylov synthesis itself
is injective on ALL two-mode coefficient vectors, since HJ
already proves ker S ⊆ ker Full and ON proves the latter trivial.
This is source nondegeneracy, not merely a scalar one-row rank. -/
theorem p4Q2ON_actualDepthOne_physicalSource_injective_of_minor
    (e e' : Link) (z z' : Pair)
    (hMinor : p4Q2OJ_originalCrossContextModalMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 1 e e' z z' First ≠ 0) :
    Function.Injective (S 1) := by
  have hPhi : Function.Injective (Full 1) :=
    p4Q2ON_actualDepthOne_fullGIDetector_injective_of_minor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e e' z z' hMinor
  intro a b hab
  apply hPhi
  have hSource : S 1 (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hInFull : a - b ∈ (Full 1).ker :=
    (p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 1) ((LinearMap.mem_ker).mpr hSource)
  have hZero : Full 1 (a - b) = 0 := (LinearMap.mem_ker).mp hInFull
  have hDiff : Full 1 a - Full 1 b = 0 := by
    simpa only [map_sub] using hZero
  exact sub_eq_zero.mp hDiff

/-- UNCONDITIONAL finite-volume physical theorem: a fixed positive
original frozen coupling produces an actual positive fine Wilson
interval on which both genuine all-context GI and the HJ original
Gauss-law physical source synthesis are INJECTIVE at right-Krylov
depth one. The finite interval depends on volume and frozen physics.
No assumption of independent source modes or rank-two detector. -/
theorem p4Q2ON_actualDepthOne_smallFine_fullGI_and_physicalSource_injective
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        Function.Injective (Full 1) ∧ Function.Injective (S 1)) := by
  obtain ⟨z, z', delta, hdelta, hMinor⟩ :=
    p4Q2OM_actualDepthOne_exists_fixedContexts_smallPositiveFine_minor_ne
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall
  have hDet := hMinor ht hsmall
  exact ⟨
    p4Q2ON_actualDepthOne_fullGIDetector_injective_of_minor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e e' z z' hDet,
    p4Q2ON_actualDepthOne_physicalSource_injective_of_minor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n e e' z z' hDet⟩

end OriginalTwoPhysicalRows
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ON_abstract_twoRows_commonKernel_eq_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ON_twoActualWilsonRows_commonKernel_eq_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ON_actualDepthOne_fullGIDetector_injective_of_minor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ON_actualDepthOne_physicalSource_injective_of_minor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ON_actualDepthOne_smallFine_fullGI_and_physicalSource_injective
