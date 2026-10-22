import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalKrylovModalKernelSplitV5_OI
import Mathlib.Tactic

/-!
# P4-Q2-OJ — genuine cross-context Wilson minors and physical Krylov residuals

OI splits each actual right-Krylov coefficient into the genuine selected
one-row null remainder and a detected physical U component. OJ evaluates
THAT SAME residual at any OTHER genuine original interacting-Wilson
link and boundary context, without altering its physical source.

The exact two-row minor
  Phi(e,z)(a0) * Phi(e',z')(a) - Phi(e,z)(a) * Phi(e',z')(a0)
equals the nonzero anchor response times the other genuine receiver
of OI's physical remainder. Via OD this is the same true signed
two-posterior FF receiver of an actual Gauss-law physical source.

All minors vanish if and only if the OI remainder belongs to the full
HJ continuous GI detector kernel. A nonzero cross-context minor,
if independently demonstrated, certifies a NONZERO physical residual
detected by the real second Wilson context. No nonzero minor is assumed
or asserted. The physical synthesis kernel is contained in the global
GI detector kernel, which is contained in any chosen single-row kernel.

No positive-fine all-source separation, volume/scale-uniform floor,
cross-scale endpoint, strong limit, or continuum mass gap is proved.
There is no independent Haar posterior, artificial rank hypothesis,
Dobrushin argument, sorry, admit, or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OJ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OJ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OJ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OJ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OJ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

private theorem p4Q2OJ_real_cross_minor_identity
    (a b c d : ℝ) (hb : b ≠ 0) :
    b * (d - (a / b) * c) = b * d - a * c := by
  calc
    b * (d - (a / b) * c) =
        b * d - ((a / b) * b) * c := by ring
    _ = b * d - a * c := by rw [div_mul_cancel₀ a hb]

section ActualCrossContext
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "Zero" => p4Q2GX_rightZeroCoefficient
local notation "M" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "P" => p4Q2HJ_actualRightGIContinuousDetector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "R" => p4Q2OI_originalKrylovModalReceiverRemainder
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "L" => p4Q2OD_originalTwoPosteriorContrastCLM
  Hn (beta n) (hbeta n)
local notation "Fiber" => p4Q2OD_originalPhysicalSignedReceiverFiber
  Hn (beta n) (hbeta n)

/-- The literal two-row determinant of TWO genuine source-weighted
Wilson GI receiver functionals on a0 and any actual Krylov coefficient.
The row (e,z) is the one fixed by OH; (e',z') may be any other real
spatial link and original two-posterior boundary context. -/
noncomputable def p4Q2OJ_originalCrossContextModalMinor
    (r : ℕ) (e e' : Link) (z z' : Cfg × Cfg)
    (a : Fin (r + 1) → ℝ) : ℝ :=
  M r e z (Zero r) * M r e' z' a -
    M r e z a * M r e' z' (Zero r)

/-- Exact cross-context residual identity on the ACTUAL signed Krylov
coefficient space. It uses the OI nonzero original Wilson anchor,
not an assumed independent family of physical right-Krylov modes. -/
theorem p4Q2OJ_originalCrossContextMinor_eq_anchor_mul_remainder
    (r : ℕ) (e e' : Link) (z z' : Cfg × Cfg)
    (hAnchor : M r e z (Zero r) ≠ 0)
    (a : Fin (r + 1) → ℝ) :
    p4Q2OJ_originalCrossContextModalMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e e' z z' a =
    M r e z (Zero r) * M r e' z' (R r e z a) := by
  unfold p4Q2OJ_originalCrossContextModalMinor
    p4Q2OI_originalKrylovModalReceiverRemainder
  rw [map_sub, map_smul, smul_eq_mul]
  exact (p4Q2OJ_real_cross_minor_identity
    (M r e z a) (M r e z (Zero r)) (M r e' z' (Zero r))
    (M r e' z' a) hAnchor).symm

/-- The cross-context minor is precisely the genuine OD signed
two-interacting-Wilson posterior functional evaluated on the unchanged
FF receiver fiber of the ACTUAL HJ physical source S(R(a)).
This does NOT assert the minor is nonzero. -/
theorem p4Q2OJ_originalCrossContextMinor_eq_signedPhysicalResidual
    (r : ℕ) (e e' : Link) (z z' : Cfg × Cfg)
    (hAnchor : M r e z (Zero r) ≠ 0)
    (a : Fin (r + 1) → ℝ) :
    p4Q2OJ_originalCrossContextModalMinor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e e' z z' a =
    M r e z (Zero r) *
      L z'.2 e' (Fiber (S r (R r e z a)) e' z') := by
  calc
    p4Q2OJ_originalCrossContextModalMinor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e e' z z' a =
      M r e z (Zero r) * M r e' z' (R r e z a) :=
        p4Q2OJ_originalCrossContextMinor_eq_anchor_mul_remainder
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r e e' z z' hAnchor a
    _ = M r e z (Zero r) *
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n) (S r (R r e z a)) e' z' := by
      rw [p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r (R r e z a) e' z']
    _ = M r e z (Zero r) *
        L z'.2 e' (Fiber (S r (R r e z a)) e' z') := by
      rw [p4Q2OD_originalPhysicalGI_eq_truePosteriorSignedFunctional]

/-- Genuine obstruction criterion: ALL original cross-context minors
vanish exactly when the EXPLICIT OI one-row physical remainder lies
in HJ's WHOLE-LINK / WHOLE-BOUNDARY continuous GI detector kernel.
This is not a claim that S(R(a)) vanishes. -/
theorem p4Q2OJ_allCrossMinors_zero_iff_residual_fullGIKernel
    (r : ℕ) (e : Link) (z : Cfg × Cfg)
    (hAnchor : M r e z (Zero r) ≠ 0)
    (a : Fin (r + 1) → ℝ) :
    (∀ e' : Link, ∀ z' : Cfg × Cfg,
      p4Q2OJ_originalCrossContextModalMinor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e e' z z' a = 0) ↔
      R r e z a ∈ (P r).ker := by
  constructor
  · intro hAll
    apply (LinearMap.mem_ker).mpr
    funext e'
    apply ContinuousMap.ext
    intro z'
    change M r e' z' (R r e z a) = 0
    have hMul : M r e z (Zero r) * M r e' z' (R r e z a) = 0 := by
      rw [← p4Q2OJ_originalCrossContextMinor_eq_anchor_mul_remainder
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e e' z z' hAnchor a]
      exact hAll e' z'
    exact (mul_eq_zero.mp hMul).resolve_left hAnchor
  · intro hKer e' z'
    have hAll : P r (R r e z a) = 0 := (LinearMap.mem_ker).mp hKer
    have hValue : M r e' z' (R r e z a) = 0 := by
      have h := congrArg (fun v : Link → C(Cfg × Cfg, ℝ) => v e' z') hAll
      simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
        Pi.zero_apply, ContinuousMap.zero_apply] using h
    rw [p4Q2OJ_originalCrossContextMinor_eq_anchor_mul_remainder
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e e' z z' hAnchor a, hValue, mul_zero]

/-- Precise relation between the HJ whole-context GI kernel and the
selected original Wilson one-row kernel. The extra, independent
obstruction is the family of ACTUAL two-row minors, not a rank axiom. -/
theorem p4Q2OJ_fullGIKernel_iff_anchor_zero_and_crossMinors_zero
    (r : ℕ) (e : Link) (z : Cfg × Cfg)
    (hAnchor : M r e z (Zero r) ≠ 0)
    (a : Fin (r + 1) → ℝ) :
    a ∈ (P r).ker ↔
      M r e z a = 0 ∧
      ∀ e' : Link, ∀ z' : Cfg × Cfg,
        p4Q2OJ_originalCrossContextModalMinor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r e e' z z' a = 0 := by
  have hCriterion :=
    p4Q2OJ_allCrossMinors_zero_iff_residual_fullGIKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z hAnchor a
  constructor
  · intro hGlobal
    have hValue : M r e z a = 0 := by
      have hFull : P r a = 0 := (LinearMap.mem_ker).mp hGlobal
      have h := congrArg (fun v : Link → C(Cfg × Cfg, ℝ) => v e z) hFull
      simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
        Pi.zero_apply, ContinuousMap.zero_apply] using h
    have hRemainder : R r e z a = a := by
      unfold p4Q2OI_originalKrylovModalReceiverRemainder
      simp [hValue]
    refine ⟨hValue, ?_⟩
    apply hCriterion.mpr
    simpa only [hRemainder] using hGlobal
  · rintro ⟨hValue, hMinors⟩
    have hRemainder : R r e z a = a := by
      unfold p4Q2OI_originalKrylovModalReceiverRemainder
      simp [hValue]
    have hGlobal := hCriterion.mp hMinors
    simpa only [hRemainder] using hGlobal

/-- Actual physical source synthesis kernel is contained in the
full Wilson GI detector kernel, which is contained in the
selected genuine one-row modal detector kernel. Neither inclusion
is silently reversed. -/
theorem p4Q2OJ_originalPhysical_fullGI_singleRow_kernel_chain
    (r : ℕ) (e : Link) (z : Cfg × Cfg) :
    (S r).ker ≤ (P r).ker ∧ (P r).ker ≤ (M r e z).ker := by
  refine ⟨p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r, ?_⟩
  intro a hKer
  have hAll : P r a = 0 := (LinearMap.mem_ker).mp hKer
  have h := congrArg (fun v : Link → C(Cfg × Cfg, ℝ) => v e z) hAll
  apply (LinearMap.mem_ker).mpr
  simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
    Pi.zero_apply, ContinuousMap.zero_apply] using h

/-- A *proved* nonzero genuine cross-context minor, whenever
available, would certify that the explicit OI remainder synthesizes
a NONZERO actual physical Gauss-law Hilbert source and is detected by
the OTHER original interacting-posterior signed receiver.
No such nonzero minor is assumed to exist in this theorem. -/
theorem p4Q2OJ_nonzeroCrossMinor_implies_nonzeroPhysical_detected
    (r : ℕ) (e e' : Link) (z z' : Cfg × Cfg)
    (hAnchor : M r e z (Zero r) ≠ 0)
    (a : Fin (r + 1) → ℝ)
    (hMinor :
      p4Q2OJ_originalCrossContextModalMinor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e e' z z' a ≠ 0) :
    S r (R r e z a) ≠ 0 ∧
      L z'.2 e' (Fiber (S r (R r e z a)) e' z') ≠ 0 := by
  have hSigned :
      L z'.2 e' (Fiber (S r (R r e z a)) e' z') ≠ 0 := by
    intro hZero
    apply hMinor
    rw [p4Q2OJ_originalCrossContextMinor_eq_signedPhysicalResidual
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e e' z z' hAnchor a, hZero, mul_zero]
  have hPhysical : S r (R r e z a) ≠ 0 := by
    intro hZero
    have hSourceKer : R r e z a ∈ (S r).ker :=
      (LinearMap.mem_ker).mpr hZero
    have hGlobalKer : R r e z a ∈ (P r).ker :=
      (p4Q2OJ_originalPhysical_fullGI_singleRow_kernel_chain
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z).1 hSourceKer
    have hAllMinors :=
      (p4Q2OJ_allCrossMinors_zero_iff_residual_fullGIKernel
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z hAnchor a).mpr hGlobalKer
    exact hMinor (hAllMinors e' z')
  exact ⟨hPhysical, hSigned⟩

/-- Quantitative extraction of the original physical U-component
coefficient t=Phi(a)/Phi(a0): ANY genuine lower bound for the
detected OI/OH anchor square transports to a lower bound for the
actual receiver square on an arbitrary coefficient a. The residual
is not controlled by this one-row inequality. -/
theorem p4Q2OJ_originalModal_anchorFloor_controls_U_coefficient
    (r : ℕ) (e : Link) (z : Cfg × Cfg)
    (hAnchor : M r e z (Zero r) ≠ 0)
    (c : ℝ) (hFloor : c ≤ (M r e z (Zero r))^2)
    (a : Fin (r + 1) → ℝ) :
    c * (M r e z a / M r e z (Zero r))^2 ≤
      (M r e z a)^2 := by
  have hScale :
      (M r e z a / M r e z (Zero r)) * M r e z (Zero r) =
        M r e z a := div_mul_cancel₀ _ hAnchor
  calc
    c * (M r e z a / M r e z (Zero r))^2 ≤
        (M r e z (Zero r))^2 *
          (M r e z a / M r e z (Zero r))^2 :=
      mul_le_mul_of_nonneg_right hFloor (sq_nonneg _)
    _ = ((M r e z a / M r e z (Zero r)) *
        M r e z (Zero r))^2 := by ring
    _ = (M r e z a)^2 := by rw [hScale]

end ActualCrossContext
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OJ_originalCrossContextModalMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OJ_originalCrossContextMinor_eq_anchor_mul_remainder
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OJ_originalCrossContextMinor_eq_signedPhysicalResidual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OJ_allCrossMinors_zero_iff_residual_fullGIKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OJ_fullGIKernel_iff_anchor_zero_and_crossMinors_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OJ_originalPhysical_fullGI_singleRow_kernel_chain
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OJ_nonzeroCrossMinor_implies_nonzeroPhysical_detected
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OJ_originalModal_anchorFloor_controls_U_coefficient
