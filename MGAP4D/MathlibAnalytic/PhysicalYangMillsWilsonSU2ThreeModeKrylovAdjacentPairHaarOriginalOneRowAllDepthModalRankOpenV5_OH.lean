import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalZeroSelectorAllDepthSameContextGIFrameV5_OG
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIJointModalKernelAndHaarDetectionV5_HG
import Mathlib.Tactic

/-!
# P4-Q2-OH — one genuine Wilson physical receiver row, all-depth rank and stability

OG proves that a SAME pair of original interacting Wilson contexts
z,z' works at each fixed physical scale n and at EVERY finite Krylov
depth r for the ACTUAL zero-selector coefficient, with the SAME
true Q_GI/N_H positive two-row signed GI modal response floor.

OH chooses ONE of those two existing genuine GI receiver rows at
depth zero and proves the SAME ROW remains positively detected with
at least HALF the actual OE Q_GI/N_H lower coefficient at ALL depths.
The row and context are selected ONCE before the universal r, not
an artificial r-dependent row or a surrogate receiver.

At this very same row OH proves, for EVERY finite Krylov depth r:
  (1) the true HF source-coefficient GI modal map is surjective to R;
  (2) its actual coefficient-space kernel has EXACT finrank r,
      by HF's original physical zero-mode nonzero theorem;
  (3) there is a real positive-radius open coefficient ball around
      the real canonical physical zero-selector on which the SAME
      true two-interacting-posterior row remains nonzero.
The local positive radius may depend on r. The kernel dimension r
makes explicit why a single real context cannot certify all
physical Krylov coefficient directions as nonzero at r>0;
a nonzero COEFFICIENT in this kernel need not be a nonzero physical
source, so no physical invisible-sector claim is inferred.

Original two interacting Wilson posterior laws, Gauss-law physical
source, full FF receiver and Perron half-density, spatial/temporal
interactions and frozen/fine coupling distinction are unchanged.
No artificial rank assumption, independent-Haar posterior, Dobrushin,
sorry/admit or new axiom. Volume-uniform U0, cross-scale endpoint,
all-coefficient positive-fine injectivity, H1-C3 and mass gap remain OPEN.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OH_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OH_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OH_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OH_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OH_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section ActualOneRowAllDepth
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "M" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Zero" => p4Q2GX_rightZeroCoefficient
local notation "N" => (p4Q2LP_originalSpatialPlaquetteCount Hn : ℝ)
local notation "E" => p4Q2LW_originalHarnackContrastScale (beta n)
local notation "Q" => p4Q2LY_originalCompensatedLocalGISquareEnergy
  Hn (beta n) (hbeta n)

/-- The genuine original source-weighted modal GI detector evaluated
on the literal GX zero-selector equals the response of its ORIGINAL
zeroth right-Krylov physical source, not an unrelated Gaussian kernel. -/
theorem p4Q2OH_actualModal_zeroSelector_eq_originalZeroPhysicalGI
    (r : ℕ) (e : Link) (z : Cfg × Cfg) :
    M r e z (Zero r) =
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n 0) e z := by
  change p4Q2GY_modalTransferLinear r
      (fun j : Fin (r + 1) =>
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n) (RightFactor n (j : ℕ)) e z)
      (Zero r) =
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n) (RightFactor n 0) e z
  exact p4Q2GY_modalTransferLinear_anchor r _

/-- The original HF physical GI single-row detector has EXACT
coefficient kernel finrank r if it detects the real physical
zero-selector, relying only on the already proved HF source rank
lemma and the actual modal-to-original-source identity above. -/
theorem p4Q2OH_actualModal_kernel_finrank_of_zeroSelector_detected
    (r : ℕ) (e : Link) (z : Cfg × Cfg)
    (hDetect : M r e z (Zero r) ≠ 0) :
    Module.finrank ℝ ↥(M r e z).ker = r := by
  have hAnchor :
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n 0) e z ≠ 0 := by
    rw [← p4Q2OH_actualModal_zeroSelector_eq_originalZeroPhysicalGI
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z]
    exact hDetect
  exact p4Q2HF_actualRightGI_modalKernel_finrank_of_anchor_ne
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r e z hAnchor

/-- A genuine nonzero source-weighted HF receiver on the canonical
physical zero-selector gives an ACTUAL positive-radius open ball
of signed right-Krylov COEFFICIENTS detected at that very same row.
No bound uniform over r is claimed. -/
theorem p4Q2OH_actualModal_zeroSelector_detected_openBall
    (r : ℕ) (e : Link) (z : Cfg × Cfg)
    (hDetect : M r e z (Zero r) ≠ 0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ a : Fin (r + 1) → ℝ,
        dist a (Zero r) < epsilon → M r e z a ≠ 0 := by
  have hOpen :
      IsOpen {a : Fin (r + 1) → ℝ | M r e z a ≠ 0} :=
    p4Q2HF_actualRightGI_detected_isOpen
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z
  obtain ⟨epsilon, hPos, hBall⟩ :=
    (Metric.isOpen_iff.mp hOpen) (Zero r) hDetect
  refine ⟨epsilon, hPos, ?_⟩
  intro a ha
  exact hBall (Metric.mem_ball.mpr (by simpa only [dist_comm] using ha))

/-- A fixed finite scale n and true Wilson physical links admit one
pair of ACTUAL interacting posterior contexts z,z' and an EXACT
one-half of the original positive Q_GI/N_H lower coefficient on ONE
selected genuine row, working UNIFORMLY IN THE DEPTH INDEX r.
The selection of row and contexts precedes all r. -/
theorem p4Q2OH_originalOneRow_exists_allDepth_sameContext_halfDensityFloor
    (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      0 < Q e e' z z' / N ∧
      ((∀ r : ℕ,
        ((Q e e' z z' / N) / (10 * E^2)) / 2 ≤
          (M r e z (Zero r))^2) ∨
       (∀ r : ℕ,
        ((Q e e' z z' / N) / (10 * E^2)) / 2 ≤
          (M r e' z' (Zero r))^2)) := by
  obtain ⟨z, z', _hN, hQ, hFloor⟩ :=
    p4Q2OG_actualZeroSelector_exists_allDepth_sameContext_modalFloor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  let k : ℝ := (Q e e' z z' / N) / (10 * E^2)
  have hAtZero : k ≤
      (M 0 e z (Zero 0))^2 + (M 0 e' z' (Zero 0))^2 := hFloor 0
  have hHalf :
      k / 2 ≤ (M 0 e z (Zero 0))^2 ∨
        k / 2 ≤ (M 0 e' z' (Zero 0))^2 := by
    by_cases hFirst : k / 2 ≤ (M 0 e z (Zero 0))^2
    · exact Or.inl hFirst
    · right
      have hLess : (M 0 e z (Zero 0))^2 < k / 2 :=
        lt_of_not_ge hFirst
      linarith
  refine ⟨z, z', hQ, ?_⟩
  rcases hHalf with hLeft | hRight
  · left
    intro r
    have hEq := p4Q2OG_originalZeroSelector_modal_depth_independent
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r 0 e z
    change k / 2 ≤ (M r e z (Zero r))^2
    rw [hEq]
    exact hLeft
  · right
    intro r
    have hEq := p4Q2OG_originalZeroSelector_modal_depth_independent
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r 0 e' z'
    change k / 2 ≤ (M r e' z' (Zero r))^2
    rw [hEq]
    exact hRight

/-- A SINGLE real interacting Wilson posterior GI receiver row
selected independently of ALL finite depths has a nonzero true
zero-selector response and an EXACT codimension-one modal kernel
at EVERY depth. In particular the coefficient kernel finrank is r,
not a false zero-dimensional kernel for arbitrary high Krylov modes. -/
theorem p4Q2OH_originalOneRow_exists_allDepth_sameContext_kernelFinrank
    (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      ((∀ r : ℕ,
        M r e z (Zero r) ≠ 0 ∧
          Module.finrank ℝ ↥(M r e z).ker = r) ∨
       (∀ r : ℕ,
        M r e' z' (Zero r) ≠ 0 ∧
          Module.finrank ℝ ↥(M r e' z').ker = r)) := by
  obtain ⟨z, z', hQ, hRows⟩ :=
    p4Q2OH_originalOneRow_exists_allDepth_sameContext_halfDensityFloor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  have hE : 0 < E :=
    p4Q2LW_originalHarnackContrastScale_pos (beta n) hFrozen
  have hSmall : 0 < ((Q e e' z z' / N) / (10 * E^2)) / 2 :=
    div_pos (div_pos hQ
      (mul_pos (by norm_num) (sq_pos_of_pos hE))) (by norm_num)
  refine ⟨z, z', ?_⟩
  rcases hRows with hLeft | hRight
  · left
    intro r
    have hDetect : M r e z (Zero r) ≠ 0 := by
      intro hZero
      have hh : (M r e z (Zero r))^2 = 0 := by simp [hZero]
      have hPos : 0 < (M r e z (Zero r))^2 :=
        lt_of_lt_of_le hSmall (hLeft r)
      exact (ne_of_gt hPos) hh
    exact ⟨hDetect,
      p4Q2OH_actualModal_kernel_finrank_of_zeroSelector_detected
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z hDetect⟩
  · right
    intro r
    have hDetect : M r e' z' (Zero r) ≠ 0 := by
      intro hZero
      have hh : (M r e' z' (Zero r))^2 = 0 := by simp [hZero]
      have hPos : 0 < (M r e' z' (Zero r))^2 :=
        lt_of_lt_of_le hSmall (hRight r)
      exact (ne_of_gt hPos) hh
    exact ⟨hDetect,
      p4Q2OH_actualModal_kernel_finrank_of_zeroSelector_detected
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e' z' hDetect⟩

/-- At the SAME physical link and original Wilson context,
for ALL finite depths r there is a genuine positive local COEFFICIENT
ball around the real right-Krylov zero-selector on which the original
source-weighted signed two-posterior GI modal response is nonzero.
The center and available radius depend on r; the chosen row/context
does NOT. This is compatible with the rank-r kernel at r>0. -/
theorem p4Q2OH_originalOneRow_exists_allDepth_sameContext_openCoefficientBalls
    (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      ((∀ r : ℕ,
        ∃ epsilon : ℝ, 0 < epsilon ∧
          ∀ a : Fin (r + 1) → ℝ,
            dist a (Zero r) < epsilon → M r e z a ≠ 0) ∨
       (∀ r : ℕ,
        ∃ epsilon : ℝ, 0 < epsilon ∧
          ∀ a : Fin (r + 1) → ℝ,
            dist a (Zero r) < epsilon → M r e' z' a ≠ 0)) := by
  obtain ⟨z, z', hRows⟩ :=
    p4Q2OH_originalOneRow_exists_allDepth_sameContext_kernelFinrank
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨z, z', ?_⟩
  rcases hRows with hLeft | hRight
  · left
    intro r
    exact p4Q2OH_actualModal_zeroSelector_detected_openBall
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z (hLeft r).1
  · right
    intro r
    exact p4Q2OH_actualModal_zeroSelector_detected_openBall
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e' z' (hRight r).1

end ActualOneRowAllDepth
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OH_actualModal_zeroSelector_eq_originalZeroPhysicalGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OH_actualModal_kernel_finrank_of_zeroSelector_detected
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OH_actualModal_zeroSelector_detected_openBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OH_originalOneRow_exists_allDepth_sameContext_halfDensityFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OH_originalOneRow_exists_allDepth_sameContext_kernelFinrank
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OH_originalOneRow_exists_allDepth_sameContext_openCoefficientBalls
