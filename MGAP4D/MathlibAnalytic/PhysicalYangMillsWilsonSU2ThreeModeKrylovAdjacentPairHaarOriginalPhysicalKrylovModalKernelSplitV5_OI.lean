import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalOneRowAllDepthModalRankOpenV5_OH
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualGIContinuousDetectorComplementFrameV5_HJ
import Mathlib.Tactic

/-!
# P4-Q2-OI — exact original physical source splitting along a genuine GI receiver

OH chooses ONE original interacting-Wilson signed GI modal detector
row and ONE true physical context independent of ALL finite Krylov
depths at any fixed scale n. Its literal zero-selector response is
nonzero and obeys the same original Q_GI/N_H positive coefficient;
the scalar detector's actual coefficient kernel has finrank r.

OI uses only this already-proved true physical nonzero anchor and
mathlib linearity to construct, for every genuine finite right-Krylov
coefficient a, the exact real coefficient-space decomposition

  a = k_r(a) + t_r(a) * a0_r,
  t_r(a) = Phi_r(a) / Phi_r(a0_r),
  Phi_r(k_r(a)) = 0,

for the unchanged original source-dependent two-Wilson-posterior
GI modal functional Phi_r (HF). The ratio denominator is NONZERO
at the selected real Wilson physical context by OH, without
adding an injectivity/rank assumption.

The ACTUAL right-Krylov Gauss-law physical source synthesis S (HJ)
then satisfies the precise Hilbert-space equality

  S_r(a) = S_r(k_r(a)) + t_r(a) * U,

because the true zero-selector source is exactly the physical unit U
at every finite r and every genuine nonnegative fine coupling (GX/OF).
The original interacting two-posterior GI gap AND OD's exact signed
FF receiver of S_r(k_r(a)) vanish at that ONE physical row/context.

This identifies the concrete high-depth physical-source obstruction:
the remainder S_r(k_r(a)) is undetected at that single row, but can
be nonzero or detected at other original contexts. It is NOT proved
to be an invisible PHYSICAL source in the global HJ kernel.
No all-coefficient injectivity or zero-invisible-sector assumption,
Dobrushin, independent Haar law, sorry, admit or new axiom.
No uniform H/n/r floor, single endpoint across scales, H1-C3,
semigroup or continuum 4d Yang-Mills mass gap follows.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OI_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OI_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OI_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OI_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OI_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section ActualKrylovSplit
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
local notation "L" => p4Q2OD_originalTwoPosteriorContrastCLM
  Hn (beta n) (hbeta n)
local notation "Fiber" => p4Q2OD_originalPhysicalSignedReceiverFiber
  Hn (beta n) (hbeta n)

/-- REAL remainder of the actual signed right-Krylov source
coefficients after extracting the detected zero-selector direction
using the literal original HF modal GI functional. The denominator
is used only in results where OH proves it nonzero. -/
noncomputable def p4Q2OI_originalKrylovModalReceiverRemainder
    (r : ℕ) (e : Link) (z : Cfg × Cfg)
    (a : Fin (r + 1) → ℝ) : Fin (r + 1) → ℝ :=
  a - (M r e z a / M r e z (Zero r)) • Zero r

/-- True original modal GI functional kills the explicit normalized
coefficient remainder; no assumption about the image of any higher
physical source or any continuum spectral gap is involved. -/
theorem p4Q2OI_originalKrylovModalRemainder_GI_zero
    (r : ℕ) (e : Link) (z : Cfg × Cfg)
    (hZeroSelector : M r e z (Zero r) ≠ 0)
    (a : Fin (r + 1) → ℝ) :
    M r e z
      (p4Q2OI_originalKrylovModalReceiverRemainder
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z a) = 0 := by
  unfold p4Q2OI_originalKrylovModalReceiverRemainder
  rw [map_sub, map_smul, smul_eq_mul,
    div_mul_cancel₀ _ hZeroSelector, sub_self]

/-- Exact zero-selector plus single-row original modal kernel
decomposition of arbitrary true fine-right Krylov COEFFICIENTS. -/
theorem p4Q2OI_originalKrylovModal_coefficient_split
    (r : ℕ) (e : Link) (z : Cfg × Cfg)
    (a : Fin (r + 1) → ℝ) :
    a =
      p4Q2OI_originalKrylovModalReceiverRemainder
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z a +
      (M r e z a / M r e z (Zero r)) • Zero r := by
  change a =
    (a - (M r e z a / M r e z (Zero r)) • Zero r) +
      (M r e z a / M r e z (Zero r)) • Zero r
  exact (sub_add_cancel a _).symm

/-- ACTUAL physical source equality in the unchanged Gauss-law
Hilbert submodule. The rightmost source is the existing true U,
because GX proves S_r(a0_r) = U for any nonnegative fine beta. -/
theorem p4Q2OI_originalPhysicalKrylovSource_split
    (r : ℕ) (e : Link) (z : Cfg × Cfg)
    (a : Fin (r + 1) → ℝ) :
    S r a =
      S r (p4Q2OI_originalKrylovModalReceiverRemainder
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z a) +
      (M r e z a / M r e z (Zero r)) • U := by
  have hUnit : S r (Zero r) = U := by
    change (∑ j : Fin (r + 1),
      Zero r j •
        physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ)) = U
    exact p4Q2GX_actualRightCoefficientSource_eq_physicalUnit
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r
  let k : Fin (r + 1) → ℝ :=
    p4Q2OI_originalKrylovModalReceiverRemainder
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z a
  let t : ℝ := M r e z a / M r e z (Zero r)
  have hCoeff : a = k + t • Zero r :=
    p4Q2OI_originalKrylovModal_coefficient_split
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z a
  calc
    S r a = S r (k + t • Zero r) := congrArg (S r) hCoeff
    _ = S r k + t • S r (Zero r) := by rw [map_add, map_smul]
    _ = S r k + t • U := by rw [hUnit]

/-- The physical source synthesized from the modal kernel remainder
has zero ORIGINAL two-interacting-posterior GI expectation gap at
the SAME chosen link/context, by HF's exact original GI modal
linearity. This does not imply detection vanishes at OTHER contexts. -/
theorem p4Q2OI_originalPhysicalKrylovRemainder_GI_zero
    (r : ℕ) (e : Link) (z : Cfg × Cfg)
    (hZeroSelector : M r e z (Zero r) ≠ 0)
    (a : Fin (r + 1) → ℝ) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n)
      (S r (p4Q2OI_originalKrylovModalReceiverRemainder
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z a)) e z = 0 := by
  rw [p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r (p4Q2OI_originalKrylovModalReceiverRemainder
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z a) e z]
  exact p4Q2OI_originalKrylovModalRemainder_GI_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r e z hZeroSelector a

/-- Same source-dependent physical remainder is killed by the TRUE
original two-posterior signed density difference L_D applied to
the unchanged FF physical receiver fiber R_f at that ONE context.
This is an exact OD intertwining consequence, not a new posterior. -/
theorem p4Q2OI_originalPhysicalKrylovRemainder_signedReceiver_zero
    (r : ℕ) (e : Link) (z : Cfg × Cfg)
    (hZeroSelector : M r e z (Zero r) ≠ 0)
    (a : Fin (r + 1) → ℝ) :
    L z.2 e
      (Fiber (S r (p4Q2OI_originalKrylovModalReceiverRemainder
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z a)) e z) = 0 := by
  rw [← p4Q2OD_originalPhysicalGI_eq_truePosteriorSignedFunctional]
  exact p4Q2OI_originalPhysicalKrylovRemainder_GI_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r e z hZeroSelector a

/-- At each fixed n and two actual physical links with frozen
beta(n)>0, one genuine Wilson context and receiver ROW is selected
ONCE for ALL depths. Every real physical right-Krylov source at
EVERY finite depth is the sum of the truly receiver-invisible-at-
THIS-ROW remainder and an explicit scalar multiple of the same U.
The scalar source decomposition is exact in the actual HJ physical
Gauss-law Hilbert submodule; it does not identify the remainder with
globally invisible physical subspaces or prove any endpoint gap. -/
theorem p4Q2OI_originalSameContext_oneRow_allDepth_physicalSourceSplit
    (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      ((∀ r : ℕ, M r e z (Zero r) ≠ 0 ∧
          ∀ a : Fin (r + 1) → ℝ,
            L z.2 e (Fiber
              (S r (p4Q2OI_originalKrylovModalReceiverRemainder
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r e z a)) e z) = 0 ∧
            S r a =
              S r (p4Q2OI_originalKrylovModalReceiverRemainder
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r e z a) +
              (M r e z a / M r e z (Zero r)) • U) ∨
       (∀ r : ℕ, M r e' z' (Zero r) ≠ 0 ∧
          ∀ a : Fin (r + 1) → ℝ,
            L z'.2 e' (Fiber
              (S r (p4Q2OI_originalKrylovModalReceiverRemainder
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r e' z' a)) e' z') = 0 ∧
            S r a =
              S r (p4Q2OI_originalKrylovModalReceiverRemainder
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r e' z' a) +
              (M r e' z' a / M r e' z' (Zero r)) • U)) := by
  obtain ⟨z, z', hRows⟩ :=
    p4Q2OH_originalOneRow_exists_allDepth_sameContext_kernelFinrank
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨z, z', ?_⟩
  rcases hRows with hLeft | hRight
  · left
    intro r
    refine ⟨(hLeft r).1, ?_⟩
    intro a
    exact ⟨
      p4Q2OI_originalPhysicalKrylovRemainder_signedReceiver_zero
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z (hLeft r).1 a,
      p4Q2OI_originalPhysicalKrylovSource_split
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z a⟩
  · right
    intro r
    refine ⟨(hRight r).1, ?_⟩
    intro a
    exact ⟨
      p4Q2OI_originalPhysicalKrylovRemainder_signedReceiver_zero
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e' z' (hRight r).1 a,
      p4Q2OI_originalPhysicalKrylovSource_split
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e' z' a⟩

end ActualKrylovSplit
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OI_originalKrylovModalRemainder_GI_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OI_originalKrylovModal_coefficient_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OI_originalPhysicalKrylovSource_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OI_originalPhysicalKrylovRemainder_GI_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OI_originalPhysicalKrylovRemainder_signedReceiver_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OI_originalSameContext_oneRow_allDepth_physicalSourceSplit
