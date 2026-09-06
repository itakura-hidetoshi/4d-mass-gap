import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEightColorHeatBathBoundedColorBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 1000000

/-- Pythagoras for a self-adjoint idempotent continuous linear endomorphism of a
real Hilbert space.  This formulation avoids introducing any new projection
structure: the two algebraic facts already proved for the Wilson color blocks
are exactly the inputs needed below. -/
theorem realHilbertProjection_residual_norm_sq
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : E →L[ℝ] E)
    (hIdem : P.comp P = P)
    (hSymm : ∀ x y : E, inner ℝ (P x) y = inner ℝ x (P y))
    (x : E) :
    ‖x - P x‖ ^ 2 = ‖x‖ ^ 2 - ‖P x‖ ^ 2 := by
  have hIdemApply : P (P x) = P x := by
    have h := congrArg (fun Q : E →L[ℝ] E => Q x) hIdem
    simpa using h
  have hxxP : inner ℝ x (P x) = ‖P x‖ ^ 2 := by
    have h := hSymm x (P x)
    rw [hIdemApply] at h
    rw [real_inner_self_eq_norm_sq] at h
    exact h.symm
  have hPxx : inner ℝ (P x) x = ‖P x‖ ^ 2 := by
    rw [real_inner_comm]
    exact hxxP
  calc
    ‖x - P x‖ ^ 2 = inner ℝ (x - P x) (x - P x) := by
      simpa using (real_inner_self_eq_norm_sq (x - P x)).symm
    _ = ‖x‖ ^ 2 - ‖P x‖ ^ 2 := by
      simp only [inner_sub_left, inner_sub_right]
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hPxx]
      ring

/-- Ordered finite composition of a family of continuous linear endomorphisms.
The head operator acts first.  No commutativity between different colors is
assumed. -/
noncomputable def realHilbertProjectionSweep
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E) :
    List C → E →L[ℝ] E
  | [] => ContinuousLinearMap.id ℝ E
  | c :: cs => (realHilbertProjectionSweep P cs).comp (P c)

/-- Sum of the successive squared projection defects encountered along an
ordered finite sweep. -/
def realHilbertProjectionSweepPathLoss
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E) :
    List C → E → ℝ
  | [], _ => 0
  | c :: cs, x =>
      ‖x - P c x‖ ^ 2 +
        realHilbertProjectionSweepPathLoss P cs (P c x)

/-- The path loss of any finite sweep is nonnegative. -/
theorem realHilbertProjectionSweepPathLoss_nonneg
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (cs : List C) (x : E) :
    0 ≤ realHilbertProjectionSweepPathLoss P cs x := by
  induction cs generalizing x with
  | nil => simp [realHilbertProjectionSweepPathLoss]
  | cons c cs ih =>
      simp only [realHilbertProjectionSweepPathLoss]
      exact add_nonneg (sq_nonneg _) (ih (P c x))

/-- For a finite sequence of self-adjoint idempotents, the total squared-norm
loss of the ordered composition is exactly the sum of the successive squared
projection defects.  Different projections need not commute. -/
theorem realHilbertProjectionSweep_norm_sq_loss
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hSymm : ∀ (c : C) (x y : E),
      inner ℝ (P c x) y = inner ℝ x (P c y))
    (cs : List C) (x : E) :
    ‖x‖ ^ 2 - ‖realHilbertProjectionSweep P cs x‖ ^ 2 =
      realHilbertProjectionSweepPathLoss P cs x := by
  induction cs generalizing x with
  | nil => simp [realHilbertProjectionSweep, realHilbertProjectionSweepPathLoss]
  | cons c cs ih =>
      simp only [realHilbertProjectionSweep, ContinuousLinearMap.comp_apply,
        realHilbertProjectionSweepPathLoss]
      have hres :=
        realHilbertProjection_residual_norm_sq
          (P c) (hIdem c) (hSymm c) x
      have htail := ih (P c x)
      calc
        ‖x‖ ^ 2 - ‖realHilbertProjectionSweep P cs (P c x)‖ ^ 2 =
            (‖x‖ ^ 2 - ‖P c x‖ ^ 2) +
              (‖P c x‖ ^ 2 -
                ‖realHilbertProjectionSweep P cs (P c x)‖ ^ 2) := by ring
        _ = ‖x - P c x‖ ^ 2 +
              realHilbertProjectionSweepPathLoss P cs (P c x) := by
          rw [← hres, htail]

/-- An ordered sweep of self-adjoint idempotents fixes a vector exactly when
every projection occurring in the sweep fixes that original vector.  The
forward implication is obtained from the exact telescoping loss, not from any
cross-projection commutativity. -/
theorem realHilbertProjectionSweep_apply_eq_self_iff_forall_mem_fixed
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hSymm : ∀ (c : C) (x y : E),
      inner ℝ (P c x) y = inner ℝ x (P c y))
    (cs : List C) (x : E) :
    realHilbertProjectionSweep P cs x = x ↔
      ∀ c ∈ cs, P c x = x := by
  induction cs generalizing x with
  | nil => simp [realHilbertProjectionSweep]
  | cons c cs ih =>
      constructor
      · intro hSweep
        have hLoss :=
          realHilbertProjectionSweep_norm_sq_loss P hIdem hSymm (c :: cs) x
        have hPathZero :
            realHilbertProjectionSweepPathLoss P (c :: cs) x = 0 := by
          rw [hSweep] at hLoss
          linarith
        have hTailNonneg :=
          realHilbertProjectionSweepPathLoss_nonneg P cs (P c x)
        have hResidualZero : ‖x - P c x‖ ^ 2 = 0 := by
          simp only [realHilbertProjectionSweepPathLoss] at hPathZero
          nlinarith [sq_nonneg ‖x - P c x‖]
        have hResidualNorm : ‖x - P c x‖ = 0 := by
          nlinarith [norm_nonneg (x - P c x)]
        have hc : P c x = x := by
          have hz : x - P c x = 0 := norm_eq_zero.mp hResidualNorm
          exact (sub_eq_zero.mp hz).symm
        have hTailSweep : realHilbertProjectionSweep P cs x = x := by
          simp only [realHilbertProjectionSweep, ContinuousLinearMap.comp_apply] at hSweep
          simpa [hc] using hSweep
        have hRest := (ih x).1 hTailSweep
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with hdc | hd
        · subst d
          exact hc
        · exact hRest d hd
      · intro hFixed
        have hc : P c x = x := hFixed c (by simp)
        have hRest : ∀ d ∈ cs, P d x = x := by
          intro d hd
          exact hFixed d (by simp [hd])
        simp only [realHilbertProjectionSweep, ContinuousLinearMap.comp_apply]
        rw [hc]
        exact (ih x).2 hRest

section EightColorSweep

variable (H N : ℕ)
variable (hN : 0 < N)
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable (beta : ℝ) (hBeta : 0 ≤ beta)

local notation "C" =>
  periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hBeta
local notation "L2" =>
  PeriodicHypercubicEvenSpecialUnitaryFixedColorGibbsL2 H N hN beta hBeta
local notation "P8" =>
  periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2
    H N hN beta hBeta

/-- Each canonical color block satisfies exact Pythagoras in the genuine Gibbs
`L²` Hilbert space. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2_residual_norm_sq
    (color : PeriodicHypercubicEvenEdgeColor)
    (f : L2) :
    ‖f - P8 color f‖ ^ 2 = ‖f‖ ^ 2 - ‖P8 color f‖ ^ 2 := by
  exact
    realHilbertProjection_residual_norm_sq
      (P8 color)
      (periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2_idempotent
        H N hN beta hBeta color)
      (fun x y =>
        periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2_inner_symm
          H N hN beta hBeta color x y)
      f

/-- The canonical normalized eight-color residual energy is exactly the average
of the eight block squared-norm losses. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2_eq_avg_block_norm_loss
    (f : L2) :
    periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
        H N hN beta hBeta f =
      ((Fintype.card PeriodicHypercubicEvenEdgeColor : ℝ)⁻¹) *
        ∑ color : PeriodicHypercubicEvenEdgeColor,
          (‖f‖ ^ 2 - ‖P8 color f‖ ^ 2) := by
  unfold periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
  unfold boundedColorNormalizedResidualEnergy
  apply congrArg
    (fun z : ℝ =>
      ((Fintype.card PeriodicHypercubicEvenEdgeColor : ℝ)⁻¹) * z)
  apply Finset.sum_congr rfl
  intro color _
  exact
    periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2_residual_norm_sq
      H N hN beta hBeta color f

/-- Explicit fixed-cardinality form of the preceding identity.  The coefficient
is `1/8`, independently of lattice volume. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2_eq_one_eighth_block_norm_loss
    (f : L2) :
    periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2
        H N hN beta hBeta f =
      (1 / 8 : ℝ) *
        ∑ color : PeriodicHypercubicEvenEdgeColor,
          (‖f‖ ^ 2 - ‖P8 color f‖ ^ 2) := by
  simpa [periodicHypercubicEvenEdgeColor_card] using
    periodicHypercubicEvenSpecialUnitaryEightColorHeatBathNormalizedResidualEnergyL2_eq_avg_block_norm_loss
      H N hN beta hBeta f

/-- Canonical ordered sweep through all eight color blocks.  The particular
`Finset.univ.toList` order is only used to define one concrete sweep; no
commutativity between different colors is asserted. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryEightColorHeatBathSweepL2 :
    L2 →L[ℝ] L2 :=
  realHilbertProjectionSweep P8
    ((Finset.univ : Finset PeriodicHypercubicEvenEdgeColor).toList)

/-- Sum of the successive block losses encountered by the canonical eight-color
sweep. -/
def periodicHypercubicEvenSpecialUnitaryEightColorHeatBathSweepPathLossL2
    (f : L2) : ℝ :=
  realHilbertProjectionSweepPathLoss P8
    ((Finset.univ : Finset PeriodicHypercubicEvenEdgeColor).toList) f

/-- The canonical eight-color sweep has exact telescoping squared-norm loss. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBathSweepL2_norm_sq_loss
    (f : L2) :
    ‖f‖ ^ 2 -
        ‖periodicHypercubicEvenSpecialUnitaryEightColorHeatBathSweepL2
          H N hN beta hBeta f‖ ^ 2 =
      periodicHypercubicEvenSpecialUnitaryEightColorHeatBathSweepPathLossL2
        H N hN beta hBeta f := by
  exact
    realHilbertProjectionSweep_norm_sq_loss
      P8
      (periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2_idempotent
        H N hN beta hBeta)
      (fun color x y =>
        periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2_inner_symm
          H N hN beta hBeta color x y)
      ((Finset.univ : Finset PeriodicHypercubicEvenEdgeColor).toList) f

/-- The path loss of the canonical eight-color sweep is nonnegative. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBathSweepPathLossL2_nonneg
    (f : L2) :
    0 ≤ periodicHypercubicEvenSpecialUnitaryEightColorHeatBathSweepPathLossL2
      H N hN beta hBeta f := by
  exact
    realHilbertProjectionSweepPathLoss_nonneg
      P8 ((Finset.univ : Finset PeriodicHypercubicEvenEdgeColor).toList) f

/-- Fixedness under one full ordered eight-color sweep is exactly membership in
the full common fixed space of all eight color blocks. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBathSweepL2_apply_eq_self_iff_commonFixed
    (f : L2) :
    periodicHypercubicEvenSpecialUnitaryEightColorHeatBathSweepL2
        H N hN beta hBeta f = f ↔
      f ∈ boundedColorCommonFixedSpace P8 := by
  unfold periodicHypercubicEvenSpecialUnitaryEightColorHeatBathSweepL2
  rw [realHilbertProjectionSweep_apply_eq_self_iff_forall_mem_fixed
    P8
    (periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2_idempotent
      H N hN beta hBeta)
    (fun color x y =>
      periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2_inner_symm
        H N hN beta hBeta color x y)]
  simp [boundedColorCommonFixedSpace]

/-- Consequently, one full eight-color sweep fixes a Gibbs `L²` vector exactly
when every one-link Wilson conditional-expectation projection fixes it. -/
theorem periodicHypercubicEvenSpecialUnitaryEightColorHeatBathSweepL2_apply_eq_self_iff_all_singleLink_fixed
    (f : L2) :
    periodicHypercubicEvenSpecialUnitaryEightColorHeatBathSweepL2
        H N hN beta hBeta f = f ↔
      ∀ e : PeriodicHypercubicEvenEdge H,
        (C).singleLinkHeatBathProjectionL2 e f = f := by
  rw [periodicHypercubicEvenSpecialUnitaryEightColorHeatBathSweepL2_apply_eq_self_iff_commonFixed]
  exact
    periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2_boundedColorCommonFixedSpace_iff_all_singleLink_fixed
      H N hN beta hBeta f

end EightColorSweep

end

end MathlibAnalytic
end MGAP4D