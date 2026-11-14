import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferUniformTopOrthogonalPowerDecay
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferScaleUniformDefectBridge
import Mathlib.Tactic
import Lean.Meta.Check
import Lean.Meta.Transform
import Lean.Util.CollectAxioms
import Lean.Util.InstantiateLevelParams
import Lean.Elab.Tactic.ElabTerm

/-!
# P4-Q2-PZ37AKL: original Wilson H-uniform top-orthogonal coercivity

The existing genuine two-sided twelve-spatial theorem supplies the common
contraction factor 3071/3072 on a positive volume-independent beta interval.
This leaf states its quadratic coercivity consequence for the ORIGINAL SU(2)
physical Wilson transfer P, normalized by S = P / ||P||, on the orthogonal
complement of the FULL eigenvalue-one space:

    (1/3072) ||x||^2 <= <x - S x, x>.

The cutoff below is exactly the existing positive cutoff at s=9. It has no H
argument. Both the nonempty interval and a single positive coupling shared
by every H are proved; no uniform frame inequality is assumed here.

The inherited six-color cardinality proof uses a compiled-decision dependency.
We prove the identical finite proposition by ordinary kernel reduction and
replay the affected proof bodies with that replacement. Every generated term
is checked by the kernel against the unchanged physical statement; the replay
also rejects any remaining dependency beyond the standard three axioms.

The squared defect has coefficient 6143/9437184. Its raw formulation retains
the factor ||P||^2. These results do not assert a positive lower bound for P,
coercivity on the full space containing its top vector, membership of the
original numerical beta0 in this interval, a uniform original GL-source
Rayleigh floor, a common-carrier limit or a continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace

noncomputable section
set_option autoImplicit false

/-- Kernel reduction proves the same original six-color cardinality fact. -/
theorem p4Q2PZ37AKL_spatialColor_card_kernel :
    Fintype.card PeriodicHypercubicEvenGroundStateSpatialColor = 6 := by
  change Fintype.card
    (PeriodicHypercubicOtherAxis (0 : PeriodicHypercubicAxis) × ZMod 2) = 6
  rw [Fintype.card_prod, periodicHypercubicOtherAxis_card]
  decide

namespace PZ37AKLProofReplay

open Lean Meta Elab Tactic

private def standardAxioms : Array Name :=
  #[`propext, `Classical.choice, `Quot.sound]

private def assertAllowedAxioms
    (allowed : Array Name) (e : Expr) : MetaM Unit := do
  for n in e.getUsedConstants do
    for ax in (← collectAxioms n) do
      unless allowed.contains ax do
        throwError "AKL replay: declaration {n} retains a disallowed dependency {ax}"

/-- This constructs a proof term; it neither changes an imported declaration
nor changes the target. The only substitution is a same-type kernel proof. -/
private def replayColorCard (input : Expr) : MetaM Expr := do
  let oldCard : Name :=
    `MGAP4D.MathlibAnalytic.periodicHypercubicEvenGroundStateSpatialColor_card
  let newCard : Name :=
    `MGAP4D.MathlibAnalytic.p4Q2PZ37AKL_spatialColor_card_kernel
  let oldInfo ← getConstInfo oldCard
  let newInfo ← getConstInfo newCard
  unless oldInfo.levelParams.isEmpty && newInfo.levelParams.isEmpty do
    throwError "AKL replay: unexpected cardinality universe parameters"
  unless (← isDefEq oldInfo.type newInfo.type) do
    throwError "AKL replay: cardinality replacement has a different type"
  assertAllowedAxioms standardAxioms (mkConst newCard)
  let inherited ← collectAxioms oldCard
  let extra := inherited.filter (fun ax => !standardAxioms.contains ax)
  -- Kernel hardening of the upstream six-color proof removes the legacy
  -- native_decide axiom.  In that case the ORIGINAL input proof must already
  -- have only standard axioms.  In the legacy case, retain the old exactly-one
  -- extra-axiom restriction and demand a standard-only replayed output.
  if extra.isEmpty then
    assertAllowedAxioms standardAxioms input
  else
    unless extra.size == 1 do
      throwError "AKL replay: the inspected legacy dependency set has changed"
    assertAllowedAxioms (standardAxioms ++ extra) input
  let output ← Lean.Core.transform (m := MetaM) input (pre := fun e => do
    match e with
    | .const n us =>
        if n == oldCard then
          return .done (mkConst newCard us)
        let axs ← collectAxioms n
        if axs.all (fun ax => standardAxioms.contains ax) then
          return .done e
        let info ← getConstInfo n
        if info.isUnsafe then
          throwError "AKL replay: unsupported declaration {n}"
        let body ← match info with
          | .defnInfo d => pure d.value
          | .thmInfo t => pure t.value
          | _ => throwError "AKL replay: no permitted proof body for {n}"
        return .visit (body.instantiateLevelParams info.levelParams us)
    | _ => return .continue)
  assertAllowedAxioms standardAxioms output
  return output

elab "p4_akl_kernel_replay " t:term : tactic =>
  closeMainGoalUsing `p4_akl_kernel_replay fun target _ => do
    assertAllowedAxioms standardAxioms target
    let input ← instantiateMVars (← elabTermEnsuringType t (some target))
    let output ← replayColorCard input
    unless (← isDefEq (← inferType output) target) do
      throwError "AKL replay changed the theorem type"
    let output ← instantiateMVars output
    let lctx ← instantiateLCtxMVars (← getLCtx)
    if output.hasMVar then
      throwError "AKL replay: unresolved variables remain in the proof"
    for localDecl in lctx do
      if localDecl.type.hasMVar then
        throwError "AKL replay: unresolved variables in local type {localDecl.userName}"
      if let some value := localDecl.value? (allowNondep := true) then
        if value.hasMVar then
          throwError "AKL replay: unresolved variables in local value {localDecl.userName}"
    match Lean.Kernel.check (← getEnv) lctx output with
    | .ok .. => pure ()
    | .error ex =>
        throwError "AKL replay kernel check: {ex.toMessageData (← getOptions)}"
    return output

end PZ37AKLProofReplay

/-- The canonical positive high-temperature cutoff, specialized at s=9.
It is independent of H and is not identified with the original beta0. -/
def p4Q2PZ37AKL_originalUniformCoercivityCutoff : ℝ :=
  GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
    9 (by norm_num)

theorem p4Q2PZ37AKL_originalUniformCoercivityCutoff_pos :
    0 < p4Q2PZ37AKL_originalUniformCoercivityCutoff :=
  GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff_pos
    9 (by norm_num)

section OriginalPhysicalWilson

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "P" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (Nat.succ_pos 1) beta hbeta
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 (Nat.succ_pos 1) beta hbeta
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H 2 (Nat.succ_pos 1) beta hbeta
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H 2 (Nat.succ_pos 1) beta hbeta

/-- The original SU(2) full-top-orthogonal restriction has one common
operator-norm bound at every H throughout the same positive beta interval. -/
theorem p4Q2PZ37AKL_originalTopOrthogonal_norm_le
    (hcut : beta ≤ p4Q2PZ37AKL_originalUniformCoercivityCutoff) :
    ‖R‖ ≤ (3071 / 3072 : ℝ) := by
  have hcut' :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
          9 (by norm_num) := hcut
  p4_akl_kernel_replay (by
    simpa only [
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor]
      using
        periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalTransferOperator_norm_le
          (fun H : ℕ => H) 2 (Nat.succ_pos 1)
          (fun _ : ℕ => beta) (fun _ => hbeta)
          9 (by norm_num) (fun _ => hcut') H)

/-- Vector contraction on the actual physical carrier; subtype norm is
transported definitionally, with no source or carrier replacement. -/
theorem p4Q2PZ37AKL_originalTopOrthogonal_apply_norm_le
    (hcut : beta ≤ p4Q2PZ37AKL_originalUniformCoercivityCutoff)
    (x : K) :
    ‖S (x : G)‖ ≤ (3071 / 3072 : ℝ) * ‖(x : G)‖ := by
  have hApply :=
    realHilbertTopEigenspaceOrthogonalRestriction_pow_apply_norm_le S
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
        H 2 (Nat.succ_pos 1) beta hbeta) 1 x
  simp only [pow_one] at hApply
  change ‖S (x : G)‖ ≤ ‖R‖ * ‖(x : G)‖ at hApply
  exact hApply.trans
    (mul_le_mul_of_nonneg_right
      (p4Q2PZ37AKL_originalTopOrthogonal_norm_le H beta hbeta hcut)
      (norm_nonneg (x : G)))

/-- H-uniform quadratic coercivity of I-S on the full-top orthogonal
physical sector, with the explicit common constant 1/3072. -/
theorem p4Q2PZ37AKL_originalTopOrthogonal_quadraticCoercivity
    (hcut : beta ≤ p4Q2PZ37AKL_originalUniformCoercivityCutoff)
    (x : K) :
    (1 / 3072 : ℝ) * ‖(x : G)‖ ^ 2 ≤
      inner ℝ ((x : G) - S (x : G)) (x : G) := by
  have hApply :=
    p4Q2PZ37AKL_originalTopOrthogonal_apply_norm_le H beta hbeta hcut x
  have hInner :
      inner ℝ (S (x : G)) (x : G) ≤
        (3071 / 3072 : ℝ) * ‖(x : G)‖ ^ 2 := by
    calc
      inner ℝ (S (x : G)) (x : G) ≤
          ‖S (x : G)‖ * ‖(x : G)‖ := real_inner_le_norm _ _
      _ ≤ ((3071 / 3072 : ℝ) * ‖(x : G)‖) * ‖(x : G)‖ :=
        mul_le_mul_of_nonneg_right hApply (norm_nonneg (x : G))
      _ = (3071 / 3072 : ℝ) * ‖(x : G)‖ ^ 2 := by ring
  rw [inner_sub_left (𝕜 := ℝ) (x : G) (S (x : G)) (x : G),
    real_inner_self_eq_norm_sq (x : G)]
  nlinarith

/-- The same common quadratic bound gives an H-uniform norm lower bound
for I-S on its physical excitation sector. -/
theorem p4Q2PZ37AKL_originalTopOrthogonal_normCoercivity
    (hcut : beta ≤ p4Q2PZ37AKL_originalUniformCoercivityCutoff)
    (x : K) :
    (1 / 3072 : ℝ) * ‖(x : G)‖ ≤ ‖(x : G) - S (x : G)‖ := by
  by_cases hx : (x : G) = 0
  · simp [hx]
  · have hxNorm : 0 < ‖(x : G)‖ := norm_pos_iff.mpr hx
    apply (mul_le_mul_iff_left₀ hxNorm).mp
    calc
      (1 / 3072 : ℝ) * ‖(x : G)‖ * ‖(x : G)‖ =
          (1 / 3072 : ℝ) * ‖(x : G)‖ ^ 2 := by ring
      _ ≤ inner ℝ ((x : G) - S (x : G)) (x : G) :=
        p4Q2PZ37AKL_originalTopOrthogonal_quadraticCoercivity H beta hbeta hcut x
      _ ≤ ‖(x : G) - S (x : G)‖ * ‖(x : G)‖ := real_inner_le_norm _ _

/-- Exact dimensionless squared-defect coefficient 1-(3071/3072)^2. -/
theorem p4Q2PZ37AKL_originalTopOrthogonal_squaredDefect
    (hcut : beta ≤ p4Q2PZ37AKL_originalUniformCoercivityCutoff)
    (x : K) :
    (6143 / 9437184 : ℝ) * ‖(x : G)‖ ^ 2 ≤
      ‖(x : G)‖ ^ 2 - ‖S (x : G)‖ ^ 2 := by
  have hApply :=
    p4Q2PZ37AKL_originalTopOrthogonal_apply_norm_le H beta hbeta hcut x
  have hSquare := pow_le_pow_left₀ (norm_nonneg (S (x : G))) hApply 2
  nlinarith

/-- The same coefficient in the RAW genuine Wilson defect. The top scale
||P||^2 is retained and is not asserted to have a uniform positive floor. -/
theorem p4Q2PZ37AKL_originalTopOrthogonal_rawSquaredDefect
    (hcut : beta ≤ p4Q2PZ37AKL_originalUniformCoercivityCutoff)
    (x : K) :
    (6143 / 9437184 : ℝ) * ‖P‖ ^ 2 * ‖(x : G)‖ ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
        H 2 (by decide) beta hbeta x := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_normalized_sq_defect_to_raw
      H 2 (by decide) beta hbeta (6143 / 9437184) x
      (p4Q2PZ37AKL_originalTopOrthogonal_squaredDefect H beta hbeta hcut x)

end OriginalPhysicalWilson

/-- A nonempty positive beta interval works simultaneously for every H.
The existential cutoff and the common coercivity constant are proved, not
inputs. No numerical inclusion of the original beta0 is asserted. -/
theorem p4Q2PZ37AKL_exists_positiveUniformCoercivityInterval :
    ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ (beta : ℝ) (hbeta : 0 < beta), beta ≤ cutoff →
        ∀ (H : ℕ)
          (x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H 2 (by decide) beta hbeta.le),
          (1 / 3072 : ℝ) *
              ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                H 2)‖ ^ 2 ≤
            inner ℝ
              ((x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                H 2) -
                periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
                  H 2 (by decide) beta hbeta.le x)
              (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                H 2) := by
  refine ⟨p4Q2PZ37AKL_originalUniformCoercivityCutoff,
    p4Q2PZ37AKL_originalUniformCoercivityCutoff_pos, ?_⟩
  intro beta hbeta hcut H x
  exact p4Q2PZ37AKL_originalTopOrthogonal_quadraticCoercivity
    H beta hbeta.le hcut x

/-- In particular, one single strictly positive coupling can be fixed
BEFORE quantifying over H. This is not a volume-dependent beta_H choice. -/
theorem p4Q2PZ37AKL_exists_fixedPositiveCoupling_uniformCoercivity :
    ∃ beta : ℝ, ∃ hbeta : 0 < beta,
      ∀ (H : ℕ)
        (x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H 2 (by decide) beta hbeta.le),
        (1 / 3072 : ℝ) *
            ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              H 2)‖ ^ 2 ≤
          inner ℝ
            ((x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              H 2) -
              periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
                H 2 (by decide) beta hbeta.le x)
            (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              H 2) := by
  have hcutPos := p4Q2PZ37AKL_originalUniformCoercivityCutoff_pos
  have hbeta : 0 < p4Q2PZ37AKL_originalUniformCoercivityCutoff / 2 := by
    positivity
  refine ⟨p4Q2PZ37AKL_originalUniformCoercivityCutoff / 2, hbeta, ?_⟩
  intro H x
  exact p4Q2PZ37AKL_originalTopOrthogonal_quadraticCoercivity
    H _ hbeta.le (by linarith) x

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKL_originalUniformCoercivityCutoff
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKL_spatialColor_card_kernel
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKL_originalUniformCoercivityCutoff_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKL_originalTopOrthogonal_norm_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKL_originalTopOrthogonal_apply_norm_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKL_originalTopOrthogonal_quadraticCoercivity
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKL_originalTopOrthogonal_normCoercivity
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKL_originalTopOrthogonal_squaredDefect
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKL_originalTopOrthogonal_rawSquaredDefect
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKL_exists_positiveUniformCoercivityInterval
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKL_exists_fixedPositiveCoupling_uniformCoercivity

-- The existing cutoff is already independent of the repaired cardinality proof.
#print axioms MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff_pos
