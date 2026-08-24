import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderArbitraryActionInsertionCinfty
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set
open scoped InnerProductSpace Topology ContDiff

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

local instance wilsonCylinderMathlibContDiffInfinityPhysicalCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- A quadratic remainder estimate implies the actual Mathlib one-dimensional
`HasDerivWithinAt` statement.  This is the calculus bridge used below: it turns
the operator-norm Taylor estimates already proved for the Wilson hierarchy into
Mathlib's derivative predicate without changing the physical domain. -/
private theorem wilsonCylinderMathlibContDiffInfinity_hasDerivWithinAt_of_quadraticRemainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f f' : ℝ → E) (s : Set ℝ) (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (_hx : x ∈ s)
    (hrem : ∀ y ∈ s,
      ‖f y - f x - (y - x) • f' x‖ ≤ B * ‖y - x‖ ^ 2) :
    HasDerivWithinAt f (f' x) s x := by
  rw [hasDerivWithinAt_iff_tendsto]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro epsilon hepsilon
  let D := B + 1
  have hD : 0 < D := by
    dsimp [D]
    linarith
  have hBD : B ≤ D := by
    dsimp [D]
    linarith
  refine ⟨epsilon / D, div_pos hepsilon hD, ?_⟩
  intro y hy hdist
  by_cases hxy : y = x
  · subst y
    simp [hepsilon]
  · have hsub : y - x ≠ 0 := sub_ne_zero.mpr hxy
    have hnorm : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.mpr hsub
    have hr := hrem y hy
    have hqnonneg :
        0 ≤ ‖y - x‖⁻¹ * ‖f y - f x - (y - x) • f' x‖ :=
      mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
    have hdx : ‖y - x‖ < epsilon / D := by
      simpa [Real.dist_eq] using hdist
    have hq :
        ‖y - x‖⁻¹ * ‖f y - f x - (y - x) • f' x‖ < epsilon := by
      calc
        ‖y - x‖⁻¹ * ‖f y - f x - (y - x) • f' x‖ ≤
            ‖y - x‖⁻¹ * (B * ‖y - x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr (norm_nonneg _))
        _ = B * ‖y - x‖ := by
          field_simp [hnorm]
        _ ≤ D * ‖y - x‖ :=
          mul_le_mul_of_nonneg_right hBD (norm_nonneg _)
        _ < D * (epsilon / D) :=
          mul_lt_mul_of_pos_left hdx hD
        _ = epsilon := by
          field_simp [ne_of_gt hD]
    simpa [Real.dist_eq, abs_of_nonneg hqnonneg] using hq

/-- Order zero of the arbitrary insertion hierarchy is exactly the physical
positive-half transfer operator.  Thus the hierarchy `K_beta S^m` already
contains the transfer itself at `m = 0`; no separate derivative tower is needed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_zero_eq_transferOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
        H N hN 0 beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
        H N hN beta hbeta := by
  apply ContinuousLinearMap.ext
  intro f
  apply (InnerProductSpace.toDualMap ℝ
    (PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N)).injective
  apply ContinuousLinearMap.ext
  intro g
  change inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
        H N hN 0 beta hbeta f) g =
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
        H N hN beta hbeta f) g
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_inner_eq_pathActionPowerIntegral
    H N hN 0 beta hbeta f g]
  rw [← periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude_eq_physicalTransfer_inner
    H N hN beta hbeta f g]
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathNthActionInsertionAmplitude
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude
  simp

/-- A total real-valued parameter wrapper for the order-`m` physical insertion.
The value outside `beta ≥ 0` is only a syntactic totalization required by
Mathlib's calculus API.  Every theorem below is restricted to `Set.Ici 0`, so
this definition introduces no negative-coupling physical assertion. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
    (H N : ℕ) (hN : 0 < N) (m : ℕ) (beta : ℝ) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  if hbeta : 0 ≤ beta then
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
      H N hN m beta hbeta
  else
    0

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_of_nonneg
    (H N : ℕ) (hN : 0 < N) (m : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN m beta =
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
        H N hN m beta hbeta := by
  simp [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily,
    hbeta]

/-- On the physical half-line, order zero of the totalized real family is the
existing genuine physical transfer operator. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_zero_eq_transferOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN 0 beta =
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
        H N hN beta hbeta := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_of_nonneg
    H N hN 0 beta hbeta]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator_zero_eq_transferOperator
      H N hN beta hbeta

/-- The generic operator Taylor remainder rewritten in the exact form expected
by `HasDerivWithinAt`: the derivative field of order `m` is minus order `m+1`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_quadraticRemainder
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN m gamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN m beta -
        (gamma - beta) •
          (-periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
            H N hN (m + 1) beta)‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ (m + 2) * ‖gamma - beta‖ ^ 2 := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_of_nonneg
    H N hN m gamma hgamma]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_of_nonneg
    H N hN m beta hbeta]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_of_nonneg
    H N hN (m + 1) beta hbeta]
  simpa [smul_neg, sub_neg_eq_add] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionBetaRemainderOperator_norm_le
      H N hN m beta hbeta gamma hgamma

/-- Actual Mathlib derivative, within the genuine physical half-line, of every
order in the Wilson insertion hierarchy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_hasDerivWithinAt
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta : ℝ) (hbeta : beta ∈ Set.Ici (0 : ℝ)) :
    HasDerivWithinAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN m)
      (-periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN (m + 1) beta)
      (Set.Ici (0 : ℝ)) beta := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound H N
  let B := C ^ (m + 2)
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg H N
  have hB : 0 ≤ B := pow_nonneg hC (m + 2)
  apply wilsonCylinderMathlibContDiffInfinity_hasDerivWithinAt_of_quadraticRemainder
    (f := periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
      H N hN m)
    (f' := fun t =>
      -periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN (m + 1) t)
    (s := Set.Ici (0 : ℝ)) B hB beta hbeta
  intro gamma hgamma
  simpa [B, C] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_quadraticRemainder
      H N hN m beta gamma hbeta hgamma

/-- Exact `derivWithin` identity for the arbitrary-order hierarchy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_derivWithin
    (H N : ℕ) (hN : 0 < N) (m : ℕ)
    (beta : ℝ) (hbeta : beta ∈ Set.Ici (0 : ℝ)) :
    derivWithin
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN m)
      (Set.Ici (0 : ℝ)) beta =
      -periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN (m + 1) beta := by
  have hder :
      HasDerivWithinAt
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN m)
        (-periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN (m + 1) beta)
        (Set.Ici (0 : ℝ)) beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_hasDerivWithinAt
      H N hN m beta hbeta
  have hunique : UniqueDiffWithinAt ℝ (Set.Ici (0 : ℝ)) beta :=
    (uniqueDiffOn_Ici (0 : ℝ)) beta hbeta
  exact hder.derivWithin hunique

/-- Every order of the hierarchy is differentiable on the physical coupling
half-line in Mathlib's native calculus sense. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_differentiableOn
    (H N : ℕ) (hN : 0 < N) (m : ℕ) :
    DifferentiableOn ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN m)
      (Set.Ici (0 : ℝ)) := by
  intro beta hbeta
  have hder :
      HasDerivWithinAt
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN m)
        (-periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN (m + 1) beta)
        (Set.Ici (0 : ℝ)) beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_hasDerivWithinAt
      H N hN m beta hbeta
  exact hder.differentiableWithinAt

/-- Hence every order is continuous on the physical half-line. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_continuousOn
    (H N : ℕ) (hN : 0 < N) (m : ℕ) :
    ContinuousOn
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN m)
      (Set.Ici (0 : ℝ)) := by
  intro beta hbeta
  have hder :
      HasDerivWithinAt
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN m)
        (-periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN (m + 1) beta)
        (Set.Ici (0 : ℝ)) beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_hasDerivWithinAt
      H N hN m beta hbeta
  exact hder.continuousWithinAt

/-- Finite-order Mathlib `ContDiffOn` for every insertion order.  The induction
uses the exact derivative recursion and the fact that `Ici 0` has unique
derivatives. -/
private theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_contDiffOn_nat
    (H N : ℕ) (hN : 0 < N) :
    ∀ (n m : ℕ),
      ContDiffOn ℝ n
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN m)
        (Set.Ici (0 : ℝ)) := by
  intro n
  induction n with
  | zero =>
      intro m
      exact (contDiffOn_zero.mpr
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_continuousOn
          H N hN m))
  | succ n ih =>
      intro m
      have hstep :
          ContDiffOn ℝ ((n : ℕ∞ω) + 1)
            (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
              H N hN m)
            (Set.Ici (0 : ℝ)) := by
        refine (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici (0 : ℝ))).2 ?_
        refine ⟨
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_differentiableOn
            H N hN m, ?_, ?_⟩
        · simp
        · have hnext := ih (m + 1)
          have hneg :
              ContDiffOn ℝ n
                (fun beta : ℝ =>
                  -periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
                    H N hN (m + 1) beta)
                (Set.Ici (0 : ℝ)) := by
            simpa only [Pi.neg_apply] using hnext.neg
          exact hneg.congr (fun beta hbeta =>
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_derivWithin
              H N hN m beta hbeta)
      simpa using hstep

/-- The certificate hierarchy of PR #2089 is now promoted to Mathlib's actual
`ContDiffOn ℝ ∞` predicate at every insertion order. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_contDiffOn_infty
    (H N : ℕ) (hN : 0 < N) (m : ℕ) :
    ContDiffOn ℝ ∞
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN m)
      (Set.Ici (0 : ℝ)) := by
  apply contDiffOn_infty.mpr
  intro n
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_contDiffOn_nat
      H N hN n m

/-- Exact all-order Mathlib iterated derivative of an arbitrary starting
insertion order. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_iteratedDerivWithin
    (H N : ℕ) (hN : 0 < N) (m n : ℕ)
    (beta : ℝ) (hbeta : beta ∈ Set.Ici (0 : ℝ)) :
    iteratedDerivWithin n
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
        H N hN m)
      (Set.Ici (0 : ℝ)) beta =
      ((-1 : ℝ) ^ n) •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN (m + n) beta := by
  induction n generalizing beta with
  | zero =>
      simp
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      have hEqOn :
          Set.EqOn
            (iteratedDerivWithin n
              (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
                H N hN m)
              (Set.Ici (0 : ℝ)))
            (fun t : ℝ =>
              ((-1 : ℝ) ^ n) •
                periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
                  H N hN (m + n) t)
            (Set.Ici (0 : ℝ)) := by
        intro t ht
        exact ih t ht
      rw [derivWithin_congr hEqOn (ih beta hbeta)]
      let F :=
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
          H N hN (m + n)
      let c : ℝ := (-1 : ℝ) ^ n
      have hbase :
          HasDerivWithinAt F
            (-periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
              H N hN (m + n + 1) beta)
            (Set.Ici (0 : ℝ)) beta := by
        simpa [F, Nat.add_assoc] using
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_hasDerivWithinAt
            H N hN (m + n) beta hbeta
      have hscaled :
          HasDerivWithinAt
            (fun t : ℝ => c • F t)
            (c • (-periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
              H N hN (m + n + 1) beta))
            (Set.Ici (0 : ℝ)) beta := by
        simpa only [Pi.smul_apply] using hbase.const_smul c
      have hunique : UniqueDiffWithinAt ℝ (Set.Ici (0 : ℝ)) beta :=
        (uniqueDiffOn_Ici (0 : ℝ)) beta hbeta
      have hscaledDeriv :
          derivWithin (fun t : ℝ => c • F t) (Set.Ici (0 : ℝ)) beta =
            c • (-periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
              H N hN (m + n + 1) beta) :=
        hscaled.derivWithin hunique
      change derivWithin (fun t : ℝ => c • F t) (Set.Ici (0 : ℝ)) beta = _
      rw [hscaledDeriv]
      simp [c, F, pow_succ, Nat.add_assoc, mul_smul]

/-- The Mathlib-facing transfer family: it is simply order zero of the single
Wilson action-insertion hierarchy.  It agrees pointwise with the genuine
physical transfer operator on `beta ≥ 0`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily
    H N hN 0 beta

/-- Pointwise identification of the Mathlib-facing family with the existing
physical transfer on the genuine physical half-line. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_eq_physicalTransfer
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN beta =
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
        H N hN beta hbeta := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_zero_eq_transferOperator
      H N hN beta hbeta

/-- The genuine positive-half physical transfer family is `C^∞` in Wilson
coupling in Mathlib's native `ContDiffOn` sense on the closed half-line. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_contDiffOn_infty
    (H N : ℕ) (hN : 0 < N) :
    ContDiffOn ℝ ∞
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN)
      (Set.Ici (0 : ℝ)) := by
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_contDiffOn_infty
      H N hN 0

/-- Exact `n`-th Mathlib iterated derivative of the transfer family.  The
right-hand side is the literal physical `K_beta S_path^n` insertion operator,
with the expected alternating sign. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin
    (H N : ℕ) (hN : 0 < N) (n : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    iteratedDerivWithin n
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
        H N hN)
      (Set.Ici (0 : ℝ)) beta =
      ((-1 : ℝ) ^ n) •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
          H N hN n beta hbeta := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_iteratedDerivWithin
    H N hN 0 n beta hbeta]
  simp only [Nat.zero_add]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionMathlibRealFamily_of_nonneg
    H N hN n beta hbeta]

/-- Final native-Mathlib smoothness package.  This replaces the previous
certificate-only wording by an actual `ContDiffOn ℝ ∞` theorem and exact
`iteratedDerivWithin` identities, while remaining entirely on `beta ≥ 0`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransfer_Cinfty_package
    (H N : ℕ) (hN : 0 < N) :
    ContDiffOn ℝ ∞
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
          H N hN)
        (Set.Ici (0 : ℝ)) ∧
      (∀ (beta : ℝ) (hbeta : 0 ≤ beta),
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
            H N hN beta =
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
            H N hN beta hbeta) ∧
      ∀ (n : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta),
        iteratedDerivWithin n
            (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily
              H N hN)
            (Set.Ici (0 : ℝ)) beta =
          ((-1 : ℝ) ^ n) •
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderNthWilsonActionInsertionOperator
              H N hN n beta hbeta := by
  exact ⟨
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_contDiffOn_infty
      H N hN,
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_eq_physicalTransfer
      H N hN,
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderMathlibTransferFamily_iteratedDerivWithin
      H N hN⟩

end
end MathlibAnalytic
end MGAP4D
