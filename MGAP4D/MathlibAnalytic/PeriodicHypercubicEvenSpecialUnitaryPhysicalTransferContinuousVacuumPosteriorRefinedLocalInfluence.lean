import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorFirstBootstrapUniformResponse
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousGroundStateFiberCrossRatio
import Mathlib.Tactic

/-!
# Refined local/remote posterior influence

The first response bootstrap now gives a boundary-independent remote response
radius.  The previous non-strict influence carrier still used the fallback
value `1` on plaquette-local off-diagonal pairs, which cannot lead to a
strict high-temperature row bound because that fallback does not vanish at
`beta = 0`.

This file removes that obstruction.

For any distinct source and target, changing the source coordinate of the
right environment changes each complete target-fiber weight by at most

  exp(16 * beta),

because the one-slab kernel and the continuous physical vacuum each cost at
most `exp(8 * beta)`.  Hence the complete log-weight cross-ratio radius is
at most `32 * beta`, and the sharp normalized half-L1 coefficient is

  q_local(beta) = (exp(32 * beta) - 1) / (exp(32 * beta) + 1).

We use this direct coefficient on plaquette-local pairs and retain the
response-generated coefficient on remote pairs.  Both vanish exactly at zero
coupling.

No row-sum strictness is asserted in this file.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance posteriorRefinedInfluenceTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorRefinedInfluenceCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorRefinedInfluenceSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorRefinedInfluenceMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorRefinedInfluenceBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

private theorem log_sub_log_abs_le_of_mutual_exp_mul
    {x y R : ℝ}
    (hx : 0 < x)
    (hy : 0 < y)
    (hxy : x ≤ Real.exp R * y)
    (hyx : y ≤ Real.exp R * x) :
    |Real.log x - Real.log y| ≤ R := by
  have hUpperLog :
      Real.log x ≤ Real.log (Real.exp R * y) :=
    Real.log_le_log hx hxy
  have hLowerLog :
      Real.log y ≤ Real.log (Real.exp R * x) :=
    Real.log_le_log hy hyx
  rw [Real.log_mul (Real.exp_ne_zero R) hy.ne', Real.log_exp] at hUpperLog
  rw [Real.log_mul (Real.exp_ne_zero R) hx.ne', Real.log_exp] at hLowerLog
  rw [abs_le]
  constructor <;> linarith

/-- Changing one distinct source coordinate changes the complete target-fiber
weight by at most `exp(16 beta)`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight_le_exp_sixteen_mul_update_source
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
        H N hN beta hbeta left right target g ≤
      Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
          H N hN beta hbeta left
          (Function.update right source sourceValue) target g := by
  let Bg : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update right target g
  let Bsg : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update (Function.update right source sourceValue) target g
  have hComm :
      Bsg = Function.update Bg source sourceValue := by
    dsimp [Bg, Bsg]
    exact Function.update_comm hNe sourceValue g right
  have hKernel :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta left Bg ≤
        Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta left (Function.update Bg source sourceValue) := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuousVacuumReplaceLink_le_exp_eight_mul
        H N hN beta hbeta left Bg source (Bg source) sourceValue
    simpa [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink,
      Bg] using h
  have hVacuum :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta Bg ≤
        Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta (Function.update Bg source sourceValue) := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuousVacuumReplaceLink_le_exp_eight_mul
        H N hN beta hbeta Bg source (Bg source) sourceValue
    simpa [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink,
      Bg] using h
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkUpdatedRight
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
  change
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta left Bg *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta Bg ≤
      Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta left Bsg *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta Bsg)
  rw [hComm]
  calc
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta left Bg *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta Bg ≤
      (Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta left (Function.update Bg source sourceValue)) *
        (Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta (Function.update Bg source sourceValue)) := by
      exact mul_le_mul hKernel hVacuum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
          H N hN beta hbeta Bg).le
        (mul_nonneg (Real.exp_pos _).le
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
            H N beta left (Function.update Bg source sourceValue)).le)
    _ =
      Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta left (Function.update Bg source sourceValue) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta (Function.update Bg source sourceValue)) := by
      have hExp :
          Real.exp (8 * beta) * Real.exp (8 * beta) =
            Real.exp (16 * beta) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        (Real.exp (8 * beta) *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta left (Function.update Bg source sourceValue)) *
          (Real.exp (8 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
              H N hN beta hbeta (Function.update Bg source sourceValue)) =
            (Real.exp (8 * beta) * Real.exp (8 * beta)) *
              (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                  H N beta left (Function.update Bg source sourceValue) *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
                  H N hN beta hbeta (Function.update Bg source sourceValue)) := by
              ring
        _ = Real.exp (16 * beta) *
              (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                  H N beta left (Function.update Bg source sourceValue) *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
                  H N hN beta hbeta (Function.update Bg source sourceValue)) := by
              rw [hExp]

/-- Reverse complete-weight comparison with the same source-change factor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight_update_source_le_exp_sixteen_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
        H N hN beta hbeta left
        (Function.update right source sourceValue) target g ≤
      Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
          H N hN beta hbeta left right target g := by
  let Bg : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update right target g
  let Bsg : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update (Function.update right source sourceValue) target g
  have hComm :
      Bsg = Function.update Bg source sourceValue := by
    dsimp [Bg, Bsg]
    exact Function.update_comm hNe sourceValue g right
  have hKernel :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta left (Function.update Bg source sourceValue) ≤
        Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta left Bg := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuousVacuumReplaceLink_le_exp_eight_mul
        H N hN beta hbeta left Bg source sourceValue (Bg source)
    simpa [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink,
      Bg] using h
  have hVacuum :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update Bg source sourceValue) ≤
        Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta Bg := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuousVacuumReplaceLink_le_exp_eight_mul
        H N hN beta hbeta Bg source sourceValue (Bg source)
    simpa [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink,
      Bg] using h
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkUpdatedRight
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
  change
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta left Bsg *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta Bsg ≤
      Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta left Bg *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta Bg)
  rw [hComm]
  calc
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta left (Function.update Bg source sourceValue) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update Bg source sourceValue) ≤
      (Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta left Bg) *
        (Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta Bg) := by
      exact mul_le_mul hKernel hVacuum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
          H N hN beta hbeta (Function.update Bg source sourceValue)).le
        (mul_nonneg (Real.exp_pos _).le
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
            H N beta left Bg).le)
    _ =
      Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta left Bg *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta Bg) := by
      have hExp :
          Real.exp (8 * beta) * Real.exp (8 * beta) =
            Real.exp (16 * beta) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        (Real.exp (8 * beta) *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta left Bg) *
          (Real.exp (8 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
              H N hN beta hbeta Bg) =
            (Real.exp (8 * beta) * Real.exp (8 * beta)) *
              (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta left Bg *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
                  H N hN beta hbeta Bg) := by
              ring
        _ = Real.exp (16 * beta) *
              (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta left Bg *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
                  H N hN beta hbeta Bg) := by
              rw [hExp]

/-- The complete target-fiber log weight changes by at most `16 beta` at each
inserted target value under one distinct source replacement. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_update_source_abs_sub_le_sixteen_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
          H N hN beta hbeta left right target g -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
          H N hN beta hbeta left
          (Function.update right source sourceValue) target g| ≤
      16 * beta := by
  let x :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
      H N hN beta hbeta left right target g
  let y :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
      H N hN beta hbeta left (Function.update right source sourceValue) target g
  have hx : 0 < x := by
    dsimp [x]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight_pos
        H N hN beta hbeta left right target g
  have hy : 0 < y := by
    dsimp [y]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight_pos
        H N hN beta hbeta left (Function.update right source sourceValue) target g
  have hxy : x ≤ Real.exp (16 * beta) * y := by
    dsimp [x, y]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight_le_exp_sixteen_mul_update_source
        H N hN beta hbeta left right target source sourceValue g hNe
  have hyx : y ≤ Real.exp (16 * beta) * x := by
    dsimp [x, y]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight_update_source_le_exp_sixteen_mul
        H N hN beta hbeta left right target source sourceValue g hNe
  have hlog :=
    log_sub_log_abs_le_of_mutual_exp_mul
      hx hy hxy hyx
  simpa [
    x, y,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
  ] using hlog

/-- Therefore the complete log-weight cross-ratio radius is at most
`32 beta`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_crossRatioBound_update_source_thirtyTwo_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target) :
    ContinuousNormalizedExpCrossRatioBound
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left right target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H N hN beta hbeta left (Function.update right source sourceValue) target)
      (32 * beta) := by
  intro u v
  have hu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_update_source_abs_sub_le_sixteen_mul
      H N hN beta hbeta left right target source sourceValue u hNe
  have hv :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_update_source_abs_sub_le_sixteen_mul
      H N hN beta hbeta left right target source sourceValue v hNe
  have huUpper := (abs_le.mp hu).2
  have hvLower := (abs_le.mp hv).1
  linarith

/-- Direct source-change influence coefficient coming from the complete
target-fiber `32 beta` cross-ratio bound. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
    (beta : ℝ) : ℝ :=
  (Real.exp (32 * beta) - 1) / (Real.exp (32 * beta) + 1)

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence_nonneg
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
        beta := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
  exact div_nonneg
    (sub_nonneg.mpr (Real.one_le_exp (by nlinarith [hbeta])))
    (by positivity)

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence_zero :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
        0 = 0 := by
  norm_num [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence]

/-- Direct half-L1 bound for posterior one-link conditionals under any distinct
one-source environment change. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalHalfL1_le_directOneSource
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hNe : source ≠ target)
    (hAgree :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
        A C source) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalHalfL1
        H N hN beta hbeta B A C target ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
        beta := by
  have hUpdate :
      Function.update A source (C source) = C :=
    posteriorAgreeOff_update_source_eq A C source hAgree
  rw [← hUpdate]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalHalfL1
  simp_rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_eq_groundStateNormalizedDensity]
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkNormalizedDensity_halfL1_le_of_crossRatio
      H N hN beta hbeta B A
      (Function.update A source (C source)) target
      (32 * beta) (by nlinarith [hbeta])
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_crossRatioBound_update_source_thirtyTwo_mul
        H N hN beta hbeta B A target source (C source) hNe)

/-- Refined influence profile: zero diagonal, direct `32 beta` coefficient on
plaquette-local pairs, response-derived coefficient on remote pairs. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
    (H : ℕ)
    (beta : ℝ)
    (epsilon :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ := by
  classical
  exact if source = target then 0
    else if periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source then
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
        beta
    else
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
        beta (epsilon target source)

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (epsilon :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hepsilon : ∀ target source, 0 ≤ epsilon target source)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
        H beta epsilon target source := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
  by_cases hdiag : source = target
  · simp [hdiag]
  · simp only [hdiag, if_false]
    by_cases hlocal :
        periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source
    · simp only [hlocal, if_true]
      exact
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence_nonneg
          beta hbeta
    · simp only [hlocal, if_false]
      exact
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence_nonneg
          beta (epsilon target source) (hepsilon target source)

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence_diagonal
    (H : ℕ)
    (beta : ℝ)
    (epsilon :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
        H beta epsilon target target = 0 := by
  classical
  simp [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence]

/-- Any remote response matrix canonically gives refined posterior influence
data with the direct local coefficient replacing the fallback value one. -/
noncomputable def
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData.toRefinedInfluenceData
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    (R :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
        H N hN beta hbeta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
      H N hN beta hbeta B := by
  classical
  let Dold := R.toNonstrictInfluenceData B
  refine
    { influence :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
          H beta R.epsilon
      influence_nonneg :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence_nonneg
          H beta hbeta R.epsilon R.epsilon_nonneg
      influence_diagonal_zero :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence_diagonal
          H beta R.epsilon
      conditionalIntegral_difference_abs_le := ?_ }
  intro target source A C hAgree phi hphi hphiBound
  by_cases hdiag : source = target
  · subst source
    have hMeasure :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
            H N hN beta hbeta B A target =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
            H N hN beta hbeta B C target :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure_eq_of_agreeOffTarget
        H N hN beta hbeta B A C target hAgree
    rw [hMeasure]
    simp [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence]
  · by_cases hlocal :
      periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source
    · let p :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H N hN beta hbeta B A target
      let q :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H N hN beta hbeta B C target
      have hp : Continuous p := by
        simpa [p] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_continuous
            H N hN beta hbeta B A target
      have hq : Continuous q := by
        simpa [q] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity_continuous
            H N hN beta hbeta B C target
      have hAeq :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditional_integral_eq_densityIntegral
          H N hN beta hbeta B A target phi hphi
      have hCeq :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditional_integral_eq_densityIntegral
          H N hN beta hbeta B C target phi hphi
      have hHalf :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalHalfL1_le_directOneSource
          H N hN beta hbeta B A C target source hdiag hAgree
      have hTest :=
        continuous_probabilityDensity_boundedTest_expectation_sub_abs_le_halfL1
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
          phi p q hphi hp hq
          1 (by norm_num) hphiBound
      rw [hAeq, hCeq]
      calc
        |(∫ g, phi g * p g
            ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) -
          ∫ g, phi g * q g
            ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)| ≤
            2 * 1 *
              ((2 : ℝ)⁻¹ *
                ∫ g, |p g - q g|
                  ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
          hTest
        _ ≤
            2 *
              periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
                beta := by
          have hHalf' :
              (2 : ℝ)⁻¹ *
                  ∫ g, |p g - q g|
                    ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) ≤
                periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
                  beta := by
            simpa [
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalHalfL1,
              p, q] using hHalf
          nlinarith
        _ =
            2 *
              periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
                H beta R.epsilon target source := by
          simp [
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence,
            hdiag, hlocal]
    · have hOld :=
        Dold.conditionalIntegral_difference_abs_le
          target source A C hAgree phi hphi hphiBound
      have hDoldInfluence :
          Dold.influence target source =
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
              beta (R.epsilon target source) := by
        dsimp [Dold]
        change
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence
              H beta R.epsilon target source =
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
              beta (R.epsilon target source)
        simp [
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence,
          hdiag, hlocal]
      rw [hDoldInfluence] at hOld
      simpa [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence,
        hdiag, hlocal] using hOld

/-- First-bootstrap refined influence data: direct local source control plus the
uniform response-derived remote coefficient. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapRefinedInfluenceData
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
      H N hN beta hbeta B :=
  (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapRemoteExpectationResponseMatrixData
    H N hN beta hbeta k).toRefinedInfluenceData B

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius_zero
    (H : ℕ)
    (k : ℕ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
        H 0 k = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth]

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapRefinedInfluenceData_influence_zero
    (H N : ℕ)
    (hN : 0 < N)
    (k : ℕ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapRefinedInfluenceData
      H N hN 0 (by norm_num) k B).influence target source = 0 := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapRefinedInfluenceData
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData.toRefinedInfluenceData
  simp [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapRemoteExpectationResponseMatrixData,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence]

end

end MathlibAnalytic
end MGAP4D
