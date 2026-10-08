import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarCanonicalWeightedSqrtError
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumWilsonDensityHaarWitness
import MGAP4D.MathlibAnalytic.RealL2ExternalTensor
import Mathlib.Tactic

/-!
# P4-Q1: integrate the genuine Wilson one-link sqrt-ratio error in L²

The canonical continuous representative W_c of the ORIGINAL Wilson
ground-state joint density satisfies a local symmetric Harnack
bound with factor exp(16 beta). The previous unit proved that the
pointwise squared sqrt-ratio deviation is <= (exp(16 beta)-1)^2.

This file now constructs, in the ORIGINAL ordered pair-Haar L²,
an actual one-link sqrt-ratio error vector and proves its squared
L² norm is bounded by (exp(16 beta)-1)^2 independently of finite H.

It then transports this L² error by the EXISTING original
half-density linear isometry U_beta into the ORIGINAL genuine
ground-state joint L² law. This is a quantitative norm bound for
an explicit joint L² approximation of the actual U_beta(1), not
a candidate under any surrogate measure.

A separate next step will identify the transported candidate's
a.e. representative with 1/sqrt(W_c(A,B[e<-1])) and prove retained-
sigma-algebra measurability. Without that identification, the
result is NOT yet an unconditional uniform bound on the full
posterior conditional-expectation residual sum. Dobrushin is not
used, and no continuum claim is made.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

/-- On a probability carrier, a pointwise L²-square bound controls
the genuine Hilbert squared norm with no density or cardinality
loss. -/
theorem realL2_norm_sq_le_of_ae_pointwise_sq_le_probability
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) (C : ℝ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ ^ 2 ≤ C) :
    ‖f‖ ^ 2 ≤ C := by
  rw [realL2_norm_sq_eq_integral_norm_sq]
  calc
    (∫ a, ‖f a‖ ^ 2 ∂μ) ≤ ∫ _a, C ∂μ := by
      apply integral_mono_ae
      · exact (memLp_two_iff_integrable_sq_norm
          (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)
      · exact integrable_const C
      · exact h
    _ = C := by simp

local instance p4Q1L2TopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q1L2CompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q1L2SecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q1L2MeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q1L2BorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q1L2SpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The exact original-canonical Wilson sqrt ratio error, on the
original ORDERED pair-Haar carrier, at one true right link e.
No quotient representative is evaluated at exceptional points. -/
noncomputable def originalWilsonContinuousPhysicalJointRightLinkSqrtErrorFunction
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) : ℝ :=
  1 - Real.sqrt
    (originalWilsonContinuousPhysicalJointWeight H beta hbeta z /
      originalWilsonContinuousPhysicalJointWeight H beta hbeta
        (z.1, Function.update z.2 e
          (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)))

/-- The original canonical Wilson pointwise sqrt-ratio error is
continuous on the actual compact pair-boundary space, in particular
a.e. strongly measurable under the true pair-Haar law. -/
theorem originalWilsonContinuousPhysicalJointRightLinkSqrtErrorFunction_continuous
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (originalWilsonContinuousPhysicalJointRightLinkSqrtErrorFunction
        H beta hbeta e) := by
  classical
  let G := Matrix.specialUnitaryGroup (Fin 2) ℂ
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  have hupdate : Continuous (fun B : X => Function.update B e (1 : G)) := by
    apply continuous_pi
    intro k
    by_cases hk : k = e
    · subst k
      simpa using (continuous_const : Continuous (fun _B : X => (1 : G)))
    · simpa [hk] using (continuous_apply k : Continuous (fun B : X => B k))
  have hfreeze : Continuous
      (fun z : X × X => (z.1, Function.update z.2 e (1 : G))) :=
    continuous_fst.prodMk (hupdate.comp continuous_snd)
  have hW : Continuous
      (originalWilsonContinuousPhysicalJointWeight H beta hbeta) :=
    originalWilsonContinuousPhysicalJointWeight_continuous H beta hbeta
  have hratio : Continuous (fun z : X × X =>
      originalWilsonContinuousPhysicalJointWeight H beta hbeta z /
        originalWilsonContinuousPhysicalJointWeight H beta hbeta
          (z.1, Function.update z.2 e (1 : G))) :=
    hW.div (hW.comp hfreeze) (fun z =>
      ne_of_gt (originalWilsonContinuousPhysicalJointWeight_pos H beta hbeta
        (z.1, Function.update z.2 e (1 : G))))
  exact continuous_const.sub (Real.continuous_sqrt.comp hratio)

/-- One original pair-Haar sqrt-ratio error is L²: its squared
pointwise norm is bounded by (exp(16 beta)-1)^2 independently
of the spatial extent. -/
theorem originalWilsonContinuousPhysicalJointRightLinkSqrtErrorFunction_memLp
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    MemLp
      (originalWilsonContinuousPhysicalJointRightLinkSqrtErrorFunction
        H beta hbeta e) 2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  letI : IsProbabilityMeasure ν := by
    dsimp [ν, periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
    infer_instance
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure]
    infer_instance
  let f := originalWilsonContinuousPhysicalJointRightLinkSqrtErrorFunction
    H beta hbeta e
  have hf : AEStronglyMeasurable f μ :=
    (originalWilsonContinuousPhysicalJointRightLinkSqrtErrorFunction_continuous
      H beta hbeta e).aestronglyMeasurable
  have hR : 0 ≤ Real.exp (16 * beta) - 1 := by
    have hx : 0 ≤ (16 : ℝ) * beta := mul_nonneg (by norm_num) hbeta
    have hle := Real.add_one_le_exp (16 * beta)
    linarith
  have hbound : ∀ᵐ z ∂μ, ‖f z‖ ≤ Real.exp (16 * beta) - 1 := by
    apply Filter.Eventually.of_forall
    intro z
    have hs :
        (f z) ^ 2 ≤ (Real.exp (16 * beta) - 1) ^ 2 :=
      originalWilsonContinuousPhysicalJointWeight_rightLink_sqrtRatio_sq_le
        H beta hbeta z.1 z.2 e
    have h := abs_le.mpr (show
        -(Real.exp (16 * beta) - 1) ≤ f z ∧
          f z ≤ Real.exp (16 * beta) - 1 by
      nlinarith [hs, sq_nonneg (f z + (Real.exp (16 * beta) - 1)),
        sq_nonneg (f z - (Real.exp (16 * beta) - 1))])
    simpa [Real.norm_eq_abs] using h
  exact MemLp.of_bound hf (Real.exp (16 * beta) - 1) hbound

/-- Actual ORIGINAL pair-Haar L² error vector, not just a pointwise
regularity heuristic. -/
noncomputable def originalWilsonContinuousPhysicalJointRightLinkSqrtErrorL2
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2 :=
  (originalWilsonContinuousPhysicalJointRightLinkSqrtErrorFunction_memLp
    H beta hbeta e).toLp
      (originalWilsonContinuousPhysicalJointRightLinkSqrtErrorFunction
        H beta hbeta e)

/-- Uniform-in-volume one-link original pair-Haar L² squared error.
The original pair-Haar law has total mass one. -/
theorem originalWilsonContinuousPhysicalJointRightLinkSqrtErrorL2_norm_sq_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ‖originalWilsonContinuousPhysicalJointRightLinkSqrtErrorL2
      H beta hbeta e‖ ^ 2 ≤
      (Real.exp (16 * beta) - 1) ^ 2 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  letI : IsProbabilityMeasure ν := by
    dsimp [ν, periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
    infer_instance
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure]
    infer_instance
  let f := originalWilsonContinuousPhysicalJointRightLinkSqrtErrorFunction H beta hbeta e
  let hmem := originalWilsonContinuousPhysicalJointRightLinkSqrtErrorFunction_memLp
    H beta hbeta e
  have hrep : (fun z => (hmem.toLp f) z) =ᵐ[μ] f :=
    MemLp.coeFn_toLp hmem
  have hbound :
      ∀ᵐ z ∂μ, ‖(hmem.toLp f) z‖ ^ 2 ≤
        (Real.exp (16 * beta) - 1) ^ 2 := by
    filter_upwards [hrep] with z hz
    rw [hz]
    change ‖f z‖ ^ 2 ≤ (Real.exp (16 * beta) - 1) ^ 2
    simpa [f, originalWilsonContinuousPhysicalJointRightLinkSqrtErrorFunction,
      Real.norm_eq_abs, sq_abs] using
      (originalWilsonContinuousPhysicalJointWeight_rightLink_sqrtRatio_sq_le
        H beta hbeta z.1 z.2 e)
  exact realL2_norm_sq_le_of_ae_pointwise_sq_le_probability
    (hmem.toLp f) _ hbound

/-- Original-genuine-joint L² approximant built solely through
the EXISTING half-density isometric equivalence U_beta. -/
noncomputable def originalWilsonCanonicalRightLinkJointVacuumApproximant
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H 2 (Nat.zero_lt_succ 1) beta hbeta :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H 2 (Nat.zero_lt_succ 1) beta hbeta)
    ((Lp.const 2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)
      (1 : ℝ)) -
      originalWilsonContinuousPhysicalJointRightLinkSqrtErrorL2 H beta hbeta e)

/-- Original genuine posterior-joint L² vacuum approximated with
ONE right-link sqrt-ratio error, no replacement posterior:
the squared L² error is ≤ (exp(16 beta)-1)^2. This norm is for the
ACTUAL joint law, with no artificial two-sided density estimate.
Retained measurability is a separate bridge. -/
theorem originalWilsonCanonicalRightLinkJointVacuumApproximant_error_sq_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ‖originalGroundStateJointTransportedPairHaarOne H 2
        (Nat.zero_lt_succ 1) beta hbeta -
      originalWilsonCanonicalRightLinkJointVacuumApproximant
        H beta hbeta e‖ ^ 2 ≤
      (Real.exp (16 * beta) - 1) ^ 2 := by
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H 2 (Nat.zero_lt_succ 1) beta hbeta
  let one : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2 :=
    Lp.const 2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2)
      (1 : ℝ)
  let err := originalWilsonContinuousPhysicalJointRightLinkSqrtErrorL2 H beta hbeta e
  change ‖U one - U (one - err)‖ ^ 2 ≤ _
  have heq : one - (one - err) = err := by abel
  rw [← map_sub, heq, U.norm_map]
  exact originalWilsonContinuousPhysicalJointRightLinkSqrtErrorL2_norm_sq_le
    H beta hbeta e

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
