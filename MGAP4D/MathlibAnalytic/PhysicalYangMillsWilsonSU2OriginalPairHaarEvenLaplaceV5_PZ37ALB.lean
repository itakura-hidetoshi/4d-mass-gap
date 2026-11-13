import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalDiagonalCenterTwistCrossingV5_PZ37ALA
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALB — true original pair-Haar even crossing Laplace integral

ALA has certified original SU(2) crossing-kernel pointwise invariance,
centered ZW pair-source oddness, and the actual diagonal center twist
preserving the original pair product Haar. We now descend from those
separate properties to a genuine equality of original Haar integrals.

The Laplace integral introduced here is ONLY a named scalar integral
over the original two-boundary product Haar using the same original
crossing kernel and same original ZW source values. It is NOT a new
physical model, Gaussian approximation, or modified transfer.

The exact parity L_H(beta,t)=L_H(beta,-t) permits the symmetrized
cosh-like expression, and the elementary exp tangents give L>=Zcross.
This recovers the true original AIW partition floor, but a NEW
quantitative second-moment gain still needs a separate certified
cosh lower bound and exact source-pair moment. No H22 true mass
upper bound, AJA decision, Hamiltonian or continuum mass gap claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ALB_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ALB_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ALB_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ALB_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ALB_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ALB_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pairH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "T" => p4Q2PZ37AHW_originalCenterTwist H
local notation "KC" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H

local instance p4Q2PZ37ALB_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- A scalar derived from EXACT original SU(2) pair-Haar/crossing/source,
not a new transfer operator or an assumed Gaussian law. -/
def p4Q2PZ37ALB_originalPairCrossingLaplace (beta t : ℝ) : ℝ :=
  ∫ P : Cfg × Cfg,
    KC beta P.1 P.2 *
      Real.exp (t * (fCont P.1 + fCont P.2)) ∂pairH

local notation "Lpair" => p4Q2PZ37ALB_originalPairCrossingLaplace H

/-- Genuine pair-Haar integrability for arbitrary real beta and t.
Both original source representatives and crossing kernel are continuous
on the actual compact original two-boundary space. -/
theorem p4Q2PZ37ALB_originalPairLaplace_integrable (beta t : ℝ) :
    Integrable (fun P : Cfg × Cfg =>
      KC beta P.1 P.2 *
        Real.exp (t * (fCont P.1 + fCont P.2))) pairH := by
  have hKC : Continuous (fun P : Cfg × Cfg =>
      KC beta P.1 P.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_continuous
      H 2 beta
  have hf1 : Continuous (fun P : Cfg × Cfg => fCont P.1) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_fst
  have hf2 : Continuous (fun P : Cfg × Cfg => fCont P.2) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_snd
  exact (hKC.mul (Real.continuous_exp.comp
    (continuous_const.mul (hf1.add hf2)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- True original weighted pair-Haar Laplace integral is EVEN in t.
This uses ALA's proven global pair MeasurePreserving, not a guessed
equality between conditional Wilson posterior distributions. -/
theorem p4Q2PZ37ALB_originalPairLaplace_even (beta t : ℝ) :
    Lpair beta t = Lpair beta (-t) := by
  let M : Cfg × Cfg → Cfg × Cfg := Prod.map T T
  have hPres : MeasurePreserving M pairH pairH :=
    p4Q2PZ37ALA_originalPairHaar_diagonalCenter_preserving H
  have hMap : Measure.map M pairH = pairH := hPres.map_eq
  have hIntegrable := p4Q2PZ37ALB_originalPairLaplace_integrable H beta t
  have hMeasMap : AEStronglyMeasurable (fun P : Cfg × Cfg =>
      KC beta P.1 P.2 *
        Real.exp (t * (fCont P.1 + fCont P.2))) (Measure.map M pairH) := by
    rw [hMap]
    exact hIntegrable.aestronglyMeasurable
  calc
    Lpair beta t =
        ∫ P : Cfg × Cfg,
          KC beta P.1 P.2 *
            Real.exp (t * (fCont P.1 + fCont P.2)) ∂pairH := rfl
    _ = ∫ P : Cfg × Cfg,
          KC beta P.1 P.2 *
            Real.exp (t * (fCont P.1 + fCont P.2)) ∂Measure.map M pairH := by
      rw [hMap]
    _ = ∫ P : Cfg × Cfg,
          KC beta (T P.1) (T P.2) *
            Real.exp (t * (fCont (T P.1) + fCont (T P.2))) ∂pairH := by
      exact MeasureTheory.integral_map hPres.measurable.aemeasurable hMeasMap
    _ = Lpair beta (-t) := by
      unfold p4Q2PZ37ALB_originalPairCrossingLaplace
      apply integral_congr_ae
      filter_upwards with P
      rw [p4Q2PZ37ALA_originalCrossingKernel_diagonalCenter H beta P.1 P.2,
        p4Q2PZ37ALA_originalPairSource_diagonalCenter_odd H P.1 P.2]
      congr 1
      ring

/-- Exactly the same pair Laplace has a pointwise-symmetrized
original measure expression, without any alternative probability law. -/
theorem p4Q2PZ37ALB_originalPairLaplace_symmetrized (beta t : ℝ) :
    Lpair beta t =
      ∫ P : Cfg × Cfg, KC beta P.1 P.2 *
        ((Real.exp (t * (fCont P.1 + fCont P.2)) +
          Real.exp (-t * (fCont P.1 + fCont P.2))) / 2) ∂pairH := by
  have hPlus := p4Q2PZ37ALB_originalPairLaplace_integrable H beta t
  have hMinus := p4Q2PZ37ALB_originalPairLaplace_integrable H beta (-t)
  have hEven := p4Q2PZ37ALB_originalPairLaplace_even H beta t
  have hSum :
      (∫ P : Cfg × Cfg, KC beta P.1 P.2 *
        ((Real.exp (t * (fCont P.1 + fCont P.2)) +
          Real.exp (-t * (fCont P.1 + fCont P.2))) / 2) ∂pairH) =
      (Lpair beta t + Lpair beta (-t)) / 2 := by
    calc
      _ = ∫ P : Cfg × Cfg,
          (KC beta P.1 P.2 *
            Real.exp (t * (fCont P.1 + fCont P.2)) +
           KC beta P.1 P.2 *
            Real.exp (-t * (fCont P.1 + fCont P.2))) / 2 ∂pairH := by
        apply integral_congr_ae
        filter_upwards with P
        ring
      _ = (∫ P : Cfg × Cfg,
          KC beta P.1 P.2 *
            Real.exp (t * (fCont P.1 + fCont P.2)) +
          KC beta P.1 P.2 *
            Real.exp (-t * (fCont P.1 + fCont P.2)) ∂pairH) / 2 := by
        rw [integral_div]
      _ = (Lpair beta t + Lpair beta (-t)) / 2 := by
        rw [integral_add hPlus hMinus]
        rfl
  rw [hSum, ← hEven]
  ring

/-- At t=0, the ACTUAL original crossing product partition, not
the full physical Wilson one-slab partition, is recovered exactly. -/
theorem p4Q2PZ37ALB_originalPairLaplace_zero (beta : ℝ) :
    Lpair beta 0 = Zcross beta := by
  unfold p4Q2PZ37ALB_originalPairCrossingLaplace
  simp only [zero_mul, Real.exp_zero, mul_one]
  exact p4Q2PZ37AIV_originalCrossingKernel_pair_integral H beta

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALB_originalPairCrossingLaplace
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALB_originalPairLaplace_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALB_originalPairLaplace_even
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALB_originalPairLaplace_symmetrized
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALB_originalPairLaplace_zero
