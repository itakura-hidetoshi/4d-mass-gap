import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarIntegratedHaarFiberVarianceFubini
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUnconditionalProjectionCommutation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# P4-Q2-DI: actual original pair-Haar fiber variance = true Hilbert L² defect

DH proved the full ORIGINAL spatial pair-Haar joint-square identity for
every literal physical left/right SU(N) Haar coordinate; DA proved that
this literal coordinate Haar mean agrees a.e. with CR's true orthogonal
conditional-expectation L² projection on bounded representatives.

Here we finally identify their actual Hilbert squared defect norm with
the genuine scalar full-joint squared difference and, using DH, with
the integrated off-coordinate Haar fiber variance. This closes the
single-coordinate analytic equality needed for the next quantitative
comparison with the genuine original Wilson mass-weighted Dirichlet form
and its twelve-color physical normalization.

The theorem is for bounded strongly measurable representatives of real
L² classes under the actual pair-Haar law. There is no evaluation of an
arbitrary quotient representative at fixed fibers; F represents f a.e.
The interacting positive-beta Wilson conditionals are not asserted to
commute; finite-volume Wilson coercivity and the continuum mass gap are
separate subsequent obligations.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

section ActualPairHaar
variable (H N : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "I" =>
  PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "muH" => normalizedCompactHaar G
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "JH" => Lp ℝ 2 muPair
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H N
local notation "Mean" => p4Q2CU_actualPairHaarCoordinateMean H N

/-- The ACTUAL original independent pair-Haar Hilbert-L² off-link
orthogonal projection defect has exactly the global squared residual
integral of a bounded strongly measurable representative and its
literal original physical single-link Haar mean. -/
theorem p4Q2DI_actualPairHaarCoordinateDefect_normSq_eq_CUmeanSquareIntegral
    (i : I) (f : JH)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M)
    (hEq : F =ᵐ[muPair] (f : Joint → ℝ)) :
    ‖f - P i f‖ ^ 2 =
      ∫ z : Joint, (F z - Mean i F z) ^ 2 ∂muPair := by
  let D : JH := f - P i f
  have hProj :
      ((P i f : JH) : Joint → ℝ) =ᵐ[muPair] Mean i F :=
    p4Q2DA_actualPairHaarProjection_ae_eq_CUmean
      H N i f F hF M hM hEq
  have hDiff :
      (D : Joint → ℝ) =ᵐ[muPair]
        (fun z : Joint => F z - Mean i F z) := by
    filter_upwards [Lp.coeFn_sub f (P i f), hEq, hProj] with z hz hf hp
    calc
      (D : Joint → ℝ) z =
          (f : Joint → ℝ) z - ((P i f : JH) : Joint → ℝ) z := hz
      _ = F z - Mean i F z := by rw [← hf, hp]
  calc
    ‖f - P i f‖ ^ 2 = inner ℝ D D := by
      exact (real_inner_self_eq_norm_sq D).symm
    _ = ∫ z : Joint, inner ℝ (D z) (D z) ∂muPair :=
      L2.inner_def D D
    _ = ∫ z : Joint, (F z - Mean i F z) ^ 2 ∂muPair := by
      apply integral_congr_ae
      filter_upwards [hDiff] with z hz
      rw [hz, real_inner_self_eq_norm_sq]
      simp [Real.norm_eq_abs, sq_abs]

/-- The integrated genuine one-SU(N)-link pair-Haar fiber variance is
EXACTLY the extended-real coercivity quantity of the ACTUAL original
CR Hilbert-L² off-coordinate projection (on any bounded representative).
This is the bridge from literal Haar Fubini to the genuine coordinate
defect appearing in the DC Efron--Stein inequality. -/
theorem p4Q2DI_actualPairHaarIntegratedFiberVariance_eq_L2_defect_sq
    (i : I) (f : JH)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M)
    (hEq : F =ᵐ[muPair] (f : Joint → ℝ)) :
    (∫⁻ a : {j : I // j ≠ i} → G,
      evariance (fun u : G =>
        F ((p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i).symm (a, u)))
        muH
      ∂(Measure.pi (fun _ : {j : I // j ≠ i} => muH))) =
      ENNReal.ofReal (‖f - P i f‖ ^ 2) := by
  let D : JH := f - P i f
  have hProj :
      ((P i f : JH) : Joint → ℝ) =ᵐ[muPair] Mean i F :=
    p4Q2DA_actualPairHaarProjection_ae_eq_CUmean
      H N i f F hF M hM hEq
  have hDiff :
      (D : Joint → ℝ) =ᵐ[muPair]
        (fun z : Joint => F z - Mean i F z) := by
    filter_upwards [Lp.coeFn_sub f (P i f), hEq, hProj] with z hz hf hp
    calc
      (D : Joint → ℝ) z =
          (f : Joint → ℝ) z - ((P i f : JH) : Joint → ℝ) z := hz
      _ = F z - Mean i F z := by rw [← hf, hp]
  have hSq : (fun z : Joint => (D z) ^ 2) =ᵐ[muPair]
      (fun z : Joint => (F z - Mean i F z) ^ 2) := by
    filter_upwards [hDiff] with z hz
    rw [hz]
  have hDInt : Integrable (fun z : Joint => (D z) ^ 2) muPair :=
    (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable D)).mp
      (Lp.memLp D)
  have hInt : Integrable
      (fun z : Joint => (F z - Mean i F z) ^ 2) muPair :=
    hDInt.congr hSq
  have hNonneg : 0 ≤ᵐ[muPair]
      (fun z : Joint => (F z - Mean i F z) ^ 2) :=
    Filter.Eventually.of_forall (fun z => sq_nonneg (F z - Mean i F z))
  calc
    (∫⁻ a : {j : I // j ≠ i} → G,
      evariance (fun u : G =>
        F ((p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i).symm (a, u)))
        muH
      ∂(Measure.pi (fun _ : {j : I // j ≠ i} => muH))) =
        ∫⁻ z : Joint,
          ENNReal.ofReal ((F z - Mean i F z) ^ 2) ∂muPair :=
      p4Q2DH_actualPairHaarIntegratedFiberVariance_eq_CUmeanSquare
        H N i F hF
    _ = ENNReal.ofReal
        (∫ z : Joint, (F z - Mean i F z) ^ 2 ∂muPair) :=
      (ofReal_integral_eq_lintegral_ofReal hInt hNonneg).symm
    _ = ENNReal.ofReal (‖f - P i f‖ ^ 2) := by
      rw [← p4Q2DI_actualPairHaarCoordinateDefect_normSq_eq_CUmeanSquareIntegral
        H N i f F hF M hM hEq]

end ActualPairHaar
end

end MathlibAnalytic
end MGAP4D
