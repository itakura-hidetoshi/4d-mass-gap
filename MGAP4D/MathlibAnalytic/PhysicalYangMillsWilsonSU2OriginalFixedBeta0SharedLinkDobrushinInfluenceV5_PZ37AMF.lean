import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalInteractingSharedLinkPlaquetteCovarianceV5_PZ37AME
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedCouplingQuadraticAJANoGoThroughThirteenV5_PZ37AKO
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryDobrushinSchurL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinMatrixL2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMF — physical SU(2) Wilson fixed-beta0 strict Dobrushin link influence

AME certified a genuine adjacent physical plaquette pair with shared link and
its FULL interacting Wilson Gibbs covariance (definition/exact density identity).
This new leaf proves a strictly subunit, VOLUME-INDEPENDENT local conditional
link-influence bound for the ORIGINAL finite periodic SU(2) Wilson system at the
UNCHANGED physical beta0 = log(3/2)/64, n = 2(H+1), H > 0.

The theorem-generated Dobrushin matrix controls true *one-link conditional Gibbs
laws* in bounded-test dual total variation and has strict row sums; the finite
Schur estimate also controls its actual link-space l2 action.

THIS IS NOT YET A GIBBS CONNECTED-PLAQUETTE COVARIANCE DECAY THEOREM:
to glue local influences into joint-observable covariance, an independent
coupling/iterated conditional expectation (or Dobrushin covariance comparison)
theorem is required. The centered L2 random-scan Rayleigh field is likewise
NOT discharged here; its assumption cannot be silently removed.
The degenerate n=2 (H=0) torus is excluded since existing shared-plaquette
uniqueness uses n>=3. No modified physics, extra axioms or weaker signatures.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2300000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "beta0" => GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling

local instance p4Q2PZ37AMF_SU2_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2

local instance p4Q2PZ37AMF_neZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  change 2 * (H + 1) ≠ 0
  omega⟩
local instance p4Q2PZ37AMF_SU2_nontrivial : Nontrivial G := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : G => (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace GroundStatePosteriorJoint

/-- Rational quantitative floor on the CURRENT exact SU(2) compact-Haar
high-temperature Dobrushin logarithmic threshold; no numeric approximation. -/
theorem p4Q2PZ37AMF_log_nineteenSeventeenths_ge_twoNineteenths :
    (2 / 19 : ℝ) ≤ Real.log ((19 : ℝ) / 17) := by
  have hLog : Real.log (17 / 19 : ℝ) ≤ (17 / 19 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  have hInv : (17 / 19 : ℝ) = ((19 / 17 : ℝ)⁻¹) := by norm_num
  rw [hInv, Real.log_inv] at hLog
  norm_num at hLog
  linarith only [hLog]

/-- The unchanged original Wilson beta0 is IN the strict compact SU(2)
Dobrushin region. This is quantitative and does not assume a coupling
sequence smallness premise. -/
theorem p4Q2PZ37AMF_originalFixedBeta0_lt_DobrushinThreshold :
    beta0 < Real.log ((19 : ℝ) / 17) / 4 := by
  have hb : beta0 ≤ (1 / 156 : ℝ) :=
    p4Q2PZ37AKO_originalFixedCoupling_le_oneOver156
  have hr := p4Q2PZ37AMF_log_nineteenSeventeenths_ge_twoNineteenths
  have hnum : (1 / 156 : ℝ) < (2 / 19 : ℝ) / 4 := by norm_num
  linarith only [hb, hr, hnum]

/-- Genuine full-Wilson local link influence coefficient at fixed beta0
is strictly less than one, independent of all finite spatial H. -/
theorem p4Q2PZ37AMF_originalFixedBeta0_DobrushinCoefficient_lt_one :
    periodicHypercubicSpecialUnitaryDobrushinCoefficient beta0 < 1 := by
  unfold periodicHypercubicSpecialUnitaryDobrushinCoefficient
  exact periodicHypercubicSpecialUnitary_eighteen_mul_eta_lt_one_of_beta_lt
    beta0 p4Q2PZ37AMF_originalFixedBeta0_lt_DobrushinThreshold

/-- The *actual* periodic SU(2) Wilson one-link conditional laws (not an
abstract probability family) have a strict Dobrushin matrix for every H>0. -/
noncomputable def p4Q2PZ37AMF_originalFixedBeta0PhysicalDobrushinMatrix
    (H : ℕ) (hH : 0 < H) :
    ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) 2 (by norm_num)
        beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) := by
  have hn : 3 ≤ PeriodicHypercubicEvenSideLength H := by
    change 3 ≤ 2 * (H + 1)
    omega
  exact periodicHypercubicSpecialUnitaryDobrushinMatrixData
    (PeriodicHypercubicEvenSideLength H) 2 hn (by norm_num)
    beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
    p4Q2PZ37AMF_originalFixedBeta0_lt_DobrushinThreshold

/-- Every full SU(2) Gibbs conditional-law influence row at original beta0
is strictly subunit, for all H>0 and every true physical link. -/
theorem p4Q2PZ37AMF_originalFixedBeta0PhysicalInfluence_rowSum_lt_one
    (H : ℕ) (hH : 0 < H)
    (target : PeriodicHypercubicEvenEdge H) :
    (∑ source : PeriodicHypercubicEvenEdge H,
      (p4Q2PZ37AMF_originalFixedBeta0PhysicalDobrushinMatrix
        H hH).influence target source) < 1 := by
  exact continuous_compact_oriented_dobrushin_rowSum_lt_one
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) 2 (by norm_num)
      beta0 p4Q2PZ37ADC_fixedCoupling_pos.le)
    (p4Q2PZ37AMF_originalFixedBeta0PhysicalDobrushinMatrix H hH) target

/-- Explicit exact conditional-EXPECTATION comparison for the ORIGINAL full
interacting SU(2) Wilson Gibbs one-link resampling. The background fields
A and B differ in at most one real lattice link; no product-Gibbs assumption. -/
theorem p4Q2PZ37AMF_originalFixedBeta0PhysicalConditionalIntegral_abs_le
    (H : ℕ) (hH : 0 < H)
    (target source : PeriodicHypercubicEvenEdge H)
    (A B : PeriodicHypercubicEvenEdge H → G)
    (hAgree :
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) 2 (by norm_num)
        beta0 p4Q2PZ37ADC_fixedCoupling_pos.le).base.AgreeOffLink
          A B source)
    (phi : G → ℝ)
    (hphi : StronglyMeasurable phi)
    (hphiBound : ∀ g : G, |phi g| ≤ 1) :
    |(∫ g, phi g ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) 2 (by norm_num)
        beta0 p4Q2PZ37ADC_fixedCoupling_pos.le).singleLinkConditionalMeasure
          A target) -
      (∫ g, phi g ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) 2 (by norm_num)
        beta0 p4Q2PZ37ADC_fixedCoupling_pos.le).singleLinkConditionalMeasure
          B target)| ≤
      2 * (p4Q2PZ37AMF_originalFixedBeta0PhysicalDobrushinMatrix
        H hH).influence target source := by
  exact (p4Q2PZ37AMF_originalFixedBeta0PhysicalDobrushinMatrix
    H hH).conditionalIntegral_difference_abs_le
      target source A B hAgree phi hphi hphiBound

/-- Uniform finite-dimensional Schur contraction of the actual physical
compact SU(2) Wilson Gibbs *influence matrix* at fixed beta0.
This is link influence l2, NOT the OS transfer or connected Gibbs covariance. -/
theorem p4Q2PZ37AMF_originalFixedBeta0PhysicalInfluence_l2_nonexpansive
    (H : ℕ) (hH : 0 < H)
    (v : PeriodicHypercubicEvenEdge H → ℝ) :
    (∑ target : PeriodicHypercubicEvenEdge H,
      (∑ source : PeriodicHypercubicEvenEdge H,
        periodicHypercubicSpecialUnitaryDobrushinInfluence
          (PeriodicHypercubicEvenSideLength H) 2 (by norm_num)
          beta0 p4Q2PZ37ADC_fixedCoupling_pos.le target source *
          v source) ^ 2) ≤
      ∑ source : PeriodicHypercubicEvenEdge H, v source ^ 2 := by
  have hn : 3 ≤ PeriodicHypercubicEvenSideLength H := by
    change 3 ≤ 2 * (H + 1)
    omega
  let alpha := periodicHypercubicSpecialUnitaryDobrushinCoefficient beta0
  have hAlpha0 : 0 ≤ alpha := by
    dsimp [alpha, periodicHypercubicSpecialUnitaryDobrushinCoefficient,
      periodicHypercubicSpecialUnitaryDobrushinEta]
    exact mul_nonneg (by norm_num)
      (compactHaarOscillationInfluence_nonneg
        (mul_nonneg p4Q2PZ37ADC_fixedCoupling_pos.le
          (by norm_num : (0 : ℝ) ≤ 4)))
  have hAlphaLt : alpha < 1 := by
    exact p4Q2PZ37AMF_originalFixedBeta0_DobrushinCoefficient_lt_one
  have hAlphaSq : alpha ^ 2 ≤ 1 := by nlinarith only [hAlpha0, hAlphaLt]
  have hSum : 0 ≤ ∑ source : PeriodicHypercubicEvenEdge H, v source ^ 2 :=
    Finset.sum_nonneg (fun source _ => sq_nonneg (v source))
  have hSchur :=
    periodicHypercubicSpecialUnitaryDobrushinInfluence_l2_sq_le
      (PeriodicHypercubicEvenSideLength H) 2 hn (by norm_num)
      beta0 p4Q2PZ37ADC_fixedCoupling_pos.le v
  calc
    (∑ target : PeriodicHypercubicEvenEdge H,
      (∑ source : PeriodicHypercubicEvenEdge H,
        periodicHypercubicSpecialUnitaryDobrushinInfluence
          (PeriodicHypercubicEvenSideLength H) 2 (by norm_num)
          beta0 p4Q2PZ37ADC_fixedCoupling_pos.le target source *
          v source) ^ 2) ≤
        alpha ^ 2 * ∑ source : PeriodicHypercubicEvenEdge H, v source ^ 2 :=
          hSchur
    _ ≤ 1 * ∑ source : PeriodicHypercubicEvenEdge H, v source ^ 2 :=
      mul_le_mul_of_nonneg_right hAlphaSq hSum
    _ = ∑ source : PeriodicHypercubicEvenEdge H, v source ^ 2 := by ring

/-- The strict current SU(2) Gibbs link influence estimate applies to a
specific TRUE physical edge shared by AME's two distinct plaquettes.
Neither neighboring plaquettes nor their Gibbs covariance are factorized. -/
theorem p4Q2PZ37AMF_originalPrimaryNeighbor_sharedEdge_strictInfluence
    (H : ℕ) (hH : 0 < H) :
    ∃ e : PeriodicHypercubicEvenEdge H,
      periodicHypercubicPlaquetteTouchesEdge
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenPrimarySpatialPlaquette H) e ∧
      periodicHypercubicPlaquetteTouchesEdge
        (PeriodicHypercubicEvenSideLength H)
        (p4Q2PZ37AME_originalPrimarySharedLinkNeighbor H) e ∧
      (∑ source : PeriodicHypercubicEvenEdge H,
        (p4Q2PZ37AMF_originalFixedBeta0PhysicalDobrushinMatrix
          H hH).influence e source) < 1 := by
  rcases p4Q2PZ37AME_originalPrimarySharedLinkNeighbor_physicalEdge H with
    ⟨e, heP, heQ⟩
  exact ⟨e, heP, heQ,
    p4Q2PZ37AMF_originalFixedBeta0PhysicalInfluence_rowSum_lt_one
      H hH e⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMF_log_nineteenSeventeenths_ge_twoNineteenths
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMF_originalFixedBeta0_lt_DobrushinThreshold
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMF_originalFixedBeta0_DobrushinCoefficient_lt_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMF_originalFixedBeta0PhysicalDobrushinMatrix
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMF_originalFixedBeta0PhysicalInfluence_rowSum_lt_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMF_originalFixedBeta0PhysicalConditionalIntegral_abs_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMF_originalFixedBeta0PhysicalInfluence_l2_nonexpansive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMF_originalPrimaryNeighbor_sharedEdge_strictInfluence
