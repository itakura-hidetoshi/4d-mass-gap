import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorHellingerSourceSeparationV5_GO
import Mathlib.Tactic

/-!
# P4-Q2-GP: explicit volume-uniform true Wilson Hellinger certificate

GO proved the genuine original SU(2) Wilson posterior squared Hellinger
separation dominates the exact original density-contrast Haar L² quantity
Q divided by 4*exp(16*beta). GA already proved its original finite-volume
Wilson Q lower bound, beta² exp(-32*beta) V_SU2.

Consequently genuine interacting Wilson posterior rows satisfy
  HellingerSq >= beta² exp(-32 beta) V_SU2 / (4 exp(16 beta)).
This lower bound is independent of finite spatial volume H, physical link
e and background B. It still vanishes as beta tends to zero.

A second quantitative statement uses the SAME ORIGINAL signed physical
joint receiver from GN/GO. A directly testable nonnegative lower bound on
its updated-link values transfers linearly to the SOURCE-WEIGHTED
Hellinger mass. Finally specialize the statement to the actual fine
right Krylov and original left-three-mode signed physical inputs, keeping
fine beta(n+1) INSIDE the physical sources and frozen beta(n) in the
posterior, receiver and Wilson certificate.

These Hellinger certificates are not identified with the signed GI
expectation gap. No actual nonzero signed source-frame, positive
Krylov coefficient minimum eigenvalue, volume-summable source response,
H1-C3 closure or continuum Yang--Mills mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1700000
set_option synthInstance.maxHeartbeats 700000

local instance p4Q2GP_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GP_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GP_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GP_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GP_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section Frozen

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "μ" => normalizedCompactHaar Gauge
local notation "P0" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
    H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H)
local notation "P1" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
    H 2 (by norm_num) beta hbeta

/-- Explicit H/e/right-background-uniform lower bound for the squared
Hellinger separation of two ACTUAL interacting Wilson posteriors.
This is a posterior-law estimate, not a signed source-frame estimate. -/
theorem p4Q2GP_originalWilsonHellinger_ge_universalSU2Variance
    (right : Cfg) (e : Link) :
    (Real.exp (-32 * beta) *
        (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance)) /
        (4 * Real.exp (16 * beta)) ≤
      p4Q2GO_originalWilsonTwoPosteriorHellingerSq H beta hbeta right e := by
  have hC : 0 < 4 * Real.exp (16 * beta) :=
    mul_pos (by norm_num) (Real.exp_pos _)
  apply (div_le_iff₀ hC).2
  calc
    Real.exp (-32 * beta) *
        (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance) ≤
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq H beta hbeta right e :=
        p4Q2GA_originalSU2WilsonPosteriorLeftSensitivityHaarSq_uniform_lower
          H beta hbeta right e
    _ ≤ (4 * Real.exp (16 * beta)) *
        p4Q2GO_originalWilsonTwoPosteriorHellingerSq H beta hbeta right e :=
      p4Q2GO_originalWilsonContrastQ_le_fourExp_mul_Hellinger H beta hbeta right e
    _ = p4Q2GO_originalWilsonTwoPosteriorHellingerSq H beta hbeta right e *
        (4 * Real.exp (16 * beta)) := by ring

/-- A lower bound on the REAL original physical signed receiver at every
SU(2) inserted right link implies the same bound times the exact
genuine-posterior squared Hellinger mass. No receiver positivity is
postulated for arbitrary signed Krylov combinations. -/
theorem p4Q2GP_originalPhysicalReceiverWeightedHellinger_ge_floor
    (f : Phys) (left right : Cfg) (e : Link)
    (m : ℝ) (_hm : 0 ≤ m)
    (hFloor : ∀ g : Gauge, m ≤
      normalizedPhysicalOneSlabJointReceiverProductBCF
        H 2 (by norm_num) beta hbeta f (left, Function.update right e g)) :
    m * p4Q2GO_originalWilsonTwoPosteriorHellingerSq H beta hbeta right e ≤
      p4Q2GO_originalPhysicalReceiverWeightedHellingerMass
        H beta hbeta f left right e := by
  let R : Gauge → ℝ := P0 right e
  let S : Gauge → ℝ := P1 (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
  let G : Gauge → ℝ := fun g => (Real.sqrt (R g) - Real.sqrt (S g)) ^ 2
  let O := normalizedPhysicalOneSlabJointReceiverProductBCF H 2 (by norm_num) beta hbeta f
  let F : Gauge → ℝ := fun g => O (left, Function.update right e g) * G g
  have hR : Continuous R := by
    let ν : Measure Gauge := normalizedCompactHaar Gauge
    change Continuous (continuousNormalizedExp ν
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
        H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H) right e))
    exact continuous_continuousNormalizedExp ν _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H) right e)
  have hS : Continuous S := by
    let ν : Measure Gauge := normalizedCompactHaar Gauge
    change Continuous (continuousNormalizedExp ν
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
        H 2 (by norm_num) beta hbeta (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e))
    exact continuous_continuousNormalizedExp ν _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) beta hbeta (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e)
  have hUp : Continuous (fun g : Gauge => (left, Function.update right e g)) := by
    fun_prop
  have hGCont : Continuous G :=
    (((Real.continuous_sqrt.comp hR).sub
      (Real.continuous_sqrt.comp hS)).pow 2)
  have hGInt : Integrable G μ :=
    hGCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFInt : Integrable F μ :=
    ((O.continuous.comp hUp).mul hGCont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (g : Gauge) : m * G g ≤ F g :=
    mul_le_mul_of_nonneg_right (hFloor g) (sq_nonneg _)
  change m * (∫ g, G g ∂μ) ≤ ∫ g, F g ∂μ
  calc
    m * (∫ g, G g ∂μ) = ∫ g, m * G g ∂μ := by rw [integral_const_mul]
    _ ≤ ∫ g, F g ∂μ := by
      apply integral_mono (hGInt.const_mul _) hFInt
      intro g
      exact hPoint g

/-- Explicit quantitative ORIGINAL physical source-weighted posterior
Hellinger mass lower bound. The source lower bound m is a physical
receiver property to be derived from the genuine Wilson transfer input;
it is NOT an assumed GI expectation-gap frame. -/
theorem p4Q2GP_originalPhysicalReceiverWeightedHellinger_ge_universal
    (f : Phys) (left right : Cfg) (e : Link)
    (m : ℝ) (hm : 0 ≤ m)
    (hFloor : ∀ g : Gauge, m ≤
      normalizedPhysicalOneSlabJointReceiverProductBCF
        H 2 (by norm_num) beta hbeta f (left, Function.update right e g)) :
    m * ((Real.exp (-32 * beta) *
        (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance)) /
        (4 * Real.exp (16 * beta))) ≤
      p4Q2GO_originalPhysicalReceiverWeightedHellingerMass
        H beta hbeta f left right e := by
  have hH := p4Q2GP_originalWilsonHellinger_ge_universalSU2Variance
    H beta hbeta right e
  have hWeighted := p4Q2GP_originalPhysicalReceiverWeightedHellinger_ge_floor
    H beta hbeta f left right e m hm hFloor
  calc
    m * ((Real.exp (-32 * beta) *
        (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance)) /
        (4 * Real.exp (16 * beta))) ≤
      m * p4Q2GO_originalWilsonTwoPosteriorHellingerSq H beta hbeta right e :=
      mul_le_mul_of_nonneg_left hH hm
    _ ≤ p4Q2GO_originalPhysicalReceiverWeightedHellingerMass
      H beta hbeta f left right e := hWeighted

end Frozen

section ActualAdjacent

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" => physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- Actual adjacent-scale fine-right Krylov signed source, not an
artificial vector family: its receiver floor, if physically established,
gives the quantitative FROZEN beta(n) original Wilson Hellinger bound. -/
theorem p4Q2GP_actualFineRightKrylovReceiverWeightedHellinger_ge_universal
    (a : Fin (r + 1) → ℝ) (left right : Cfg) (e : Link)
    (m : ℝ) (hm : 0 ≤ m)
    (hFloor : ∀ g : Gauge, m ≤
      normalizedPhysicalOneSlabJointReceiverProductBCF Hn 2 (by norm_num)
        (beta n) (hbeta n) (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (left, Function.update right e g)) :
    m * ((Real.exp (-32 * beta n) *
        ((beta n) ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance)) /
        (4 * Real.exp (16 * beta n))) ≤
      p4Q2GO_originalPhysicalReceiverWeightedHellingerMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        left right e := by
  exact p4Q2GP_originalPhysicalReceiverWeightedHellinger_ge_universal
    Hn (beta n) (hbeta n) _ left right e m hm hFloor

/-- Actual adjacent-scale fine-left three-mode physical input, with its
fine beta(n+1) source construction retained and frozen beta(n) Wilson law. -/
theorem p4Q2GP_actualFineLeftThreeModeReceiverWeightedHellinger_ge_universal
    (a : Fin 3 → ℝ) (left right : Cfg) (e : Link)
    (m : ℝ) (hm : 0 ≤ m)
    (hFloor : ∀ g : Gauge, m ≤
      normalizedPhysicalOneSlabJointReceiverProductBCF Hn 2 (by norm_num)
        (beta n) (hbeta n) (∑ k : Fin 3, a k • LeftFactor n r k)
        (left, Function.update right e g)) :
    m * ((Real.exp (-32 * beta n) *
        ((beta n) ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance)) /
        (4 * Real.exp (16 * beta n))) ≤
      p4Q2GO_originalPhysicalReceiverWeightedHellingerMass
        Hn (beta n) (hbeta n)
        (∑ k : Fin 3, a k • LeftFactor n r k)
        left right e := by
  exact p4Q2GP_originalPhysicalReceiverWeightedHellinger_ge_universal
    Hn (beta n) (hbeta n) _ left right e m hm hFloor

end ActualAdjacent
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GP_originalWilsonHellinger_ge_universalSU2Variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GP_originalPhysicalReceiverWeightedHellinger_ge_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GP_originalPhysicalReceiverWeightedHellinger_ge_universal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GP_actualFineRightKrylovReceiverWeightedHellinger_ge_universal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GP_actualFineLeftThreeModeReceiverWeightedHellinger_ge_universal
