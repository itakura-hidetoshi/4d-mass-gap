import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoBoundarySignedResponseHaarPositiveV5_GT
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarAnyFineZeroModePositive
import Mathlib.Tactic

/-!
# P4-Q2-GV — unconditional original Wilson source witness at true Krylov depth zero

GS and GT proved the TRUE Wilson two-boundary signed physical receiver
difference has positive compact SU(2) Haar squared mass whenever the
ORIGINAL transfer-smoothing integral of the SAME physical source is
strictly positive at the SU(2) pi insertion. That positivity should be
PROVED from the original Wilson kernel, not imposed as a frame axiom.

For the actual physical Haar-L² CONSTANT UNIT, its canonical Lp
representative equals 1 Haar-a.e., while the original finite-volume
Wilson one-slab kernel K_beta(A,B) is strictly positive and continuous.
Thus the true transfer integral
  t_1(B) = integral_A K_beta(A,B) dHaar(A) > 0
at EVERY physical right background, for beta>=0.

The TRUE adjacent fine right Krylov source at depth zero is exactly
this original physical constant unit for ANY nonnegative fine coupling
beta(n+1). At positive FROZEN beta(n), the original pair of identity/pi
left boundary physical receivers therefore has a strict NEGATIVE
SU(2) pi-insertion response difference and strictly POSITIVE reference-
Haar squared mass, without any source-frame positivity hypothesis.

This is a concrete nonzero genuine physical Krylov source witness.
It does NOT establish injectivity of GI's two-posterior expectation gap,
an arbitrary signed Krylov coefficient frame, an H/scale uniform
Rayleigh eigenvalue, a continuum Yang-Mills mass gap or H1-C3 closure.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 660000

local instance p4Q2GV_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GV_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GV_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GV_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GV_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- For the ACTUAL constant unit physical source the ORIGINAL,
nonnegative-coupling Wilson one-slab transfer integral is everywhere
STRICTLY POSITIVE. No point-evaluation of an arbitrary L² source is
made: the unit source is first identified Haar-a.e. with the canonical
constant-one representative and only then integrated. -/
theorem p4Q2GV_originalConstantPhysicalTransferIntegral_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    0 < decomposableOneSliceTransferIntegral H 2 beta
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) B := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let K : Cfg → ℝ := fun A =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B
  let f : Lp ℝ 2 μ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
    infer_instance
  let oneL2 : Lp ℝ 2 μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H 2
  have hOneL2 : (fun A : Cfg => oneL2 A) =ᵐ[μ]
      (fun _ => (1 : ℝ)) := by
    change (fun A : Cfg => (Lp.const 2 μ (1 : ℝ)) A) =ᵐ[μ]
      (fun _ => (1 : ℝ))
    exact Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℝ))
  have hF : f = oneL2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_coe_eq_HaarOneL2
      H 2
  have hOne : (fun A : Cfg => f A) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
    rw [hF]
    exact hOneL2
  have hKCont : Continuous K := by
    dsimp [K]
    exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 beta).comp₂ continuous_id continuous_const
  have hKInt : Integrable K μ :=
    hKCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hKPos (A : Cfg) : 0 < K A :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H 2 beta A B
  have hIntegralPos : 0 < ∫ A : Cfg, K A ∂μ := by
    rw [integral_pos_iff_support_of_nonneg
      (fun A : Cfg => (hKPos A).le) hKInt]
    have hSupport : Function.support K = Set.univ := by
      ext A
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (hKPos A).ne'
    rw [hSupport]
    simp
  change 0 < ∫ A : Cfg, K A * f A ∂μ
  calc
    0 < ∫ A : Cfg, K A ∂μ := hIntegralPos
    _ = ∫ A : Cfg, K A * f A ∂μ := by
      apply integral_congr_ae
      filter_upwards [hOne] with A hA
      simp [hA]

section ActualAdjacent

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- The ACTUAL fine-right Krylov zero-depth mode is the true physical
constant unit, independent of the genuine fine beta(n+1). Its original
FROZEN Wilson transfer is therefore strictly positive everywhere. -/
theorem p4Q2GV_actualFineRightZeroDepthTransferIntegral_pos
    (B : Cfg) :
    0 < decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (RightFactor n 0) B := by
  rw [fineRightFactor_zeroDepth_eq_constantUnit_anyFineBeta
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n]
  exact p4Q2GV_originalConstantPhysicalTransferIntegral_pos
    Hn (beta n) (hbeta n) B

/-- A concrete physically existing Krylov mode, unlike a postulated
signed source-frame, forces the ACTUAL two Wilson LEFT boundary
signed receiver difference to be strictly negative at the true
SU(2) pi right insertion. -/
theorem p4Q2GV_actualFineRightZeroDepth_twoBoundarySignedResponse_neg
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        Hn 2 (by norm_num) (beta n) (hbeta n)
        (RightFactor n 0) e
        ((originalWilsonExplicitIdentityBoundary Hn,
          Function.update right e (1 : Gauge)), specialUnitaryTwoRotation Real.pi) -
      p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        Hn 2 (by norm_num) (beta n) (hbeta n)
        (RightFactor n 0) e
        ((p4Q2FQ_originalSU2LeftPiRotationAtLink Hn e,
          Function.update right e (1 : Gauge)), specialUnitaryTwoRotation Real.pi) < 0 := by
  exact p4Q2GS_originalPhysicalSource_twoBoundaryResponse_strict_neg
    Hn (beta n) (hbeta n) hFrozen (RightFactor n 0) right e
      (p4Q2GV_actualFineRightZeroDepthTransferIntegral_pos
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (Function.update right e (specialUnitaryTwoRotation Real.pi)))

/-- The exact original zero-depth fine-right physical Krylov source has
strictly positive two-boundary signed response SQUARED HAAR mass at
EVERY actual finite Wilson link for beta(n)>0, without any source
positivity/frame premise. Haar is a reference norm, not a replacement
conditional Wilson posterior. -/
theorem p4Q2GV_actualFineRightZeroDepth_HaarMass_pos
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    0 < p4Q2GT_originalTwoBoundaryPhysicalSignedResponseHaarMass
      Hn (beta n) (hbeta n) (RightFactor n 0) right e := by
  exact p4Q2GT_originalPhysicalSignedTwoBoundaryHaarMass_pos_of_transfer
    Hn (beta n) (hbeta n) hFrozen (RightFactor n 0) right e
      (p4Q2GV_actualFineRightZeroDepthTransferIntegral_pos
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (Function.update right e (specialUnitaryTwoRotation Real.pi)))

end ActualAdjacent
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GV_originalConstantPhysicalTransferIntegral_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GV_actualFineRightZeroDepthTransferIntegral_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GV_actualFineRightZeroDepth_twoBoundarySignedResponse_neg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GV_actualFineRightZeroDepth_HaarMass_pos
