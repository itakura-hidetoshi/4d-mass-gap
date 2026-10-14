import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativePosteriorReceiverV5_GR
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorHalfDensityMinorFloorV5_FV
import Mathlib.Tactic

/-!
# P4-Q2-GS: actual SU(2) two-boundary signed physical receiver witness

GR gives the exact ORIGINAL signed physical-source link response R_f under
an actual interacting Wilson left-boundary posterior, using the same
physical transfer t_f and the genuine posterior square-root ratio.

Here subtract its two genuine left rows at arbitrary actual right SU(2)
link insertions g,h: the common t_f(B_h) cancels POINTWISE and the
difference is
  L*t_f(B_g)*[sqrt(p_pi(h))/sqrt(p_pi(g))
               - sqrt(p_id(h))/sqrt(p_id(g))].

For h=identity and g=real SU(2) pi rotation, FV's strictly positive
original posterior square-root 2x2 minor proves the ratio bracket is
strictly NEGATIVE whenever frozen beta>0. Consequently any ORIGINAL
physical source with an explicitly positive actual Wilson transfer
t_f(B_g)>0 has a strictly nonzero TWO-LEFT-BOUNDARY signed response
difference at this explicit insertion and right environment.

Unlike abstract test vectors, the input remains the real physical
gauge-invariant Hilbert source. The final statements specialize the
same witness to the actual fine right Krylov and original left
three-mode sources, retaining fine beta(n+1) IN those source factors
and the frozen beta(n) in posterior and receiver.

This is a pointwise signed receiver witness, NOT yet positivity of the
GI integrated two-Wilson-posterior expectation gap Delta, nor source
injectivity for arbitrary signed Krylov coefficients, nor a uniform
source frame, C1/C2/C3/H2/H3/H4 or a continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1900000
set_option synthInstance.maxHeartbeats 760000

local instance p4Q2GS_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GS_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GS_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GS_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GS_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section Frozen

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "posterior" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
    H 2 (by norm_num) beta hbeta
local notation "L" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta‖⁻¹

/-- For ANY two genuine SU(2) right insertion values g,h, the signed
FF physical receiver's difference across the two ACTUAL Wilson LEFT
boundaries has a common original transfer source factor. -/
theorem p4Q2GS_originalTwoBoundarySignedResponse_eq_transfer_mul_posteriorRootContrast
    (f : Phys) (right : Cfg) (e : Link) (g h : Gauge) :
    p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        H 2 (by norm_num) beta hbeta f e
        ((originalWilsonExplicitIdentityBoundary H, Function.update right e h),g) -
      p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        H 2 (by norm_num) beta hbeta f e
        ((p4Q2FQ_originalSU2LeftPiRotationAtLink H e,
          Function.update right e h),g) =
      L * decomposableOneSliceTransferIntegral H 2 beta f
        (Function.update right e g) *
        (Real.sqrt
            (posterior (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e h) /
          Real.sqrt
            (posterior (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g) -
         Real.sqrt
            (posterior (originalWilsonExplicitIdentityBoundary H) right e h) /
          Real.sqrt
            (posterior (originalWilsonExplicitIdentityBoundary H) right e g)) := by
  rw [p4Q2GR_originalSignedResponse_at_inserted_right,
    p4Q2GR_originalSignedResponse_at_inserted_right]
  ring

/-- FV's strict authentic Wilson two-boundary positive square-root
minor becomes a strict inequality of the ORIGINAL conditional
posterior density ratios at the two ACTUAL SU(2) target insertions. -/
theorem p4Q2GS_originalTwoWilsonBoundary_posteriorSqrtRatio_strict
    (hpos : 0 < beta) (right : Cfg) (e : Link) :
    Real.sqrt
        (posterior (p4Q2FQ_originalSU2LeftPiRotationAtLink H e)
          right e (1 : Gauge)) /
      Real.sqrt
        (posterior (p4Q2FQ_originalSU2LeftPiRotationAtLink H e)
          right e (specialUnitaryTwoRotation Real.pi)) <
    Real.sqrt
        (posterior (originalWilsonExplicitIdentityBoundary H)
          right e (1 : Gauge)) /
      Real.sqrt
        (posterior (originalWilsonExplicitIdentityBoundary H)
          right e (specialUnitaryTwoRotation Real.pi)) := by
  let a := p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
    H beta hbeta right e false false
  let b := p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
    H beta hbeta right e false true
  let c := p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
    H beta hbeta right e true false
  let d := p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
    H beta hbeta right e true true
  have hBound (row col : Bool) :
      Real.exp (-16 * beta) ≤
        p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
          H beta hbeta right e row col := by
    unfold p4Q2FU_originalSU2WilsonPosteriorFourCornerEntry
    exact (p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
      H 2 (by norm_num) beta hbeta
      (if row then p4Q2FQ_originalSU2LeftPiRotationAtLink H e
        else originalWilsonExplicitIdentityBoundary H)
      right e
      (if col then specialUnitaryTwoRotation Real.pi
        else (1 : Gauge))).1
  have ha : 0 < a := (Real.exp_pos _).trans_le (hBound false false)
  have hb : 0 < b := (Real.exp_pos _).trans_le (hBound false true)
  have hc : 0 < c := (Real.exp_pos _).trans_le (hBound true false)
  have hd : 0 < d := (Real.exp_pos _).trans_le (hBound true true)
  have hMinor : 0 < Real.sqrt (a * d) - Real.sqrt (b * c) := by
    simpa only [a, b, c, d,
      p4Q2FV_originalSU2WilsonPosteriorHalfDensityMinor] using
      (p4Q2FV_originalSU2WilsonPosteriorHalfDensityMinor_pos
        H beta hpos right e)
  have hAD : Real.sqrt (a * d) = Real.sqrt a * Real.sqrt d :=
    Real.sqrt_mul ha.le d
  have hBC : Real.sqrt (b * c) = Real.sqrt b * Real.sqrt c :=
    Real.sqrt_mul hb.le c
  rw [hAD, hBC] at hMinor
  have hMul :
      Real.sqrt c * Real.sqrt b < Real.sqrt a * Real.sqrt d := by
    nlinarith [hMinor]
  have hRatio :
      Real.sqrt c / Real.sqrt d < Real.sqrt a / Real.sqrt b :=
    (div_lt_div_iff₀ (Real.sqrt_pos.mpr hd)
      (Real.sqrt_pos.mpr hb)).2 hMul
  exact hRatio

/-- ACTUAL positive Wilson transfer response at a concrete right-link
SU(2) pi insertion forces STRICT NONZERO signed physical receiver
contrast between the two true left Wilson boundaries. No density
independence or synthetic frame is used. -/
theorem p4Q2GS_originalPhysicalSource_twoBoundaryResponse_strict_neg
    (hpos : 0 < beta) (f : Phys) (right : Cfg) (e : Link)
    (hTransfer : 0 <
      decomposableOneSliceTransferIntegral H 2 beta f
        (Function.update right e (specialUnitaryTwoRotation Real.pi))) :
    p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        H 2 (by norm_num) beta hbeta f e
        ((originalWilsonExplicitIdentityBoundary H,
          Function.update right e (1 : Gauge)), specialUnitaryTwoRotation Real.pi) -
      p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        H 2 (by norm_num) beta hbeta f e
        ((p4Q2FQ_originalSU2LeftPiRotationAtLink H e,
          Function.update right e (1 : Gauge)), specialUnitaryTwoRotation Real.pi) < 0 := by
  have hL : 0 < L :=
    inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H 2 (by norm_num) beta hbeta)
  have hRatio := p4Q2GS_originalTwoWilsonBoundary_posteriorSqrtRatio_strict
    H beta hbeta hpos right e
  rw [p4Q2GS_originalTwoBoundarySignedResponse_eq_transfer_mul_posteriorRootContrast]
  exact mul_neg_of_pos_of_neg (mul_pos hL hTransfer) (sub_neg.mpr hRatio)

end Frozen

section ActualAdjacent

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "RightFactor" => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" => physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- The SAME positive-transfer signed receiver contrast applies to
the ACTUAL fine-beta(n+1) Krylov right source family, with the original
FROZEN beta(n) Wilson posterior. Positivity of a signed source's
true transfer is an explicit remaining physical input, not a frame axiom. -/
theorem p4Q2GS_actualFineRightKrylov_twoBoundaryResponse_strict_neg
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ) (right : Cfg) (e : Link)
    (hTransfer : 0 <
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Function.update right e (specialUnitaryTwoRotation Real.pi))) :
    p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        Hn 2 (by norm_num) (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e
        ((originalWilsonExplicitIdentityBoundary Hn,
          Function.update right e (1 : Gauge)), specialUnitaryTwoRotation Real.pi) -
      p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        Hn 2 (by norm_num) (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e
        ((p4Q2FQ_originalSU2LeftPiRotationAtLink Hn e,
          Function.update right e (1 : Gauge)), specialUnitaryTwoRotation Real.pi) < 0 := by
  have hTransfer' : 0 <
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (↑(∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)))
        (Function.update right e (specialUnitaryTwoRotation Real.pi)) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using hTransfer
  exact p4Q2GS_originalPhysicalSource_twoBoundaryResponse_strict_neg
    Hn (beta n) (hbeta n) hFrozen _ right e hTransfer'

/-- The true fine left-three-mode physical source family inherits the
same original Wilson source-dependent strict response witness at
frozen beta(n); no abstract three-vector replacement is introduced. -/
theorem p4Q2GS_actualFineLeftThreeMode_twoBoundaryResponse_strict_neg
    (hFrozen : 0 < beta n) (a : Fin 3 → ℝ) (right : Cfg) (e : Link)
    (hTransfer : 0 <
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (∑ k : Fin 3, a k • LeftFactor n r k)
        (Function.update right e (specialUnitaryTwoRotation Real.pi))) :
    p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        Hn 2 (by norm_num) (beta n) (hbeta n)
        (∑ k : Fin 3, a k • LeftFactor n r k) e
        ((originalWilsonExplicitIdentityBoundary Hn,
          Function.update right e (1 : Gauge)), specialUnitaryTwoRotation Real.pi) -
      p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        Hn 2 (by norm_num) (beta n) (hbeta n)
        (∑ k : Fin 3, a k • LeftFactor n r k) e
        ((p4Q2FQ_originalSU2LeftPiRotationAtLink Hn e,
          Function.update right e (1 : Gauge)), specialUnitaryTwoRotation Real.pi) < 0 := by
  exact p4Q2GS_originalPhysicalSource_twoBoundaryResponse_strict_neg
    Hn (beta n) (hbeta n) hFrozen _ right e hTransfer

end ActualAdjacent
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GS_originalTwoBoundarySignedResponse_eq_transfer_mul_posteriorRootContrast
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GS_originalTwoWilsonBoundary_posteriorSqrtRatio_strict
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GS_originalPhysicalSource_twoBoundaryResponse_strict_neg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GS_actualFineRightKrylov_twoBoundaryResponse_strict_neg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GS_actualFineLeftThreeMode_twoBoundaryResponse_strict_neg
