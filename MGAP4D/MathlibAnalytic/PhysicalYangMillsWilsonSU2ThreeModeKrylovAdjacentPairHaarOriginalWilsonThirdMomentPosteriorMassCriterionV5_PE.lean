import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonThirdMomentPhysicalSchurV5_PD
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonAllFineUnconditionalGLMassV5_OX
import Mathlib.Tactic

/-!
# P4-Q2-PE — original Wilson third physical moment ↔ genuine posterior criterion

Connect the true PD moment-orthogonal physical Schur innovation to the
ACTUAL all-depth HJ physical right-Krylov synthesis, the UNMODIFIED
two-interacting-Wilson-posterior GL mass and the original signed GI
receiver. The positive-frozen Wilson response is not replaced by
independent Haar. The frozen and fine couplings are kept distinct.

At all finite H, frozen b>0 and fine t>=0, the canonical depth-two
moment coefficient a=( -A, -B, D2 ) synthesizes *exactly* the real
Gauss-law Schur innovation R2=D2*T_t²U-A*U-B*T_tU.
The TRUE original posterior GL mass vanishes iff
  D2(t)*D3(t)=0.
On the independently proven original small-positive-fine D2>0
interval this becomes the exact original-model alternatives:
  GLmass(R2)>0 ↔ D3>0 ↔ ∃ genuine signed two-posterior GI context
  detecting the identical R2.

These are precise analytical *equivalences*, not a proof that D3>0.
They replace the abstract spectral-support test with a concrete
two-posterior integral/receiver target on the SAME Wilson physical
source. No rank-three hypothesis, new axiom, Dobrushin, surrogate
posterior, sorry or admit. U0/endpoint/continuum gap remain OPEN.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Matrix
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PE_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PE_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PE_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PE_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PE_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section ActualOriginalWilsonPosteriorMomentCriterion

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Full" => p4Q2HJ_actualRightGIContinuousDetector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "M" => p4Q2HF_actualRightGIModalLinear
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive
    (beta (n + 1)) (hbeta (n + 1))
local notation "m" =>
  p4Q2PB_originalWilsonPhysicalMoment Hn (beta (n + 1)) (hbeta (n + 1))
local notation "D2" =>
  p4Q2PD_originalWilsonTwoMomentDet Hn
    (beta (n + 1)) (hbeta (n + 1))
local notation "D3" =>
  p4Q2PD_originalWilsonThirdMomentGap Hn
    (beta (n + 1)) (hbeta (n + 1))
local notation "R" =>
  p4Q2PD_originalWilsonThirdSchurPhysical Hn
    (beta (n + 1)) (hbeta (n + 1))
local notation "Mass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- REAL coefficients on the existing original HJ depth-two source.
Use the literal OO selectors; the second coefficient is D2.
No degree-three independence/rank is postulated. -/
noncomputable def p4Q2PE_actualThirdMomentCoefficient :
    Fin (2 + 1) → ℝ :=
  D2 • p4Q2OO_depthTwoSecondCoefficient -
    ((m 2) ^ 2 - m 1 * m 3) • p4Q2GX_rightZeroCoefficient 2 -
    (m 0 * m 3 - m 1 * m 2) • p4Q2OO_depthTwoFirstCoefficient

/-- Exact equality, in the SAME original Gauss-law physical Hilbert
carrier, of the original HJ synthesized coefficient and the PD
orthogonal Hankel-Schur moment innovation. -/
theorem p4Q2PE_actualThirdMomentSource_eq_physicalSchur :
    S 2 (p4Q2PE_actualThirdMomentCoefficient
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n) = R := by
  obtain ⟨h0, h1, h2⟩ :=
    p4Q2OO_actualDepthTwo_selectorPhysicalSources
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  unfold p4Q2PE_actualThirdMomentCoefficient
  simp only [map_sub, map_smul]
  rw [h0, h1, h2]
  rfl

/-- The original two-posterior GL mass of the genuinely synthesized
third physical moment source has EXACT zero locus D2*D3=0, for
ALL nonnegative fine t (frozen b>0), without rank-three assumptions. -/
theorem p4Q2PE_actualAllFine_thirdMoment_postMass_zero_iff_detProduct_zero
    (hFrozen : 0 < beta n) (e : Link) (left₀ : Cfg) :
    Mass (S 2 (p4Q2PE_actualThirdMomentCoefficient
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n))
      (Finset.univ : Finset Link) = 0 ↔ D2 * D3 = 0 := by
  let a : Fin (2 + 1) → ℝ :=
    p4Q2PE_actualThirdMomentCoefficient
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  have hMass :=
    p4Q2OX_originalPositiveFrozen_allFine_allDepth_massZero_iff_physicalZero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀ 2 a
  have hSource : S 2 a = R :=
    p4Q2PE_actualThirdMomentSource_eq_physicalSchur
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  rw [hSource] at hMass
  change Mass (S 2 a) (Finset.univ : Finset Link) = 0 ↔ D2 * D3 = 0
  rw [hSource]
  have hNorm : ‖R‖ ^ 2 = D2 * D3 :=
    p4Q2PD_originalWilsonThirdSchur_normSq_eq_twoDet_mul_threeGap
      Hn (beta (n + 1)) (hbeta (n + 1))
  constructor
  · intro hzero
    have hR : R = 0 := hMass.mp hzero
    have hn : ‖R‖ ^ 2 = 0 := by rw [hR, norm_zero]; norm_num
    exact hNorm.symm.trans hn
  · intro hProd
    apply hMass.mpr
    have hn : ‖R‖ ^ 2 = 0 := hNorm.trans hProd
    have hn0 : ‖R‖ = 0 := by nlinarith [norm_nonneg R]
    exact norm_eq_zero.mp hn0

/-- Strict original posterior GL mass positivity is equivalent to
TRUE third scalar Hankel positivity when the genuine physical
two-mode pivot D2>0. The mass is NOT a surrogate Gaussian statistic. -/
theorem p4Q2PE_actualThirdMoment_postMass_pos_iff_thirdGap_pos
    (hFrozen : 0 < beta n) (e : Link) (left₀ : Cfg)
    (hTwo : 0 < D2) :
    (0 < Mass (S 2 (p4Q2PE_actualThirdMomentCoefficient
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n))
        (Finset.univ : Finset Link)) ↔ 0 < D3 := by
  let a : Fin (2 + 1) → ℝ :=
    p4Q2PE_actualThirdMomentCoefficient
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  have hSource : S 2 a = R :=
    p4Q2PE_actualThirdMomentSource_eq_physicalSchur
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  have hCriterion :=
    p4Q2PD_originalWilsonThirdMomentGap_pos_iff_physicalSchur_nonzero
      Hn (beta (n + 1)) (hbeta (n + 1)) hTwo
  have hMassZero :=
    p4Q2OX_originalPositiveFrozen_allFine_allDepth_massZero_iff_physicalZero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀ 2 a
  constructor
  · intro hpos
    have hSourceNe : S 2 a ≠ 0 := by
      intro hz
      have hmzero := hMassZero.mpr hz
      exact (ne_of_gt hpos) hmzero
    rw [hSource] at hSourceNe
    exact hCriterion.mpr hSourceNe
  · intro hGap
    have hr : R ≠ 0 := hCriterion.mp hGap
    have hNonzero : S 2 a ≠ 0 := by rw [hSource]; exact hr
    exact p4Q2OX_originalPositiveFrozen_allFine_allDepth_nonzero_mass_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀ 2 a hNonzero

/-- The missing THIRD rank is *equivalent* to finding an actual
original two-interacting-Wilson-posterior signed GI response of the
canonical HJ moment-Schur source. The link e may be fixed BEFORE
choosing the genuine boundary context z, via OT/OW regularity. -/
theorem p4Q2PE_actualThirdMoment_trueSignedGI_exists_iff_thirdGap_pos
    (hFrozen : 0 < beta n) (e : Link) (left₀ : Cfg)
    (hTwo : 0 < D2) :
    (∃ z : Pair,
       M 2 e z (p4Q2PE_actualThirdMomentCoefficient
         (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n) ≠ 0) ↔
      0 < D3 := by
  let a : Fin (2 + 1) → ℝ :=
    p4Q2PE_actualThirdMomentCoefficient
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  have hSource : S 2 a = R :=
    p4Q2PE_actualThirdMomentSource_eq_physicalSchur
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  have hCriterion :=
    p4Q2PD_originalWilsonThirdMomentGap_pos_iff_physicalSchur_nonzero
      Hn (beta (n + 1)) (hbeta (n + 1)) hTwo
  constructor
  · rintro ⟨z, hModal⟩
    have hSourceNe : S 2 a ≠ 0 := by
      intro hS
      have hKer : a ∈ (S 2).ker := (LinearMap.mem_ker).mpr hS
      have hFullKer : a ∈ (Full 2).ker :=
        (p4Q2HJ_actualRightSourceKernel_le_GIContinuousDetectorKernel
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n 2) hKer
      have hFull : Full 2 a = 0 := (LinearMap.mem_ker).mp hFullKer
      have hAt := congrArg (fun g : Link → C(Pair, ℝ) => g e z) hFull
      have hModalZero : M 2 e z a = 0 := by
        simpa only [p4Q2HJ_actualRightGIContinuousDetector_apply,
          Pi.zero_apply, ContinuousMap.zero_apply] using hAt
      exact hModal hModalZero
    rw [hSource] at hSourceNe
    exact hCriterion.mpr hSourceNe
  · intro hGap
    have hr : R ≠ 0 := hCriterion.mp hGap
    have hS : S 2 a ≠ 0 := by rw [hSource]; exact hr
    obtain ⟨z, hGI⟩ :=
      p4Q2OT_originalContinuousPhysical_nonzero_genuineGI
        Hn (beta n) hFrozen (S 2 a) hS
        (p4Q2OW_actualAllDepth_source_hasGaugeContinuousRepresentative
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n 2 a) e left₀
    have hHF :=
      p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 2 a e z
    change p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n) (S 2 a) e z = M 2 e z a at hHF
    exact ⟨z, hHF ▸ hGI⟩

/-- The same original small-positive fine interval in PC supplies
the exact positive D2 condition needed by the genuine third-moment
posterior criterion; no restriction to an assumed rank-three branch. -/
theorem p4Q2PE_actualSmallFine_trueMomentPivot_pos
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta → 0 < D2) := by
  obtain ⟨delta, hdelta, hStrict⟩ :=
    p4Q2PC_actualSmallFine_allShifts_strictWilsonMomentLogConvex
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall
  have h := hStrict ht hsmall 0
  simpa only [zero_add, p4Q2PD_originalWilsonTwoMomentDet] using h

/-- Practical original-Wilson analytic target in one common small
positive-fine interval: actual positive GL mass and a genuine
signed two-posterior context are each equivalent to the SAME
unproved D3>0 moment innovation. This closes the formulation /
authority-transport gate, NOT the rank-three analytic gate. -/
theorem p4Q2PE_actualSmallFine_posteriorMass_and_receiver_iff_thirdGap
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        ((0 < Mass (S 2 (p4Q2PE_actualThirdMomentCoefficient
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n))
          (Finset.univ : Finset Link) ↔ 0 < D3) ∧
         ((∃ z : Pair,
           M 2 e z (p4Q2PE_actualThirdMomentCoefficient
             (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n) ≠ 0)
           ↔ 0 < D3))) := by
  obtain ⟨delta, hdelta, hTwo⟩ :=
    p4Q2PE_actualSmallFine_trueMomentPivot_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall
  exact ⟨
    p4Q2PE_actualThirdMoment_postMass_pos_iff_thirdGap_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀ (hTwo ht hsmall),
    p4Q2PE_actualThirdMoment_trueSignedGI_exists_iff_thirdGap_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀ (hTwo ht hsmall)⟩

end ActualOriginalWilsonPosteriorMomentCriterion

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PE_actualThirdMomentSource_eq_physicalSchur
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PE_actualAllFine_thirdMoment_postMass_zero_iff_detProduct_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PE_actualThirdMoment_postMass_pos_iff_thirdGap_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PE_actualThirdMoment_trueSignedGI_exists_iff_thirdGap_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PE_actualSmallFine_trueMomentPivot_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PE_actualSmallFine_posteriorMass_and_receiver_iff_thirdGap
