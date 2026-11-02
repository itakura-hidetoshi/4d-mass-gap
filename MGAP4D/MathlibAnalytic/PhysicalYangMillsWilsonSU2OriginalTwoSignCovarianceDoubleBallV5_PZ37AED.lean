import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalExplicitSpherePolynomialFloorV5_PZ37AEC
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AED — two-sign genuine physical Wilson covariance, doubled Haar floor

ACI proves that the ORIGINAL centered Gauss-law physical FF covariance is
nonzero at a genuine boundary pair for every finite H and physical link e.
ACD proves continuity, and the original pair-space is compact. Thus the
MAXIMUM of the actual absolute covariance is attained and strictly positive.
The original ACC center-gauge action changes its sign without changing
the physical source, FF receiver, either interacting posterior, or Haar law.

ADM's genuine full-chordal uniform continuity gives the SAME radius R>0
around opposite-sign centers a and Gamma_e(a), on which the original
covariance remains respectively >= C(a)/2 and <= -C(a)/2.
These two actual D_H balls are DISJOINT. AEC's genuine original pair-Haar
radius polynomial applies to EACH of them; finite original pair-Haar
additivity on their union provides TWICE the previous lower certificate.
The original ADE covariance-square moment over this union consequently
obeys:
  0 < (C(a)/2)^2 * (2 * P_H(R)) <= S(H,b0,e),
  P_H(R) = (min(R/(2*card(Link_H)+1),2)/4)^(8*card(Link_H)),
where a is a global positive covariance maximizer.

A checkable half-radius continuity certificate supplies the exact
rational factor 2*(1/(8*(2*card(Link_H)+1)))^(8*card(Link_H)).
It is NOT asserted that this certificate already holds numerically.

The original centered-source witness and compact uniform modulus are
nonconstructive; their covariance amplitude and stable R have NOT
been numerically evaluated. No claimed H-uniform coercivity, GI 68
threshold, physical gap, or continuum four-dimensional mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

-- The TRUE original SU(2) compact and Borel structures are explicit.
-- The pair-space compactness/measurability should not be expected to
-- synthesize from a local Fintype Link instance alone.
local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AED_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AED_compactG : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AED_countableG : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AED_measurableG : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AED_borelG : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "Ball" => p4Q2PZ37ADL_originalFullBoundaryChordalBall H
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "Gamma" => p4Q2PZ37ACC_originalCenterGaugePair H
local notation "b₀" => p4Q2PZ37ADC_fixedCoupling
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H

local instance p4Q2PZ37AED_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AED_pairCompact : CompactSpace Pair := by
  infer_instance
local instance p4Q2PZ37AED_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The original physical covariance has a STRICTLY POSITIVE attained
global absolute maximum on the actual compact boundary-pair space.
No new nonzero source, continuity premise or surrogate receiver. -/
theorem p4Q2PZ37AED_originalMaximumAbsoluteCovariance_exists
    (e : Link) :
    ∃ a : Pair,
      0 < |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| ∧
      ∀ z : Pair,
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| ≤
          |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| := by
  obtain ⟨a₀, ha₀⟩ :=
    p4Q2PZ37ACI_centeredEnergyCovariance_nonzero
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos e
        (originalWilsonExplicitIdentityBoundary H)
  have hC : Continuous (fun z : Pair =>
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z) :=
    p4Q2PZ37ACD_originalReceiver_covariance_continuous
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e
  obtain ⟨a, _ha, hMax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set Pair)).exists_isMaxOn
      ⟨a₀, Set.mem_univ a₀⟩ hC.abs.continuousOn
  exact ⟨a, (abs_pos.mpr ha₀).trans_le (hMax (Set.mem_univ a₀)),
    fun z => hMax (Set.mem_univ z)⟩

/-- The genuine original center-gauge action makes a positive covariance
GLOBAL maximizer available, with a negative partner of EQUAL amplitude. -/
theorem p4Q2PZ37AED_originalPositiveMaximumCovariance_exists
    (e : Link) :
    ∃ a : Pair,
      0 < C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a ∧
      (∀ z : Pair,
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| ≤
          C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a) := by
  obtain ⟨a, hAbs, hMax⟩ :=
    p4Q2PZ37AED_originalMaximumAbsoluteCovariance_exists H e
  have hFlip :
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e (Gamma e a) =
        -C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a :=
    p4Q2PZ37ACC_centeredReceiver_covariance_centerGauge
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a
  have hNe :
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a ≠ 0 :=
    (abs_pos.mp hAbs)
  rcases lt_or_gt_of_ne hNe with hn | hp
  · refine ⟨Gamma e a, ?_, ?_⟩
    · rw [hFlip]
      linarith
    · intro z
      rw [hFlip]
      simpa only [abs_of_neg hn] using hMax z
  · refine ⟨a, hp, ?_⟩
    intro z
    simpa only [abs_of_pos hp] using hMax z

/-- One and the SAME authentic full-D_H stability radius keeps the
original covariance above +C(a)/2 and below -C(a)/2 in the genuine
opposite center-gauge balls. This is uniform continuity, not a
hypothetical Lipschitz coefficient. -/
theorem p4Q2PZ37AED_originalTwoSignBalls_stable
    (e : Link) (a : Pair)
    (ha : 0 < C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a) :
    ∃ R : ℝ, 0 < R ∧
      (∀ z ∈ Ball a R,
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2 ≤
          C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z) ∧
      (∀ z ∈ Ball (Gamma e a) R,
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z ≤
          -(C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2)) := by
  let v : ℝ := C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a
  have hv : 0 < v := ha
  obtain ⟨R, hR, hMod⟩ :=
    p4Q2PZ37ADM_originalCenteredCovariance_uniformChordalModulus
      H e (v / 2) (half_pos hv)
  have hFlip :
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e (Gamma e a) = -v := by
    simpa only [v] using
      (p4Q2PZ37ACC_centeredReceiver_covariance_centerGauge
        H b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a)
  refine ⟨R, hR, ?_, ?_⟩
  · intro z hz
    have h := (abs_lt.mp (hMod a z hz)).2
    change v - C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z < v / 2 at h
    change v / 2 ≤ C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z
    linarith
  · intro z hz
    have h := (abs_lt.mp (hMod (Gamma e a) z hz)).1
    rw [hFlip] at h
    dsimp [v] at h ⊢
    linarith

/-- The two actual original gauge-conjugate balls are disjoint
whenever their genuine covariance bands have opposite strict signs. -/
theorem p4Q2PZ37AED_originalTwoSignBalls_disjoint
    (e : Link) (a : Pair) (R : ℝ)
    (ha : 0 < C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a)
    (hPos : ∀ z ∈ Ball a R,
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2 ≤
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z)
    (hNeg : ∀ z ∈ Ball (Gamma e a) R,
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z ≤
        -(C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2)) :
    Disjoint (Ball a R) (Ball (Gamma e a) R) := by
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  have hp := hPos z hz₁
  have hn := hNeg z hz₂
  linarith

/-- AEC's exact original pair-Haar polynomial floor applies to BOTH
disjoint true full-chordal gauge-conjugate balls. The full union
therefore has TWICE the proven genuine physical Haar mass floor. -/
theorem p4Q2PZ37AED_originalTwoSignBallUnion_mass_ge_doublePolynomial
    (e : Link) (a : Pair) (R : ℝ) (hR : 0 < R)
    (ha : 0 < C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a)
    (hPos : ∀ z ∈ Ball a R,
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2 ≤
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z)
    (hNeg : ∀ z ∈ Ball (Gamma e a) R,
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z ≤
        -(C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2)) :
    2 * (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
        (8 * Fintype.card Link) ≤
      Measure.real outer (Ball a R ∪ Ball (Gamma e a) R) := by
  have hd :=
    p4Q2PZ37AED_originalTwoSignBalls_disjoint H e a R ha hPos hNeg
  have hUnion : Measure.real outer (Ball a R ∪ Ball (Gamma e a) R) =
      Measure.real outer (Ball a R) +
      Measure.real outer (Ball (Gamma e a) R) :=
    measureReal_union hd
      (p4Q2PZ37ADL_originalFullChordalBall_isOpen
        H (Gamma e a) R).measurableSet
  have hOne :=
    p4Q2PZ37AEC_originalFullBall_mass_ge_minPolynomial H a R hR
  have hTwo :=
    p4Q2PZ37AEC_originalFullBall_mass_ge_minPolynomial H (Gamma e a) R hR
  rw [hUnion]
  linarith only [hOne, hTwo]

/-- The genuine same original covariance is >= its positive
half-amplitude in ABSOLUTE VALUE on the entire disjoint union. -/
theorem p4Q2PZ37AED_originalTwoSignBallUnion_absFloor
    (e : Link) (a : Pair) (R : ℝ)
    (hPos : ∀ z ∈ Ball a R,
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2 ≤
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z)
    (hNeg : ∀ z ∈ Ball (Gamma e a) R,
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z ≤
        -(C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2)) :
    ∀ z ∈ Ball a R ∪ Ball (Gamma e a) R,
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2 ≤
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| := by
  intro z hz
  rcases hz with hz₁ | hz₂
  · exact (hPos z hz₁).trans (le_abs_self _)
  · have h := hNeg z hz₂
    exact (by linarith :
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2 ≤
        -C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z).trans
          (neg_le_abs _)

/-- Unlike a single-ball witness, the same true physical covariance
square is integrated over TWO disjoint sign-definite physical balls.
The AEC explicit polynomial lower bound is DOUBLED, without any new
physical quantitative regularity assumption. -/
theorem p4Q2PZ37AED_originalTwoSignBallUnion_secondMoment_doubleFloor
    (e : Link) (a : Pair) (R : ℝ) (hR : 0 < R)
    (ha : 0 < C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a)
    (hPos : ∀ z ∈ Ball a R,
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2 ≤
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z)
    (hNeg : ∀ z ∈ Ball (Gamma e a) R,
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z ≤
        -(C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2)) :
    (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2) ^ 2 *
      (2 * (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
        (8 * Fintype.card Link)) ≤
      S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  have hMass :=
    p4Q2PZ37AED_originalTwoSignBallUnion_mass_ge_doublePolynomial
      H e a R hR ha hPos hNeg
  have hMoment :=
    p4Q2PZ37ADE_originalOpenCovarianceRegion_lowerMoment
      H e (Ball a R ∪ Ball (Gamma e a) R)
      (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2)
      ((p4Q2PZ37ADL_originalFullChordalBall_isOpen H a R).union
        (p4Q2PZ37ADL_originalFullChordalBall_isOpen H (Gamma e a) R))
      (half_pos ha)
      (p4Q2PZ37AED_originalTwoSignBallUnion_absFloor
        H e a R hPos hNeg)
  exact (mul_le_mul_of_nonneg_left hMass (sq_nonneg _)).trans hMoment

/-- Every actual original spatial link has a positive maximizer and
two gauge-opposed genuine D_H balls, producing an unconditional
existential DOUBLED physical covariance-square moment certificate.
The maximum amplitude and common R are physical but not numerically
evaluated by the pre-existing nonconstructive injectivity/modulus proofs. -/
theorem p4Q2PZ37AED_originalEveryLink_doubledMaxMomentWitness
    (e : Link) :
    ∃ (a : Pair) (R : ℝ),
      0 < C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a ∧
      (∀ z : Pair,
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| ≤
          C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a) ∧
      0 < R ∧
      0 <
        (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2) ^ 2 *
          (2 * (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
            (8 * Fintype.card Link)) ∧
      (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2) ^ 2 *
        (2 * (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
          (8 * Fintype.card Link)) ≤
        S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  obtain ⟨a, ha, hMax⟩ :=
    p4Q2PZ37AED_originalPositiveMaximumCovariance_exists H e
  obtain ⟨R, hR, hPos, hNeg⟩ :=
    p4Q2PZ37AED_originalTwoSignBalls_stable H e a ha
  have hPoly : 0 <
      (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
        (8 * Fintype.card Link) := by
    rw [← p4Q2PZ37AEC_originalFullFloor_eq_minPolynomial H R hR]
    exact p4Q2PZ37AEA_explicitFloor_pos H R hR
  have hPositive : 0 <
      (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2) ^ 2 *
        (2 * (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
          (8 * Fintype.card Link)) :=
    mul_pos (pow_pos (half_pos ha) _) (mul_pos (by norm_num) hPoly)
  exact ⟨a, R, ha, hMax, hR, hPositive,
    p4Q2PZ37AED_originalTwoSignBallUnion_secondMoment_doubleFloor
      H e a R hR ha hPos hNeg⟩

/-- At the literal full-D_H half radius, the AEC min polynomial is
exactly a rational power in the original number of physical links. -/
theorem p4Q2PZ37AED_originalHalfRadius_polynomial_eq_rational :
    (min ((1 / 2 : ℝ) / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
      (8 * Fintype.card Link) =
    (1 / (8 * (2 * (Fintype.card Link : ℝ) + 1))) ^
      (8 * Fintype.card Link) := by
  have hDen : (0 : ℝ) < 2 * (Fintype.card Link : ℝ) + 1 := by positivity
  have hSmall : (1 / 2 : ℝ) /
      (2 * (Fintype.card Link : ℝ) + 1) ≤ 2 := by
    apply (div_le_iff₀ hDen).mpr
    have hCard : (0 : ℝ) ≤ (Fintype.card Link : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hBase :
      ((1 / 2 : ℝ) / (2 * (Fintype.card Link : ℝ) + 1)) / 4 =
        1 / (8 * (2 * (Fintype.card Link : ℝ) + 1)) := by
    field_simp
    ring
  rw [min_eq_left hSmall, hBase]

/-- A fully explicit R=1/2 numerical H-dependent coefficient follows
if the original physical covariance's TRUE uniform modulus is verified
at that fixed radius. This condition is NOT asserted unconditionally. -/
theorem p4Q2PZ37AED_originalHalfBall_certifiedDoubledMoment
    (e : Link) (a : Pair)
    (ha : 0 < C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a)
    (hHalfMod : ∀ z w : Pair, D z w < (1 / 2 : ℝ) →
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z -
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e w| <
          C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2) :
    (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2) ^ 2 *
      (2 * (1 / (8 * (2 * (Fintype.card Link : ℝ) + 1))) ^
        (8 * Fintype.card Link)) ≤
      S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  have hFlip :
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e (Gamma e a) =
        -C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a :=
    p4Q2PZ37ACC_centeredReceiver_covariance_centerGauge
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a
  have hPos : ∀ z ∈ Ball a (1 / 2 : ℝ),
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2 ≤
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z := by
    intro z hz
    have h := (abs_lt.mp (hHalfMod a z hz)).2
    linarith
  have hNeg : ∀ z ∈ Ball (Gamma e a) (1 / 2 : ℝ),
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z ≤
        -(C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a / 2) := by
    intro z hz
    have h := (abs_lt.mp (hHalfMod (Gamma e a) z hz)).1
    rw [hFlip] at h
    linarith
  have h :=
    p4Q2PZ37AED_originalTwoSignBallUnion_secondMoment_doubleFloor
      H e a (1 / 2) (by norm_num) ha hPos hNeg
  rw [p4Q2PZ37AED_originalHalfRadius_polynomial_eq_rational H] at h
  exact h

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AED_originalMaximumAbsoluteCovariance_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AED_originalPositiveMaximumCovariance_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AED_originalTwoSignBalls_stable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AED_originalTwoSignBalls_disjoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AED_originalTwoSignBallUnion_mass_ge_doublePolynomial
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AED_originalTwoSignBallUnion_absFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AED_originalTwoSignBallUnion_secondMoment_doubleFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AED_originalEveryLink_doubledMaxMomentWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AED_originalHalfRadius_polynomial_eq_rational
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AED_originalHalfBall_certifiedDoubledMoment
