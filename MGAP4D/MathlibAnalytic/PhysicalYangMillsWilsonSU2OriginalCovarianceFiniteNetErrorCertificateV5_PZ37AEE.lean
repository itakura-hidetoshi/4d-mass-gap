import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTwoSignCovarianceDoubleBallV5_PZ37AED
import Mathlib.Topology.Compactness.Bases
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEE — genuine finite-net covariance amplitude and variable-error certificates

On the ACTUAL original finite-H boundary-pair space, ADL's separating full
D_H chordal distance has open balls, and ADM proves the SAME physical
centered-source FF covariance C_e is uniformly continuous. Compactness
therefore provides, for every tolerance epsilon>0, a finite net of
genuine boundary-pair configurations that approximates the GLOBAL
physical absolute covariance amplitude to within epsilon.

Every *certified* finite net and *verified* original physical modulus
also yields a finite-table upper bound for all physical covariance
values. The existence of a suitable finite net/modulus does NOT give
a computed net, an evaluated covariance, or a numerical epsilon-radius.

AED's gauge-opposite double-ball argument is further strengthened:
for any actual positive covariance sample a, certified radius R>0
and genuinely verified global covariance oscillation error epsilon
with 0 <= epsilon < C_e(a), the true original pair-Haar moment obeys

 (C_e(a)-epsilon)^2 *
   (2 * (min (R/(2*card(Link_H)+1)) 2 / 4)^(8*card(Link_H)))
     <= S(H,b0,e).

This is a variable-error physical certificate, not an assumed
Lipschitz constant. A fixed half-radius rational specialization and
a CONDITIONAL genuine FC/GI threshold interface are also given.
Original SU(2), the original pair-Haar law, centered Gauss-law source,
Perron/transfer, FF receiver, two interacting posteriors, Lean/mathlib
pins and theorem roots remain unchanged.

No computed physical amplitude, certified numerical radius, H-uniform
coercivity, physical spectral gap or continuum 4D Yang--Mills gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AEE_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEE_compactG : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEE_countableG : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEE_measurableG : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEE_borelG : BorelSpace G :=
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
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H

local instance p4Q2PZ37AEE_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AEE_pairCompact : CompactSpace Pair := by
  infer_instance
local instance p4Q2PZ37AEE_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- A finite net consists of ACTUAL original Wilson boundary pairs,
and covers every such pair in the SAME calibrated full D_H distance. -/
def p4Q2PZ37AEE_isOriginalFullNet (s : Finset Pair) (r : ℝ) : Prop :=
  ∀ z : Pair, ∃ a ∈ s, D a z < r

/-- The original compact physical boundary-pair space admits an actual
finite D_H net for every positive radius. The net cardinality is not
numerically evaluated, nor are the centers fabricated. -/
theorem p4Q2PZ37AEE_originalFullFiniteNet_exists
    (r : ℝ) (hr : 0 < r) :
    ∃ s : Finset Pair, p4Q2PZ37AEE_isOriginalFullNet H s r := by
  have hOpen (a : Pair) : IsOpen (Ball a r) :=
    p4Q2PZ37ADL_originalFullChordalBall_isOpen H a r
  have hCover : (Set.univ : Set Pair) ⊆ ⋃ a : Pair, Ball a r := by
    intro z _hz
    apply Set.mem_iUnion.mpr
    refine ⟨z, ?_⟩
    change D z z < r
    rw [p4Q2PZ37ADL_originalFullDistance_self H z]
    exact hr
  obtain ⟨s, hs⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set Pair)).elim_finite_subcover
      (fun a : Pair => Ball a r) hOpen hCover
  refine ⟨s, ?_⟩
  intro z
  have hz := hs (Set.mem_univ z)
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hz
  obtain ⟨has, haz⟩ := Set.mem_iUnion.mp ha
  exact ⟨a, has, haz⟩

/-- Certified genuine D_H net + a genuine uniform covariance modulus
give a sampled original covariance whose absolute amplitude differs
from any requested true value by LESS than epsilon. -/
theorem p4Q2PZ37AEE_certifiedFiniteNet_covarianceApprox
    (e : Link) (s : Finset Pair) (r ε : ℝ)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hMod : ∀ z w : Pair, D z w < r →
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z -
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e w| < ε) :
    ∀ z : Pair, ∃ a ∈ s,
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| <
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| + ε := by
  intro z
  obtain ⟨a, ha, haz⟩ := hNet z
  refine ⟨a, ha, ?_⟩
  have hOsc := hMod a z haz
  have hTriangle :
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| ≤
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| +
          |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a -
            C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| := by
    calc
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| =
          |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a -
            (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a -
              C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z)| := by
                congr 1
                ring
      _ ≤ |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| +
          |-(C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a -
              C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z)| := by
            simpa only [sub_eq_add_neg] using
              (abs_add_le
                (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a)
                (-(C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a -
                    C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z)))
      _ = _ := by simp
  linarith only [hTriangle, hOsc]

/-- A verified finite TABLE of physical covariance absolute values,
together with a genuine D_H covering and oscillation certificate,
rigorously bounds the SAME physical covariance at every boundary pair.
The finite-table premise is explicit and not evaluated here. -/
theorem p4Q2PZ37AEE_certifiedFiniteTable_globalAmplitudeUpper
    (e : Link) (s : Finset Pair) (r ε M : ℝ)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hMod : ∀ z w : Pair, D z w < r →
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z -
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e w| < ε)
    (hSamples : ∀ a ∈ s,
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| ≤ M) :
    ∀ z : Pair,
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| < M + ε := by
  intro z
  obtain ⟨a, ha, hApprox⟩ :=
    p4Q2PZ37AEE_certifiedFiniteNet_covarianceApprox
      H e s r ε hNet hMod z
  exact hApprox.trans_le (add_le_add_right (hSamples a ha) ε)

/-- Every finite H and actual physical link has an arbitrarily
accurate FINITE sampling interface for the genuine global covariance.
Both the real modulus radius and the finite sample set exist by
compactness but are not claimed to be constructed numerically. -/
theorem p4Q2PZ37AEE_everyLink_finiteAmplitudeApprox_exists
    (e : Link) (ε : ℝ) (hε : 0 < ε) :
    ∃ (r : ℝ), 0 < r ∧
      ∃ (s : Finset Pair),
        p4Q2PZ37AEE_isOriginalFullNet H s r ∧
        ∀ z : Pair, ∃ a ∈ s,
          |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| <
            |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| + ε := by
  obtain ⟨r, hr, hMod⟩ :=
    p4Q2PZ37ADM_originalCenteredCovariance_uniformChordalModulus H e ε hε
  obtain ⟨s, hNet⟩ := p4Q2PZ37AEE_originalFullFiniteNet_exists H r hr
  exact ⟨r, hr, s, hNet,
    p4Q2PZ37AEE_certifiedFiniteNet_covarianceApprox H e s r ε hNet hMod⟩

/-- ACI's genuine nonzero Wilson covariance cannot disappear at all
points of a sufficiently fine genuine FINITE boundary-pair sample.
The sample radius and sample values remain existential, not numeric. -/
theorem p4Q2PZ37AEE_everyLink_nonzeroFiniteSample_exists
    (e : Link) :
    ∃ (r : ℝ) (s : Finset Pair) (a : Pair),
      0 < r ∧ a ∈ s ∧
      p4Q2PZ37AEE_isOriginalFullNet H s r ∧
      0 < |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| := by
  obtain ⟨a₀, ha₀⟩ :=
    p4Q2PZ37ACI_centeredEnergyCovariance_nonzero
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos e
        (originalWilsonExplicitIdentityBoundary H)
  have hAmp : 0 < |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a₀| :=
    abs_pos.mpr ha₀
  have hε :
      0 < |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a₀| / 2 :=
    half_pos hAmp
  obtain ⟨r, hr, s, hNet, hApprox⟩ :=
    p4Q2PZ37AEE_everyLink_finiteAmplitudeApprox_exists
      H e (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a₀| / 2) hε
  obtain ⟨a, ha, hClose⟩ := hApprox a₀
  refine ⟨r, s, a, hr, ha, hNet, ?_⟩
  linarith only [hAmp, hClose]

/-- Arbitrary verified oscillation epsilon (not just AED's half-amplitude)
gives a strengthened exact TRUE physical double-ball moment certificate.
If 0 <= epsilon < C_e(a) and ALL actual D_H-displacements below R
change C_e by at most epsilon, the two gauge-opposite balls are disjoint,
have the original AEC polynomial Haar mass, and contribute at least
(C_e(a)-epsilon)^2 each. No numerical modulus is assumed to hold. -/
theorem p4Q2PZ37AEE_certifiedTwoSignError_doubleMomentFloor
    (e : Link) (a : Pair) (R ε : ℝ)
    (hR : 0 < R) (hε : 0 ≤ ε)
    (hAmp : ε < C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a)
    (hMod : ∀ z w : Pair, D z w < R →
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z -
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e w| ≤ ε) :
    (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a - ε) ^ 2 *
      (2 * (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
        (8 * Fintype.card Link)) ≤
      S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  let A : ℝ := C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a - ε
  have hA : 0 < A := sub_pos.mpr hAmp
  have hFlip :
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e (Gamma e a) =
        -C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a :=
    p4Q2PZ37ACC_centeredReceiver_covariance_centerGauge
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a
  have hPos : ∀ z ∈ Ball a R, A ≤
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z := by
    intro z hz
    have h := (abs_le.mp (hMod a z hz)).2
    dsimp [A]
    linarith
  have hNeg : ∀ z ∈ Ball (Gamma e a) R,
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z ≤ -A := by
    intro z hz
    have h := (abs_le.mp (hMod (Gamma e a) z hz)).1
    rw [hFlip] at h
    dsimp [A]
    linarith
  have hd : Disjoint (Ball a R) (Ball (Gamma e a) R) := by
    apply Set.disjoint_left.mpr
    intro z hz₁ hz₂
    have hp := hPos z hz₁
    have hn := hNeg z hz₂
    linarith only [hp, hn, hA]
  have hUnion : Measure.real outer (Ball a R ∪ Ball (Gamma e a) R) =
      Measure.real outer (Ball a R) +
      Measure.real outer (Ball (Gamma e a) R) :=
    measureReal_union hd
      (p4Q2PZ37ADL_originalFullChordalBall_isOpen H (Gamma e a) R).measurableSet
  have hMass :
      2 * (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
        (8 * Fintype.card Link) ≤
        Measure.real outer (Ball a R ∪ Ball (Gamma e a) R) := by
    have hOne :=
      p4Q2PZ37AEC_originalFullBall_mass_ge_minPolynomial H a R hR
    have hTwo :=
      p4Q2PZ37AEC_originalFullBall_mass_ge_minPolynomial H (Gamma e a) R hR
    rw [hUnion]
    linarith only [hOne, hTwo]
  have hAbs : ∀ z ∈ Ball a R ∪ Ball (Gamma e a) R,
      A ≤ |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| := by
    intro z hz
    rcases hz with hz₁ | hz₂
    · exact (hPos z hz₁).trans (le_abs_self _)
    · have h := hNeg z hz₂
      exact (by linarith :
        A ≤ -C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z).trans
          (neg_le_abs _)
  have hMoment :=
    p4Q2PZ37ADE_originalOpenCovarianceRegion_lowerMoment
      H e (Ball a R ∪ Ball (Gamma e a) R) A
      ((p4Q2PZ37ADL_originalFullChordalBall_isOpen H a R).union
        (p4Q2PZ37ADL_originalFullChordalBall_isOpen H (Gamma e a) R))
      hA hAbs
  change A ^ 2 *
    (2 * (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
      (8 * Fintype.card Link)) ≤
    S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e
  exact (mul_le_mul_of_nonneg_left hMass (sq_nonneg A)).trans hMoment

/-- At certified original full-chordal radius 1/2, the exact AEC
polynomial is a rational H-dependent coefficient, while the physically
verified error epsilon and observed C_e(a) remain explicit inputs. -/
theorem p4Q2PZ37AEE_certifiedHalfRadiusError_doubleMomentFloor
    (e : Link) (a : Pair) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hAmp : ε < C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a)
    (hMod : ∀ z w : Pair, D z w < (1 / 2 : ℝ) →
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z -
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e w| ≤ ε) :
    (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a - ε) ^ 2 *
      (2 * (1 / (8 * (2 * (Fintype.card Link : ℝ) + 1))) ^
        (8 * Fintype.card Link)) ≤
      S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  have h :=
    p4Q2PZ37AEE_certifiedTwoSignError_doubleMomentFloor
      H e a (1 / 2) ε (by norm_num) hε hAmp hMod
  rw [p4Q2PZ37AED_originalHalfRadius_polynomial_eq_rational H] at h
  exact h

/-- A genuinely certified finite-H two-ball error floor gives
positive original mean GI SQUARED budget ONLY if the separate numerical
FC envelope dominance test is supplied. This does not turn physical
existence of a,r,epsilon into a verified GI threshold. -/
theorem p4Q2PZ37AEE_certifiedErrorFloor_FC_dominance_gives_GI
    (e : Link) (a : Pair) (R ε : ℝ)
    (hR : 0 < R) (hε : 0 ≤ ε)
    (hAmp : ε < C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a)
    (hMod : ∀ z w : Pair, D z w < R →
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z -
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e w| ≤ ε)
    (hNumeric : (B b₀ p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 <
      272 * ((C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a - ε) ^ 2 *
        (2 * (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
          (8 * Fintype.card Link)))) :
    0 < Budget b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  have hMoment :=
    p4Q2PZ37AEE_certifiedTwoSignError_doubleMomentFloor
      H e a R ε hR hε hAmp hMod
  have hScaled :=
    mul_le_mul_of_nonneg_left hMoment (show (0 : ℝ) ≤ 272 by norm_num)
  exact p4Q2PZ37ADE_fixedCovarianceFC_gives_positiveBudget H e
    (hNumeric.trans_le hScaled)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEE_originalFullFiniteNet_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEE_certifiedFiniteNet_covarianceApprox
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEE_certifiedFiniteTable_globalAmplitudeUpper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEE_everyLink_finiteAmplitudeApprox_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEE_everyLink_nonzeroFiniteSample_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEE_certifiedTwoSignError_doubleMomentFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEE_certifiedHalfRadiusError_doubleMomentFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEE_certifiedErrorFloor_FC_dominance_gives_GI
