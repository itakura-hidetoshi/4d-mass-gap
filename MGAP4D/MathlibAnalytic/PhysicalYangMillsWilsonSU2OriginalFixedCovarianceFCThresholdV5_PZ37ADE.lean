import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedCouplingCertificateV5_PZ37ADC

/-!
# P4-Q2-PZ37ADE — truly physical fixed-coupling covariance threshold

Append-only theorems on the SAME finite interacting Wilson SU(2)
physical receiver, centered Gauss-law source, positive Perron ground
representative, updated transfer section, actual two interacting
posteriors, and original boundary pair-Haar measure.

At ADC's exactly fixed b0=log(3/2)/64, the true source covariance
second moment S(H,b0,e)>0 and original finite-volume FC envelope
B(H,b0)^2>0 still depend on H (and S on e). The rational ADC test is
    u(H,b0,e)>1/17  IFF  B(H,b0)^2 < 272*S(H,b0,e).
This is a complete exact conversion, not an estimate of S.

The EXISTING ACI+ACD genuinely construct nonzero original covariance
regions with positive outer pair-Haar mass. The original ACJ integral
argument gives, for any open measurable A on which |Cov|>=a>0,
    a^2 * ν_H(A) <= S(H,b0,e).
Thus the physically numerical (currently unproved) condition
    B(H,b0)^2 < 272*a^2*ν_H(A)
suffices for the ORIGINAL mean GI SQUARED certificate, and existing
ACO provides an OPEN positive-pair-Haar nonzero SIGNED two-posterior GI
region. Conversely if the original mean certificate is nonpositive,
then ALL such genuinely constrained covariance regions satisfy
    272*a^2*ν_H(A) <= B(H,b0)^2.
Neither the unconditional existence of a positive region nor S>0
alone guarantees the STRICT numerical condition.

At each fixed finite H with nonempty physical link type, existence of
a strictly positive minimum s_H=min_e S(H,b0,e) is formally proved.
The additional numerical comparison B(H,b0)^2 < 272*s_H would suffice
for all physical links of this H, but is NOT derived from positivity.
No H-uniform lower bound, Wilson Gibbs sampling replacement, or
continuum 4D Yang–Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local instance p4Q2PZ37ADE_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADE_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADE_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADE_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADE_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADE_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "b₀" => p4Q2PZ37ADC_fixedCoupling
local notation "hb₀" => p4Q2PZ37ADC_fixedCoupling_pos
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "Cov" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "u" => p4Q2PZ37ADB_originalSignalFCFraction H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local instance p4Q2PZ37ADE_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ADE_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Pure REAL elementary equivalence converting the exact ADB
dimensionless signal ratio into an evaluated integer coefficient 272. -/
theorem p4Q2PZ37ADE_realSignalThreshold_iff
    (x s : ℝ) (hx : 0 < x) :
    (1 / 17 : ℝ) < 16 * s / x ↔ x < 272 * s := by
  constructor
  · intro h
    have hc := (lt_div_iff₀ hx).mp h
    nlinarith only [hc]
  · intro h
    apply (lt_div_iff₀ hx).mpr
    nlinarith only [h]

/-- Exact weak complementary numerical obstruction. -/
theorem p4Q2PZ37ADE_realSignalNonpositive_iff
    (x s : ℝ) (hx : 0 < x) :
    16 * s / x ≤ (1 / 17 : ℝ) ↔ 272 * s ≤ x := by
  constructor
  · intro h
    have hc := (div_le_iff₀ hx).mp h
    nlinarith only [hc]
  · intro h
    apply (div_le_iff₀ hx).mpr
    nlinarith only [h]

/-- A positive local original covariance region contribution
exceeding the rational FC budget implies the exact global moment
criterion, with no probabilistic independence or new physical law. -/
theorem p4Q2PZ37ADE_realLocalMoment_dominance
    (x s a m : ℝ)
    (hLocal : a ^ 2 * m ≤ s)
    (hThreshold : x < 272 * (a ^ 2 * m)) :
    x < 272 * s := by
  nlinarith only [hLocal, hThreshold]

/-- Concrete original Wilson fixed-coupling numerical margin, NOT
claimed positive for arbitrary H,e. -/
def p4Q2PZ37ADE_fixedCovarianceFCMargin
    (e : Link) : ℝ :=
  272 * S b₀ hb₀.le e - (B b₀ hb₀.le) ^ 2

/-- Exact rational ADC test on the SAME original Wilson covariance
moment and unchanged FC envelope at the actual fixed coupling b0. -/
theorem p4Q2PZ37ADE_fixedSignal_iff_originalCovarianceFC
    (e : Link) :
    (1 / 17 : ℝ) < u b₀ hb₀.le e ↔
      (B b₀ hb₀.le) ^ 2 < 272 * S b₀ hb₀.le e := by
  have hB := p4Q2PZ37ADB_originalFCsq_pos H b₀ hb₀ e
  change (1 / 17 : ℝ) <
    (16 * S b₀ hb₀.le e) / (B b₀ hb₀.le) ^ 2 ↔
      (B b₀ hb₀.le) ^ 2 < 272 * S b₀ hb₀.le e
  exact p4Q2PZ37ADE_realSignalThreshold_iff
    ((B b₀ hb₀.le) ^ 2) (S b₀ hb₀.le e) hB

/-- The scalar FC moment gap is positive iff the original rational
ADC signal fraction has crossed its genuinely numerical threshold. -/
theorem p4Q2PZ37ADE_fixedMargin_pos_iff
    (e : Link) :
    0 < p4Q2PZ37ADE_fixedCovarianceFCMargin H e ↔
      (1 / 17 : ℝ) < u b₀ hb₀.le e := by
  rw [p4Q2PZ37ADE_fixedSignal_iff_originalCovarianceFC]
  unfold p4Q2PZ37ADE_fixedCovarianceFCMargin
  exact sub_pos

/-- A single quantitative original covariance-vs-FC inequality
suffices for positive GI SQUARED mean on the same original receiver. -/
theorem p4Q2PZ37ADE_fixedCovarianceFC_gives_positiveBudget
    (e : Link)
    (hNumerical : (B b₀ hb₀.le) ^ 2 < 272 * S b₀ hb₀.le e) :
    0 < Budget b₀ hb₀.le e := by
  exact p4Q2PZ37ADC_fixedCoupling_signal_gt_seventeenth_budget_pos
    H e ((p4Q2PZ37ADE_fixedSignal_iff_originalCovarianceFC H e).mpr
      hNumerical)

/-- The same conditional FC inequality gives a genuinely nonzero
SIGNED two-interacting-posterior response on an OPEN positive original
pair-Haar-mass set, not a surrogate or squared-sign claim. -/
theorem p4Q2PZ37ADE_fixedCovarianceFC_gives_openGI
    (e : Link)
    (hNumerical : (B b₀ hb₀.le) ^ 2 < 272 * S b₀ hb₀.le e) :
    ∃ Uset : Set Pair, IsOpen Uset ∧
      0 < Measure.real outer Uset ∧
      ∀ z ∈ Uset,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b₀ hb₀.le f₀ e z| := by
  exact p4Q2PZ37ADC_fixedCoupling_signal_gt_seventeenth_openGI
    H e ((p4Q2PZ37ADE_fixedSignal_iff_originalCovarianceFC H e).mpr
      hNumerical)

/-- Nonpositive mean GI certificate forces a precise obstruction to
the same ORIGINAL numerical covariance-FC comparison. -/
theorem p4Q2PZ37ADE_nonpositiveBudget_forces_FC_obstruction
    (e : Link)
    (hNonpos : Budget b₀ hb₀.le e ≤ 0) :
    272 * S b₀ hb₀.le e ≤ (B b₀ hb₀.le) ^ 2 := by
  have hu := p4Q2PZ37ADC_fixedCoupling_nonpositiveBudget_signal_le_seventeenth
    H e hNonpos
  have hB := p4Q2PZ37ADB_originalFCsq_pos H b₀ hb₀ e
  change (16 * S b₀ hb₀.le e) / (B b₀ hb₀.le) ^ 2 ≤
    (1 / 17 : ℝ) at hu
  exact (p4Q2PZ37ADE_realSignalNonpositive_iff
    ((B b₀ hb₀.le) ^ 2) (S b₀ hb₀.le e) hB).mp hu

/-- For ANY actual measurable OPEN original outer region whose
covariance has fixed positive magnitude at least a, its real Haar mass
times a² is below the exact original covariance second moment S.
This is ACJ's integral mechanism factored into reusable data. -/
theorem p4Q2PZ37ADE_originalOpenCovarianceRegion_lowerMoment
    (e : Link) (A : Set Pair) (a : ℝ)
    (hOpen : IsOpen A) (ha : 0 < a)
    (hCov : ∀ z ∈ A, a ≤ |Cov b₀ hb₀.le e z|) :
    a ^ 2 * Measure.real outer A ≤ S b₀ hb₀.le e := by
  have hInt : Integrable
      (fun z : Pair => (Cov b₀ hb₀.le e z) ^ 2) outer :=
    ((p4Q2PZ37ACD_originalReceiver_covariance_continuous
      H b₀ hb₀.le f₀ e).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hPoint (z : Pair) (hz : z ∈ A) :
      a ^ 2 ≤ (Cov b₀ hb₀.le e z) ^ 2 := by
    have h := pow_le_pow_left₀ ha.le (hCov z hz) 2
    simpa only [sq_abs] using h
  have hSet :
      a ^ 2 * Measure.real outer A ≤
        ∫ z in A, (Cov b₀ hb₀.le e z) ^ 2 ∂outer :=
    setIntegral_ge_of_const_le_real hOpen.measurableSet
      (measure_ne_top _ _) hPoint hInt.integrableOn
  have hFull : (∫ z in A,
      (Cov b₀ hb₀.le e z) ^ 2 ∂outer) ≤ S b₀ hb₀.le e :=
    setIntegral_le_integral hInt
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  exact hSet.trans hFull

/-- Purely ORIGINAL physical regional sufficient condition for a
positive GI mean certificate at exact b0. The strict numerical
comparison is explicitly a hypothesis, not smuggled positivity. -/
theorem p4Q2PZ37ADE_originalRegionNumeric_gives_positiveBudget
    (e : Link) (A : Set Pair) (a : ℝ)
    (hOpen : IsOpen A) (ha : 0 < a)
    (hCov : ∀ z ∈ A, a ≤ |Cov b₀ hb₀.le e z|)
    (hNumerical :
      (B b₀ hb₀.le) ^ 2 < 272 * (a ^ 2 * Measure.real outer A)) :
    0 < Budget b₀ hb₀.le e := by
  have hMoment :=
    p4Q2PZ37ADE_originalOpenCovarianceRegion_lowerMoment
      H e A a hOpen ha hCov
  exact p4Q2PZ37ADE_fixedCovarianceFC_gives_positiveBudget H e
    (p4Q2PZ37ADE_realLocalMoment_dominance
      ((B b₀ hb₀.le) ^ 2) (S b₀ hb₀.le e)
        a (Measure.real outer A) hMoment hNumerical)

/-- The same local covariance witness condition produces the actual
open pair-Haar region of nonzero signed two-posterior response. -/
theorem p4Q2PZ37ADE_originalRegionNumeric_gives_openGI
    (e : Link) (A : Set Pair) (a : ℝ)
    (hOpen : IsOpen A) (ha : 0 < a)
    (hCov : ∀ z ∈ A, a ≤ |Cov b₀ hb₀.le e z|)
    (hNumerical :
      (B b₀ hb₀.le) ^ 2 < 272 * (a ^ 2 * Measure.real outer A)) :
    ∃ Uset : Set Pair, IsOpen Uset ∧
      0 < Measure.real outer Uset ∧
      ∀ z ∈ Uset,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b₀ hb₀.le f₀ e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion
    H b₀ hb₀.le e
    (p4Q2PZ37ADE_originalRegionNumeric_gives_positiveBudget
      H e A a hOpen ha hCov hNumerical)

/-- If the original mean GI squared certificate is nonpositive, EVERY
actual open covariance region with positive fixed amplitude is too
small (in the above quantitative sense) to cross the 272 threshold.
No vanishing of signed GI is inferred. -/
theorem p4Q2PZ37ADE_nonpositiveBudget_allRegions_FC_obstruction
    (e : Link) (hNonpos : Budget b₀ hb₀.le e ≤ 0)
    (A : Set Pair) (a : ℝ) (hOpen : IsOpen A) (ha : 0 < a)
    (hCov : ∀ z ∈ A, a ≤ |Cov b₀ hb₀.le e z|) :
    272 * (a ^ 2 * Measure.real outer A) ≤
      (B b₀ hb₀.le) ^ 2 := by
  have hM :=
    p4Q2PZ37ADE_originalOpenCovarianceRegion_lowerMoment
      H e A a hOpen ha hCov
  have hB :=
    p4Q2PZ37ADE_nonpositiveBudget_forces_FC_obstruction
      H e hNonpos
  nlinarith only [hM, hB]

/-- ACI's actual nonzero physical covariance and ACD's true local
continuity/Haar theorem provide UNCONDITIONALLY a positive-amplitude
open original covariance region of positive real Haar mass at b0.
Crucially no strict numerical comparison with B² is asserted. -/
theorem p4Q2PZ37ADE_originalPhysicalCovarianceRegion_exists
    (e : Link) :
    ∃ (a : ℝ) (A : Set Pair),
      0 < a ∧ IsOpen A ∧ 0 < Measure.real outer A ∧
      ∀ z ∈ A, a ≤ |Cov b₀ hb₀.le e z| := by
  obtain ⟨z₀, hz₀⟩ :=
    p4Q2PZ37ACI_centeredEnergyCovariance_nonzero
      H b₀ hb₀ e (originalWilsonExplicitIdentityBoundary H)
  obtain ⟨a, V, _, ha, _, _, _, _, hmass, _⟩ :=
    p4Q2PZ37ACD_exists_relativeDefectRegion_of_nonzeroCovariance
      H b₀ hb₀.le f₀ e z₀ hz₀
  let A : Set Pair :=
    p4Q2PZ37ACD_originalCovarianceRegion
      H b₀ hb₀.le f₀ e a V
  refine ⟨a, A, ha,
    p4Q2PZ37ACD_originalCovarianceRegion_isOpen
      H b₀ hb₀.le f₀ e a V, hmass, ?_⟩
  intro z hz
  exact hz.1.le

/-- Concrete physical witness, obtained at every finite H and link
WITHOUT positing any independent Haar model: positive regional energy
a² ν(A), nevertheless with no proven 272 dominance. -/
theorem p4Q2PZ37ADE_originalPositiveLocalMomentWitness_exists
    (e : Link) :
    ∃ (a : ℝ) (A : Set Pair),
      0 < a ∧ IsOpen A ∧
      0 < a ^ 2 * Measure.real outer A ∧
      a ^ 2 * Measure.real outer A ≤ S b₀ hb₀.le e := by
  obtain ⟨a, A, ha, hOpen, hMass, hCov⟩ :=
    p4Q2PZ37ADE_originalPhysicalCovarianceRegion_exists H e
  refine ⟨a, A, ha, hOpen, mul_pos (pow_pos ha 2) hMass, ?_⟩
  exact p4Q2PZ37ADE_originalOpenCovarianceRegion_lowerMoment
    H e A a hOpen ha hCov

/-- Since the genuine link set is finite at a fixed H, its actual
positive covariance-square moments have a common positive minimum s_H.
Neither a numerical 272 gap nor uniformity in H follows from finiteness. -/
theorem p4Q2PZ37ADE_fixedVolumePositiveCovarianceMomentConstant
    [Nonempty Link] :
    ∃ s₀ : ℝ, 0 < s₀ ∧
      ∀ e : Link, s₀ ≤ S b₀ hb₀.le e := by
  classical
  obtain ⟨e₀, _, hMin⟩ :=
    Set.exists_min_image (Set.univ : Set Link)
      (fun e : Link => S b₀ hb₀.le e)
      (Set.finite_univ : (Set.univ : Set Link).Finite)
      (Set.univ_nonempty : (Set.univ : Set Link).Nonempty)
  refine ⟨S b₀ hb₀.le e₀,
    p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos
      H b₀ hb₀ e₀, ?_⟩
  intro e
  exact hMin e (Set.mem_univ e)

/-- A SINGLE scalar s₀ at each fixed H, once independently checked
against the original FC budget, makes the mean GI certificate positive
at ALL genuinely existing physical links of this volume. -/
theorem p4Q2PZ37ADE_fixedVolumeConstant_dominance_allLinks
    [Nonempty Link] (s₀ : ℝ)
    (hLower : ∀ e : Link, s₀ ≤ S b₀ hb₀.le e)
    (hNumeric : (B b₀ hb₀.le) ^ 2 < 272 * s₀) :
    ∀ e : Link, 0 < Budget b₀ hb₀.le e := by
  intro e
  apply p4Q2PZ37ADE_fixedCovarianceFC_gives_positiveBudget H e
  have he := hLower e
  nlinarith only [he, hNumeric]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADE_realSignalThreshold_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADE_realSignalNonpositive_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADE_realLocalMoment_dominance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADE_fixedSignal_iff_originalCovarianceFC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADE_fixedMargin_pos_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADE_fixedCovarianceFC_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADE_fixedCovarianceFC_gives_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADE_nonpositiveBudget_forces_FC_obstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADE_originalOpenCovarianceRegion_lowerMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADE_originalRegionNumeric_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADE_originalRegionNumeric_gives_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADE_nonpositiveBudget_allRegions_FC_obstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADE_originalPhysicalCovarianceRegion_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADE_originalPositiveLocalMomentWitness_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADE_fixedVolumePositiveCovarianceMomentConstant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADE_fixedVolumeConstant_dominance_allLinks
