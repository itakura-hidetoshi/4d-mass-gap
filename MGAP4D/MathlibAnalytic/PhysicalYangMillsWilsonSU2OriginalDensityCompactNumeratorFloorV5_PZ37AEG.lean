import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalNumeratorDenominatorModulusV5_PZ37AEF
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEG — genuine finite-H density floor and numerator regularity

AEF separated the ACTUAL original centered-source Wilson covariance
C_e = N_e / q_H, where N_e is the exact original SU(2) Haar integral
of the original FF physical source receiver times Wilson character,
and q_H is JQ's original Perron/transfer density-cancellation weight.

This append-only module proves that at each genuine finite volume H:
* q_H is CONTINUOUS and everywhere positive on the original compact
  two-boundary configuration space;
* the original continuous-vacuum factors in q_H cancel EXACTLY,
  q_H(z)=‖T_H‖⁻¹ / continuousJointSqrtDensity_H(z);
* the true joint sqrt-density attains a positive finite maximum,
  which supplies an authentic strictly positive H-dependent lower
  bound on q_H (not a numeric constant);
* N_e equals C_e*q_H and is continuous, with a strictly positive
  attained finite global absolute maximum for every physical link;
* N_e and q_H each have genuine global uniform continuity moduli in
  the SAME full calibrated all-link D_H distance;
* for any strictly positive numerator and denominator error budgets,
  there exist one common genuine radius and original finite-H
  numerator/density certificates satisfying the AEF interface.

The proof does NOT calculate the maximal true joint sqrt-density,
the true Perron transfer norm, finite-net samples, the H-dependent
minimum density, the true source Haar numerator, the stability radius,
the AEF/GI numerical threshold, H-uniform coercivity, physical spectral
gap or continuum 4D Yang-Mills mass gap. All original Wilson SU(2)
objects, Gauss-law physical source, FF receiver, actual two interacting
posteriors, pair-Haar law, fixed toolchain and theorem root are unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AEG_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEG_compactG : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEG_countableG : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEG_measurableG : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEG_borelG : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "q" => p4Q2JQ_originalPhysicalGIDensityWeight H
local notation "N" => p4Q2PZ37AEF_originalCenteredCovarianceNumerator H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "W" =>
  normalizedPhysicalOneSlabJointHalfDensityWeightBCF H 2 (by norm_num) b0 hb0
local notation "V" =>
  normalizedPhysicalOneSlabContinuousVacuumInverseBCF H 2 (by norm_num) b0 hb0
local notation "rho" =>
  continuousJointSqrtDensity H 2 (by norm_num) b0 hb0
local notation "Omega" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H 2 (by norm_num) b0 hb0
local notation "L" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b0 hb0‖⁻¹

local instance p4Q2PZ37AEG_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AEG_pairCompact : CompactSpace Pair := by
  infer_instance

/-- In the ORIGINAL physical JQ density weight, the original
strictly positive continuous vacuum Ω(z.2) and its inverse cancel
EXACTLY; the remaining inverse transfer norm and joint sqrt-density
are unchanged. This is an algebraic identity, not an approximate
or replacement posterior law. -/
theorem p4Q2PZ37AEG_originalDensity_exactVacuumCancellation
    (z : Pair) :
    q b0 hb0 z = L / rho z := by
  have hOmega : Omega z.2 ≠ 0 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H 2 (by norm_num) b0 hb0 z.2).ne'
  have hRho : rho z ≠ 0 :=
    (continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 z).ne'
  change (L * Omega z.2 / rho z) * (Omega z.2)⁻¹ = L / rho z
  field_simp [hOmega, hRho]

/-- True original JQ density is continuous on the genuine finite-H
compact two-boundary configuration space: both BCF factors are
ALREADY actual continuous maps, without inserting a new density. -/
theorem p4Q2PZ37AEG_originalDensity_continuous :
    Continuous (fun z : Pair => q b0 hb0 z) := by
  let w := normalizedPhysicalOneSlabJointHalfDensityWeightBCF
    H 2 (by norm_num) b0 hb0
  let v := normalizedPhysicalOneSlabContinuousVacuumInverseBCF
    H 2 (by norm_num) b0 hb0
  change Continuous (fun z : Pair => w z * v z.2)
  exact w.continuous.mul (v.continuous.comp continuous_snd)

/-- The genuine joint sqrt-density reaches an actual finite positive
maximum over all true original boundary pairs at each fixed H. -/
theorem p4Q2PZ37AEG_originalJointSqrtDensity_positiveMaximum_exists :
    ∃ M : ℝ, 0 < M ∧ ∀ z : Pair, rho z ≤ M := by
  have hQ : Continuous (fun z : Pair => q b0 hb0 z) :=
    p4Q2PZ37AEG_originalDensity_continuous H
  have hQne : ∀ z : Pair, q b0 hb0 z ≠ 0 :=
    fun z => (p4Q2PZ37AEF_originalDensity_pos H z).ne'
  have hL : L ≠ 0 := (inv_pos.mpr
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) b0 hb0)).ne'
  have hRhoEq : (fun z : Pair => rho z) =
      (fun z : Pair => L / q b0 hb0 z) := by
    funext z
    have hr : rho z ≠ 0 :=
      (continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 z).ne'
    rw [p4Q2PZ37AEG_originalDensity_exactVacuumCancellation H z]
    field_simp [hL, hr]
  have hrho : Continuous (fun z : Pair => rho z) := by
    rw [hRhoEq]
    exact continuous_const.div hQ hQne
  let z0 : Pair := (originalWilsonExplicitIdentityBoundary H,
    originalWilsonExplicitIdentityBoundary H)
  obtain ⟨a, _ha, hMax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set Pair)).exists_isMaxOn
      ⟨z0, Set.mem_univ z0⟩ hrho.continuousOn
  exact ⟨rho a,
    continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 a,
    fun z => hMax (Set.mem_univ z)⟩

/-- A verified upper majorant for the original joint sqrt-density
gives an explicit finite-H physical density lower bound involving
the ACTUAL positive inverse Perron/transfer operator norm. -/
theorem p4Q2PZ37AEG_originalDensity_ge_transferInverseOverSqrtMajorant
    (M : ℝ) (hM : 0 < M)
    (hRhoBound : ∀ z : Pair, rho z ≤ M)
    (z : Pair) :
    L / M ≤ q b0 hb0 z := by
  rw [p4Q2PZ37AEG_originalDensity_exactVacuumCancellation H z]
  have hL : 0 ≤ L := le_of_lt (inv_pos.mpr
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) b0 hb0))
  have hr : 0 < rho z :=
    continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 z
  apply (div_le_div_iff₀ hM hr).mpr
  have hm := mul_le_mul_of_nonneg_left (hRhoBound z) hL
  nlinarith only [hm]

/-- The ORIGINAL density has a strictly positive finite-H lower
constant. This is an exact existential factorization
  λ_H=‖T_H‖⁻¹ / max_z continuousJointSqrtDensity_H(z) > 0,
not a computed lower bound or an H-uniform estimate. -/
theorem p4Q2PZ37AEG_originalDensity_globalPositiveFloor_exists :
    ∃ lambda : ℝ, 0 < lambda ∧
      ∀ z : Pair, lambda ≤ q b0 hb0 z := by
  obtain ⟨M, hM, hMajorant⟩ :=
    p4Q2PZ37AEG_originalJointSqrtDensity_positiveMaximum_exists H
  have hL : 0 < L := inv_pos.mpr
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) b0 hb0)
  exact ⟨L / M, div_pos hL hM,
    fun z => p4Q2PZ37AEG_originalDensity_ge_transferInverseOverSqrtMajorant
      H M hM hMajorant z⟩

/-- The AEF TRUE original Haar numerator equals the genuine centered
physical covariance times the unchanged positive density, pointwise.
This is a rearrangement of the exact ACI identity, not a new law. -/
theorem p4Q2PZ37AEG_originalNumerator_eq_covariance_mul_density
    (e : Link) (z : Pair) :
    N e z = C b0 hb0 e z * q b0 hb0 z := by
  have hq : q b0 hb0 z ≠ 0 :=
    (p4Q2PZ37AEF_originalDensity_pos H z).ne'
  calc
    N e z = (N e z / q b0 hb0 z) * q b0 hb0 z := by
      field_simp [hq]
    _ = C b0 hb0 e z * q b0 hb0 z := by
      rw [p4Q2PZ37AEF_originalCovariance_eq_trueNumerator_div_density H e z]

/-- Real continuity of the ACTUAL original source-dependent Wilson
Haar numerator, obtained from ACD's genuine covariance continuity
and the true BCF density product. -/
theorem p4Q2PZ37AEG_originalNumerator_continuous (e : Link) :
    Continuous (fun z : Pair => N e z) := by
  have hC : Continuous (fun z : Pair => C b0 hb0 e z) :=
    p4Q2PZ37ACD_originalReceiver_covariance_continuous
      H b0 hb0 f0 e
  have hQ := p4Q2PZ37AEG_originalDensity_continuous H
  have hEq : (fun z : Pair => N e z) =
      (fun z : Pair => C b0 hb0 e z * q b0 hb0 z) := by
    funext z
    exact p4Q2PZ37AEG_originalNumerator_eq_covariance_mul_density H e z
  rw [hEq]
  exact hC.mul hQ

/-- For every genuine physical link, the original Haar numerator has
a strictly positive, actually attained global ABSOLUTE maximum on the
compact original finite-H boundary-pair space. No numeric maximum
is reported. -/
theorem p4Q2PZ37AEG_originalNumerator_positiveMaxAbs_exists
    (e : Link) :
    ∃ M : ℝ, 0 < M ∧
      ∀ z : Pair, |N e z| ≤ M := by
  obtain ⟨z0, hz0⟩ :=
    p4Q2PZ37AEF_originalEveryLink_nonzeroTrueNumerator H e
  have hN := p4Q2PZ37AEG_originalNumerator_continuous H e
  obtain ⟨a, _ha, hMax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set Pair)).exists_isMaxOn
      ⟨z0, Set.mem_univ z0⟩ hN.abs.continuousOn
  refine ⟨|N e a|, ?_, fun z => hMax (Set.mem_univ z)⟩
  exact (abs_pos.mpr hz0).trans_le (hMax (Set.mem_univ z0))

/-- The genuine Haar numerator has a uniform modulus in the ACTUAL
full all-link calibrated D_H at each finite H and physical link.
Its radius depends on the model, H, link and requested error. -/
theorem p4Q2PZ37AEG_originalNumerator_uniformChordalModulus
    (e : Link) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ R : ℝ, 0 < R ∧ ∀ z w : Pair,
      D z w < R → |N e z - N e w| < delta := by
  exact p4Q2PZ37ADM_compactContinuous_uniformDistanceModulus
    D (p4Q2PZ37ADM_originalFullDistance_jointContinuous H)
    (fun z w => p4Q2PZ37ADL_originalFullDistance_eq_zero_iff H z w)
    (fun z w => p4Q2PZ37ADL_originalFullDistance_nonneg H z w)
    (fun z : Pair => N e z)
    (p4Q2PZ37AEG_originalNumerator_continuous H e)
    delta hdelta

/-- The SAME original Perron/transfer density has a genuine uniform
modulus for arbitrary positive error in the SAME full D_H, not a
hypothetical globally Lipschitz substitute. -/
theorem p4Q2PZ37AEG_originalDensity_uniformChordalModulus
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ R : ℝ, 0 < R ∧ ∀ z w : Pair,
      D z w < R →
        |q b0 hb0 z - q b0 hb0 w| < delta := by
  exact p4Q2PZ37ADM_compactContinuous_uniformDistanceModulus
    D (p4Q2PZ37ADM_originalFullDistance_jointContinuous H)
    (fun z w => p4Q2PZ37ADL_originalFullDistance_eq_zero_iff H z w)
    (fun z w => p4Q2PZ37ADL_originalFullDistance_nonneg H z w)
    (fun z : Pair => q b0 hb0 z)
    (p4Q2PZ37AEG_originalDensity_continuous H)
    delta hdelta

/-- At each finite volume H and genuine link e, the exact AEF
separated numerator/density verification obligations are genuinely
SIMULTANEOUSLY satisfiable for any positive independent requested
errors deltaN and deltaQ. A common actual D_H radius exists, but
none of its witnesses is evaluated numerically here. -/
theorem p4Q2PZ37AEG_originalEveryLink_factorizedCertificates_exist
    (e : Link) (deltaN deltaQ : ℝ)
    (hdeltaN : 0 < deltaN) (hdeltaQ : 0 < deltaQ) :
    ∃ (lambda M R : ℝ),
      0 < lambda ∧ 0 < M ∧ 0 < R ∧
      (∀ z : Pair, lambda ≤ q b0 hb0 z) ∧
      (∀ z : Pair, |N e z| ≤ M) ∧
      (∀ z w : Pair, D z w < R →
        |N e z - N e w| ≤ deltaN) ∧
      (∀ z w : Pair, D z w < R →
        |q b0 hb0 z - q b0 hb0 w| ≤ deltaQ) := by
  obtain ⟨lambda, hlambda, hFloor⟩ :=
    p4Q2PZ37AEG_originalDensity_globalPositiveFloor_exists H
  obtain ⟨M, hM, hMax⟩ :=
    p4Q2PZ37AEG_originalNumerator_positiveMaxAbs_exists H e
  obtain ⟨rN, hrN, hNmod⟩ :=
    p4Q2PZ37AEG_originalNumerator_uniformChordalModulus
      H e deltaN hdeltaN
  obtain ⟨rQ, hrQ, hQmod⟩ :=
    p4Q2PZ37AEG_originalDensity_uniformChordalModulus
      H deltaQ hdeltaQ
  let R : ℝ := min rN rQ
  have hR : 0 < R := lt_min hrN hrQ
  refine ⟨lambda, M, R, hlambda, hM, hR, hFloor, hMax, ?_, ?_⟩
  · intro z w hzw
    exact (hNmod z w (lt_of_lt_of_le hzw (min_le_left _ _))).le
  · intro z w hzw
    exact (hQmod z w (lt_of_lt_of_le hzw (min_le_right _ _))).le

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEG_originalDensity_exactVacuumCancellation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEG_originalDensity_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEG_originalJointSqrtDensity_positiveMaximum_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEG_originalDensity_ge_transferInverseOverSqrtMajorant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEG_originalDensity_globalPositiveFloor_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEG_originalNumerator_eq_covariance_mul_density
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEG_originalNumerator_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEG_originalNumerator_positiveMaxAbs_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEG_originalNumerator_uniformChordalModulus
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEG_originalDensity_uniformChordalModulus
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEG_originalEveryLink_factorizedCertificates_exist
