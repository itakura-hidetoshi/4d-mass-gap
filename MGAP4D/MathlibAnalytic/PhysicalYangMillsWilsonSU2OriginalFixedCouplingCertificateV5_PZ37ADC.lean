import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalDimensionlessSignalResidualV5_PZ37ADB

/-!
# P4-Q2-PZ37ADC — freeze the genuine Wilson coupling at an exact constant

An append-only theorem leaf on the SAME finite interacting Wilson SU(2)
receiver, its original centered Gauss-law source, Perron ground state,
updated transfer, both actual interacting posterior laws, original
spatial link and original boundary pair-Haar measure.

The constant positive coupling b₀ = log(3/2)/64 makes the exact ACP
posterior exponential-gap square tau(b₀) = (exp(64 b₀)-1)^2 = 1/4.
Consequently ADB's exact original mean GI SQUARED certificate criterion
reduces, for each finite H and actual link e, to
   M_GI(H,b₀,e)>0  iff  v(H,b₀,e)<16*u(H,b₀,e).
The previously PROVED genuine receiver FC allocation
   0<u, 0<=v, u+v<=1
then yields the exact rational sufficient threshold
   u(H,b₀,e)>1/17  ==> M_GI(H,b₀,e)>0.
The nonpositive certificate forces u<=1/17. Positive certificate
implies an OPEN positive original pair-Haar-mass set of nonzero ACTUAL
signed two-posterior GI response by the previous ACO bridge.

Fixing b₀ does NOT freeze the truly H,e-dependent u. We therefore
explicitly isolate the missing uniform physical obligation:
a constant c>1/17 and a proof that c<=u(H,b₀,e) for EVERY H,e
would give positive ORIGINAL mean certificates for all H,e at
the same fixed coupling. Neither this uniform lower bound nor a
continuum 4D Yang–Mills mass gap is asserted or assumed away.
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
local instance p4Q2PZ37ADC_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADC_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADC_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADC_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADC_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADC_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "u" => p4Q2PZ37ADB_originalSignalFCFraction H
local notation "v" => p4Q2PZ37ADB_originalResidualFCFraction H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local notation "tau" => p4Q2PZ37ACP_originalPosteriorExponentGapSq
local instance p4Q2PZ37ADC_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ADC_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- An EXACT positive real Wilson coupling independent of H and e. -/
def p4Q2PZ37ADC_fixedCoupling : ℝ :=
  Real.log (3 / 2 : ℝ) / 64

/-- This coupling is genuinely positive, not a zero-coupling limit. -/
theorem p4Q2PZ37ADC_fixedCoupling_pos :
    0 < p4Q2PZ37ADC_fixedCoupling := by
  unfold p4Q2PZ37ADC_fixedCoupling
  exact div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2))
    (by norm_num)

/-- Exact, no numerical approximation: exp(64 b₀) is the rational 3/2. -/
theorem p4Q2PZ37ADC_fixedCoupling_exp_eq :
    Real.exp (64 * p4Q2PZ37ADC_fixedCoupling) = (3 / 2 : ℝ) := by
  have hs :
      (64 : ℝ) * p4Q2PZ37ADC_fixedCoupling =
        Real.log (3 / 2 : ℝ) := by
    unfold p4Q2PZ37ADC_fixedCoupling
    ring
  rw [hs]
  exact Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)

/-- The TRUE ACP posterior exponent-gap square is the rational 1/4. -/
theorem p4Q2PZ37ADC_fixedCoupling_gap_eq_quarter :
    tau p4Q2PZ37ADC_fixedCoupling = (1 / 4 : ℝ) := by
  unfold p4Q2PZ37ACP_originalPosteriorExponentGapSq
  rw [p4Q2PZ37ADC_fixedCoupling_exp_eq]
  norm_num

/-- At the exact b₀, the ADB FC threshold tau/(tau+4) equals 1/17. -/
theorem p4Q2PZ37ADC_fixedCoupling_ratio_eq_seventeenth :
    tau p4Q2PZ37ADC_fixedCoupling /
        (tau p4Q2PZ37ADC_fixedCoupling + 4) = (1 / 17 : ℝ) := by
  rw [p4Q2PZ37ADC_fixedCoupling_gap_eq_quarter]
  norm_num

/-- FIXED-COUPLING EXACT GI squared-mean certificate test.
The finite-volume receiver, residual, link and original posterior stay
UNCHANGED: only the scalar physical coupling has been fixed. -/
theorem p4Q2PZ37ADC_fixedCoupling_budget_pos_iff
    (e : Link) :
    0 < Budget p4Q2PZ37ADC_fixedCoupling
        p4Q2PZ37ADC_fixedCoupling_pos.le e ↔
      v p4Q2PZ37ADC_fixedCoupling
        p4Q2PZ37ADC_fixedCoupling_pos.le e <
      16 * u p4Q2PZ37ADC_fixedCoupling
        p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  have h :=
    p4Q2PZ37ADB_originalGIMeanBudget_pos_iff_dimensionless
      H p4Q2PZ37ADC_fixedCoupling
        p4Q2PZ37ADC_fixedCoupling_pos e
  rw [p4Q2PZ37ADC_fixedCoupling_gap_eq_quarter] at h
  constructor
  · intro hh
    have hratio := h.mp hh
    linarith only [hratio]
  · intro hh
    apply h.mpr
    linarith only [hh]

/-- The genuine original FC budget gives the concrete *rational*
sufficient threshold u>1/17 for the EXACT fixed coupling. No lower
bound on u is asserted to hold for the actual physical Wilson model. -/
theorem p4Q2PZ37ADC_fixedCoupling_signal_gt_seventeenth_budget_pos
    (e : Link)
    (hSignal : (1 / 17 : ℝ) <
      u p4Q2PZ37ADC_fixedCoupling
        p4Q2PZ37ADC_fixedCoupling_pos.le e) :
    0 < Budget p4Q2PZ37ADC_fixedCoupling
      p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  have hv := p4Q2PZ37ADB_originalResidualShare_le_unusedSignal
    H p4Q2PZ37ADC_fixedCoupling
      p4Q2PZ37ADC_fixedCoupling_pos e
  apply (p4Q2PZ37ADC_fixedCoupling_budget_pos_iff H e).mpr
  linarith only [hSignal, hv]

/-- The exact same fixed coupling and scalar signal threshold yield an
OPEN original boundary-pair-Haar locus of nonzero REAL signed
two-interacting-posterior GI response, conditionally. -/
theorem p4Q2PZ37ADC_fixedCoupling_signal_gt_seventeenth_openGI
    (e : Link)
    (hSignal : (1 / 17 : ℝ) <
      u p4Q2PZ37ADC_fixedCoupling
        p4Q2PZ37ADC_fixedCoupling_pos.le e) :
    ∃ Uset : Set Pair, IsOpen Uset ∧
      0 < Measure.real outer Uset ∧
      ∀ z ∈ Uset,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H p4Q2PZ37ADC_fixedCoupling
            p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion
    H p4Q2PZ37ADC_fixedCoupling
      p4Q2PZ37ADC_fixedCoupling_pos.le e
    (p4Q2PZ37ADC_fixedCoupling_signal_gt_seventeenth_budget_pos
      H e hSignal)

/-- Reverse quantitative obstruction at the fixed physical coupling:
failure of the positive squared-mean certificate forces u<=1/17.
This does NOT imply the true signed GI response vanishes. -/
theorem p4Q2PZ37ADC_fixedCoupling_nonpositiveBudget_signal_le_seventeenth
    (e : Link)
    (hNonpos : Budget p4Q2PZ37ADC_fixedCoupling
      p4Q2PZ37ADC_fixedCoupling_pos.le e ≤ 0) :
    u p4Q2PZ37ADC_fixedCoupling
      p4Q2PZ37ADC_fixedCoupling_pos.le e ≤ (1 / 17 : ℝ) := by
  have hOb :=
    (p4Q2PZ37ADB_originalGIMeanBudget_nonpos_iff_obstruction
      H p4Q2PZ37ADC_fixedCoupling
        p4Q2PZ37ADC_fixedCoupling_pos e).mp hNonpos
  have hv := p4Q2PZ37ADB_originalResidualShare_le_unusedSignal
    H p4Q2PZ37ADC_fixedCoupling
      p4Q2PZ37ADC_fixedCoupling_pos e
  rw [p4Q2PZ37ADC_fixedCoupling_gap_eq_quarter] at hOb
  linarith only [hOb, hv]

/-- A genuinely constant lower bound c, valid across ALL physical
links at a fixed H, suffices when c>1/17. Positivity of c alone is
not enough; the numerical comparison is the still-open obligation. -/
theorem p4Q2PZ37ADC_fixedVolume_linkUniformSignal_bound
    (c : ℝ) (hc : (1 / 17 : ℝ) < c)
    (hLower : ∀ e : Link, c ≤
      u p4Q2PZ37ADC_fixedCoupling
        p4Q2PZ37ADC_fixedCoupling_pos.le e) :
    ∀ e : Link, 0 < Budget p4Q2PZ37ADC_fixedCoupling
      p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  intro e
  exact p4Q2PZ37ADC_fixedCoupling_signal_gt_seventeenth_budget_pos
    H e (lt_of_lt_of_le hc (hLower e))

/-- The exact remaining volume-uniform physical obligation, expressed
with a SINGLE scalar c independent of H and e. We prove the CONDITIONAL
deduction only; existence of this c for the genuine Wilson data is OPEN. -/
theorem p4Q2PZ37ADC_allFiniteVolumes_of_uniformSignalConstant
    (c : ℝ) (hc : (1 / 17 : ℝ) < c)
    (hUniform : ∀ n : ℕ,
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink n,
        c ≤ p4Q2PZ37ADB_originalSignalFCFraction n
          p4Q2PZ37ADC_fixedCoupling
          p4Q2PZ37ADC_fixedCoupling_pos.le e) :
    ∀ n : ℕ,
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink n,
        0 < p4Q2PZ37ACO_originalGIMeanBudget n
          p4Q2PZ37ADC_fixedCoupling
          p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  intro n e
  exact p4Q2PZ37ADC_fixedCoupling_signal_gt_seventeenth_budget_pos
    n e (lt_of_lt_of_le hc (hUniform n e))

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling_exp_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling_gap_eq_quarter
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling_ratio_eq_seventeenth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling_budget_pos_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling_signal_gt_seventeenth_budget_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling_signal_gt_seventeenth_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling_nonpositiveBudget_signal_le_seventeenth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedVolume_linkUniformSignal_bound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADC_allFiniteVolumes_of_uniformSignalConstant
