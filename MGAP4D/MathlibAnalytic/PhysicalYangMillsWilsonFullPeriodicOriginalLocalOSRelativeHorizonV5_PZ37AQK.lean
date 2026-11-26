import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSConnectedGeometricV5_PZ37AQJ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AQK — finite relative decay budget and scalar obstruction

AQJ supplies an absolute geometric envelope B*r^m for the actual centered
finite Wilson reflection correlation, with r = rho^(2k).
AQI supplies a finite log-convex lower envelope. Their combination bounds
the m-th power of the normalized first correlation by (B/a0)*r^m.
A uniform bound B/a0 <= K and a strict target c > q >= r give a finite
integer horizon M, independent of volume and observable, on which the
first ratio is at most c, provided the actual double support budget admits M.
Without control of B/a0, even a positive log-convex finite sequence satisfying
the entire absolute geometric envelope can be constant. This last example is
a scalar logical obstruction, not a counterexample to the Wilson model.
No uniform prefactor, unrestricted operator, continuum or mass gap asserted.
-/
namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace InnerProduct BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 100000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "O" => PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
local notation "P" => periodicHypercubicEvenEdgeOrbitPartition
local notation "L" => PeriodicHypercubicEvenSideLength
local notation "Tau" => periodicHypercubicIntegerTemporalConfigurationTranslation
local notation "Theta" => periodicHypercubicEvenConfigurationReflection
local notation "Gibbs" => periodicHypercubicSpecialUnitaryWilsonSystem
local notation "Pair" => p4Q2PZ37AQC_reflectedPair
local notation "Supported" => p4Q2PZ37APZ_DependsOn
local notation "Local" => p4Q2PZ37AQB_localHalfObservable
local notation "Read" => p4Q2PZ37AQC_boundaryRead
local notation "L2" => periodicHypercubicEvenWilsonOpenHalfObservableL2
local notation "HalfMu" => periodicHypercubicEvenOpenHalfHaarMeasure
local notation "BoundaryMu" => periodicHypercubicEvenBoundaryHaarMeasure
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "Obs" => (fun H : ℕ => BoundedContinuousFunction (O H 2) ℝ)

local instance p4Q2PZ37AQK_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AQK_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AQK_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AQK_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AQK_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AQK_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37AQK_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37AQK_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37AQK_sliceFinite (H : ℕ) : SFinite (Mu H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37AQK_openHalfProbability (H : ℕ) :
    IsProbabilityMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance


local instance p4Q2PZ37AQK_boundaryProbability (H : ℕ) :
    IsProbabilityMeasure (BoundaryMu H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance





local notation "Cfg" => (fun H : ℕ => PeriodicHypercubicEvenEdge H → G)
local notation "FullObs" => (fun H : ℕ => BoundedContinuousFunction (Cfg H) ℝ)
local notation "Ref" => periodicHypercubicEvenEdgeReflection
local notation "Shift" => p4Q2PZ37APZ_edgeShift
local notation "Corr" => p4Q2PZ37AQG_fullReflectedCorrelation
local notation "Conn" => p4Q2PZ37AQH_connectedCorrelation
local notation "Mean" => p4Q2PZ37AQH_fullGibbsMean
local notation "EvenC" => p4Q2PZ37AQI_evenConnected
local notation "Rho" => (fun beta : ℝ => 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)


/-- A strict margin in the target ratio absorbs any fixed finite prefactor
at all sufficiently large integer endpoints. -/
theorem p4Q2PZ37AQK_exists_geometric_horizon
    (K q c : ℝ) (hq : 0 ≤ q) (hqc : q < c) :
    ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, M ≤ m → K * q ^ m ≤ c ^ m := by
  have hc : 0 < c := hq.trans_lt hqc
  have hratio0 : 0 ≤ q / c := div_nonneg hq hc.le
  have hratio1 : q / c < 1 := (div_lt_iff₀ hc).mpr (by simpa using hqc)
  have hlim : Tendsto (fun n : ℕ => K * (q / c) ^ n) atTop (nhds 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1
    simpa using (tendsto_const_nhds.mul hpow :
      Tendsto (fun n : ℕ => K * (q / c) ^ n) atTop (nhds (K * 0)))
  have hev : ∀ᶠ n : ℕ in atTop, K * (q / c) ^ n < 1 :=
    (tendsto_order.1 hlim).2 1 (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N + 1, by omega, ?_⟩
  intro m hm
  have hsmall : K * (q / c) ^ m ≤ 1 := (hN m (by omega)).le
  calc
    K * q ^ m = (K * (q / c) ^ m) * c ^ m := by
      rw [mul_assoc, ← mul_pow, div_mul_cancel₀ _ hc.ne']
    _ ≤ 1 * c ^ m := mul_le_mul_of_nonneg_right hsmall (pow_nonneg hc.le _)
    _ = c ^ m := one_mul _

/-- A finite absolute geometric envelope plus log-convexity does not alone
force a strict relative contraction. The witness is scalar, not a Wilson
observable. It preserves every endpoint inequality through the given m. -/
theorem p4Q2PZ37AQK_absoluteEnvelope_noRelative
    (B r : ℝ) (hB : 0 < B) (hr0 : 0 < r) (hr1 : r < 1) (m : ℕ) :
    ∃ a : ℕ → ℝ, 0 < a 0 ∧ a 1 = a 0 ∧
      (∀ j, 0 ≤ a j) ∧
      (∀ j, a (j + 1) ^ 2 ≤ a j * a (j + 2)) ∧
      (∀ j, j ≤ m → a j ≤ B * r ^ j) := by
  refine ⟨fun _ => B * r ^ m, mul_pos hB (pow_pos hr0 _), rfl, ?_, ?_, ?_⟩
  · intro j
    exact mul_nonneg hB.le (pow_nonneg hr0.le _)
  · intro j
    exact (pow_two (B * r ^ m)).le
  · intro j hj
    have hsplit : m = j + (m - j) := by omega
    have htail : r ^ (m - j) ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hr0.le hr1.le (m - j)
    have hpow : r ^ m ≤ r ^ j := by
      calc
        r ^ m = r ^ j * r ^ (m - j) := by
          rw [← pow_add, ← hsplit]
        _ ≤ r ^ j * 1 := mul_le_mul_of_nonneg_left htail (pow_nonneg hr0.le _)
        _ = r ^ j := mul_one _
    exact mul_le_mul_of_nonneg_left hpow hB.le

/-- The exact absolute AQJ amplitude, including the Gibbs denominator. -/
def p4Q2PZ37AQK_prefactor
    (H : ℕ) (S : Finset (PeriodicHypercubicEvenEdge H)) (beta : ℝ) (u : Obs H) : ℝ :=
  ((S.card : ℝ) * (2 * ‖u‖)) ^ 2 / (1 - Rho beta)

local notation "Bnd" => p4Q2PZ37AQK_prefactor

variable [Nontrivial G]

/-- AQJ's true terminal bound in separated amplitude and stride-ratio form. -/
theorem p4Q2PZ37AQK_evenConnected_le_prefactor
    (H k m : ℕ) (hH : 0 < H) (S : Finset (PeriodicHypercubicEvenEdge H))
    (beta : ℝ) (hb : 0 ≤ beta) (hThreshold : Rho beta < 1) (u : Obs H)
    (hu : Supported H (↑S : Set (PeriodicHypercubicEvenEdge H))
      (fun A => u ((P H).positiveRestriction A)))
    (hbudget : ∀ e ∈ S, (e.1 0).val + m * k + m * k ≤ H) :
    EvenC H k m beta hb u ≤ Bnd H S beta u * (Rho beta ^ (k + k)) ^ m := by
  calc
    _ ≤ (Rho beta ^ (m * k + m * k) / (1 - Rho beta)) *
        ((S.card : ℝ) * (2 * ‖u‖)) ^ 2 :=
      p4Q2PZ37AQJ_evenConnected_le_geometric H k m hH S beta hb hThreshold u hu hbudget
    _ = _ := by
      unfold p4Q2PZ37AQK_prefactor
      rw [show m * k + m * k = (k + k) * m by ring, pow_mul]
      ring

/-- The actual normalized first correlation power is bounded by the
absolute-to-OS prefactor ratio, not merely the absolute Gibbs envelope. -/
theorem p4Q2PZ37AQK_evenConnected_ratioPower_le
    (H k m : ℕ) (hH : 0 < H) (hm : 0 < m)
    (S : Finset (PeriodicHypercubicEvenEdge H))
    (beta : ℝ) (hb : 0 ≤ beta) (hThreshold : Rho beta < 1) (u : Obs H)
    (hu : Supported H (↑S : Set (PeriodicHypercubicEvenEdge H))
      (fun A => u ((P H).positiveRestriction A)))
    (hp : ∀ e ∈ S, periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.positive)
    (hbudget : ∀ e ∈ S, (e.1 0).val + m * k + m * k ≤ H)
    (hbase : 0 < EvenC H k 0 beta hb u) :
    (EvenC H k 1 beta hb u / EvenC H k 0 beta hb u) ^ m ≤
      (Bnd H S beta u / EvenC H k 0 beta hb u) * (Rho beta ^ (k + k)) ^ m := by
  apply (mul_le_mul_iff_of_pos_left hbase).mp
  calc
    _ = (EvenC H k 1 beta hb u / EvenC H k 0 beta hb u) ^ m * EvenC H k 0 beta hb u :=
      mul_comm _ _
    _ ≤ EvenC H k m beta hb u :=
      p4Q2PZ37AQI_evenConnected_ratioPower H k m hm (↑S) beta hb u hu hp hbudget hbase
    _ ≤ Bnd H S beta u * (Rho beta ^ (k + k)) ^ m :=
      p4Q2PZ37AQK_evenConnected_le_prefactor H k m hH S beta hb hThreshold u hu hbudget
    _ = _ := by
      rw [← mul_assoc, mul_comm (EvenC H k 0 beta hb u), div_mul_cancel₀ _ hbase.ne']

/-- A bound on the actual amplitude relative to the actual nonzero
initial correlation gives a finite terminal test with any common rate q. -/
theorem p4Q2PZ37AQK_first_of_relative_budget
    (H k m : ℕ) (hH : 0 < H) (hm : 0 < m)
    (S : Finset (PeriodicHypercubicEvenEdge H))
    (beta : ℝ) (hb : 0 ≤ beta) (hThreshold : Rho beta < 1) (u : Obs H)
    (hu : Supported H (↑S : Set (PeriodicHypercubicEvenEdge H))
      (fun A => u ((P H).positiveRestriction A)))
    (hp : ∀ e ∈ S, periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.positive)
    (hbudget : ∀ e ∈ S, (e.1 0).val + m * k + m * k ≤ H)
    (hbase : 0 < EvenC H k 0 beta hb u)
    (K q c : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hRate : Rho beta ^ (k + k) ≤ q)
    (hPref : Bnd H S beta u ≤ K * EvenC H k 0 beta hb u)
    (hGeom : K * q ^ m ≤ c ^ m) :
    EvenC H k 1 beta hb u ≤ c * EvenC H k 0 beta hb u := by
  have hRho : 0 ≤ Rho beta := mul_nonneg (by norm_num)
    (periodicHypercubicSpecialUnitaryActiveTVMajorant_nonneg beta hb)
  have hPow : (Rho beta ^ (k + k)) ^ m ≤ q ^ m :=
    pow_le_pow_left₀ (pow_nonneg hRho _) hRate m
  have hKbase : 0 ≤ K * EvenC H k 0 beta hb u := mul_nonneg hK hbase.le
  have hterm : EvenC H k m beta hb u ≤ c ^ m * EvenC H k 0 beta hb u := by
    calc
      _ ≤ Bnd H S beta u * (Rho beta ^ (k + k)) ^ m :=
        p4Q2PZ37AQK_evenConnected_le_prefactor H k m hH S beta hb hThreshold u hu hbudget
      _ ≤ (K * EvenC H k 0 beta hb u) * (Rho beta ^ (k + k)) ^ m :=
        mul_le_mul_of_nonneg_right hPref (pow_nonneg (pow_nonneg hRho _) _)
      _ ≤ (K * EvenC H k 0 beta hb u) * q ^ m :=
        mul_le_mul_of_nonneg_left hPow hKbase
      _ = (K * q ^ m) * EvenC H k 0 beta hb u := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hGeom hbase.le
  exact p4Q2PZ37AQI_evenConnected_terminalThreshold H k m hm (↑S) beta hb u hu hp
    hbudget hbase c hc hterm

/-- One common finite horizon works across the actual finite models and
observable supports admitting the same relative prefactor and stride-rate
budgets. No assumption that these budgets hold is introduced. -/
theorem p4Q2PZ37AQK_exists_uniform_relative_horizon
    (K q c : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hqc : q < c) (hc1 : c < 1) :
    0 < c ∧ c < 1 ∧ ∃ M : ℕ, 0 < M ∧
      ∀ (H k m : ℕ) (_hH : 0 < H) (_hm : M ≤ m)
        (S : Finset (PeriodicHypercubicEvenEdge H))
        (beta : ℝ) (hb : 0 ≤ beta) (_hThreshold : Rho beta < 1) (u : Obs H),
        Supported H (↑S : Set (PeriodicHypercubicEvenEdge H))
          (fun A => u ((P H).positiveRestriction A)) →
        (∀ e ∈ S, periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.positive) →
        (∀ e ∈ S, (e.1 0).val + m * k + m * k ≤ H) →
        0 < EvenC H k 0 beta hb u →
        Rho beta ^ (k + k) ≤ q →
        Bnd H S beta u ≤ K * EvenC H k 0 beta hb u →
        EvenC H k 1 beta hb u ≤ c * EvenC H k 0 beta hb u := by
  have hc : 0 < c := hq.trans_lt hqc
  obtain ⟨M, hM, hGeom⟩ := p4Q2PZ37AQK_exists_geometric_horizon K q c hq hqc
  refine ⟨hc, hc1, M, hM, ?_⟩
  intro H k m hH hm S beta hb hThreshold u hu hp hbudget hbase hRate hPref
  exact p4Q2PZ37AQK_first_of_relative_budget H k m hH (by omega) S beta hb hThreshold u
    hu hp hbudget hbase K q c hK hc.le hRate hPref (hGeom m hm)

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQK_exists_geometric_horizon
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQK_absoluteEnvelope_noRelative
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQK_prefactor
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQK_evenConnected_le_prefactor
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQK_evenConnected_ratioPower_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQK_first_of_relative_budget
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQK_exists_uniform_relative_horizon
