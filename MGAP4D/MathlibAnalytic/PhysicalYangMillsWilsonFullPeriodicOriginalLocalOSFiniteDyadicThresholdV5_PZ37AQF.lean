import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicOriginalLocalOSFiniteDyadicBudgetV5_PZ37AQE
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AQF — quantitative finite dyadic threshold and obstruction

The actual Wilson OS image is controlled by AQE's finite dyadic estimate.
A positive original OS norm allows an explicit relative root bound. A
relative terminal or Haar budget yields a conditional linear bound, and a
violation forces a strictly larger budget. The zero-norm case of the
threshold statement needs no division. A sharp scalar countermodel shows
that any finite depth and any prescribed relative ceiling above one are
compatible with expansion under the midpoint recurrence alone. This
countermodel is not an assertion of expansion in the Wilson model.
APX/APY remain unchanged. No global contraction or mass gap is asserted.
-/
namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "O" => PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
local notation "P" => periodicHypercubicEvenEdgeOrbitPartition
local notation "Supported" => p4Q2PZ37APZ_DependsOn
local notation "Local" => p4Q2PZ37AQB_localHalfObservable
local notation "Read" => p4Q2PZ37AQC_boundaryRead
local notation "L2" => periodicHypercubicEvenWilsonOpenHalfObservableL2
local notation "HalfMu" => periodicHypercubicEvenOpenHalfHaarMeasure
local notation "BoundaryMu" => periodicHypercubicEvenBoundaryHaarMeasure
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "Obs" => (fun H : ℕ => BoundedContinuousFunction (O H 2) ℝ)

local instance p4Q2PZ37AQF_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AQF_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AQF_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AQF_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AQF_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AQF_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37AQF_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37AQF_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37AQF_sliceFinite (H : ℕ) : SFinite (Mu H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37AQF_openHalfProbability (H : ℕ) :
    IsProbabilityMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance


local instance p4Q2PZ37AQF_boundaryProbability (H : ℕ) :
    IsProbabilityMeasure (BoundaryMu H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance


private theorem pow_split (b : ℝ) (m : ℕ) (hm : 0 < m) :
    b ^ m = b ^ (m - 1) * b := by
  have he : m - 1 + 1 = m := by omega
  calc
    b ^ m = b ^ (m - 1 + 1) := congrArg (fun i : ℕ => b ^ i) he.symm
    _ = _ := pow_succ _ _

/-- Normalize the finite power estimate at a nonzero base. -/
theorem p4Q2PZ37AQF_powerRatio
    (a b M : ℝ) (m : ℕ) (hb : 0 < b) (hm : 0 < m)
    (h : a ^ m ≤ b ^ (m - 1) * M) :
    (a / b) ^ m ≤ M / b := by
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos hb m)).2
  calc
    a ^ m ≤ b ^ (m - 1) * M := h
    _ = b ^ (m - 1) * (M / b * b) := by rw [div_mul_cancel₀ _ hb.ne']
    _ = M / b * b ^ m := by
      rw [pow_split b m hm]
      ring

/-- The exact positive-root relative estimate; no limiting argument. -/
theorem p4Q2PZ37AQF_powerRatioRoot
    (a b M : ℝ) (m : ℕ) (ha : 0 ≤ a) (hb : 0 < b)
    (hM : 0 ≤ M) (hm : 0 < m)
    (h : a ^ m ≤ b ^ (m - 1) * M) :
    a / b ≤ (M / b) ^ ((m : ℝ)⁻¹) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  apply (Real.le_rpow_inv_iff_of_pos
    (div_nonneg ha hb.le) (div_nonneg hM hb.le) hmR).2
  simpa only [Real.rpow_natCast] using
    p4Q2PZ37AQF_powerRatio a b M m hb hm h

/-- A finite power bound with a relative terminal ceiling yields the
corresponding linear threshold, also when the base is zero. -/
theorem p4Q2PZ37AQF_powerThreshold
    (a b M c : ℝ) (m : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hm : 0 < m)
    (h : a ^ m ≤ b ^ (m - 1) * M)
    (hM : M ≤ c ^ m * b) :
    a ≤ c * b := by
  have hpow : a ^ m ≤ (c * b) ^ m := by
    calc
      a ^ m ≤ b ^ (m - 1) * M := h
      _ ≤ b ^ (m - 1) * (c ^ m * b) :=
        mul_le_mul_of_nonneg_left hM (pow_nonneg hb _)
      _ = (c * b) ^ m := by
        rw [mul_pow, pow_split b m hm]
        ring
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  apply (Real.rpow_le_rpow_iff ha (mul_nonneg hc hb) hmR).mp
  simpa only [Real.rpow_natCast] using hpow

/-- Sharp scalar obstruction: at any finite depth, even a prescribed
ceiling M > 1 on all observed terms permits expansion. This is a
countermodel to the scalar inference, not a Wilson counterexample. -/
theorem p4Q2PZ37AQF_finiteRecurrence_noContraction
    (M : ℝ) (hM : 1 < M) (n : ℕ) :
    ∃ a : ℕ → ℝ, (∀ j, 0 ≤ a j) ∧
      (∀ j < n, a j ^ 2 ≤ a (j + 1)) ∧
      (∀ j ≤ n, a j ≤ M) ∧ 1 < a 0 := by
  let m : ℕ := (2 : ℕ) ^ n
  have hm : 0 < m := pow_pos (by norm_num) _
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  let r : ℝ := M ^ ((m : ℝ)⁻¹)
  have hr : 1 < r := Real.one_lt_rpow hM (inv_pos.mpr hmR)
  have hM0 : 0 ≤ M := le_trans zero_le_one hM.le
  have hrpow : r ^ m = M := by
    change (M ^ ((m : ℝ)⁻¹)) ^ m = M
    rw [← Real.rpow_mul_natCast hM0, inv_mul_cancel₀ hmR.ne', Real.rpow_one]
  refine ⟨fun j => r ^ ((2 : ℕ) ^ j), ?_, ?_, ?_, ?_⟩
  · intro j
    exact pow_nonneg (le_trans zero_le_one hr.le) _
  · intro j _
    change (r ^ ((2 : ℕ) ^ j)) ^ 2 ≤ r ^ ((2 : ℕ) ^ (j + 1))
    rw [pow_succ (2 : ℕ) j, pow_mul]
  · intro j hj
    have hp : (2 : ℕ) ^ j ≤ m :=
      pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hj
    have hpR : ((↑((2 : ℕ) ^ j) : ℝ)) ≤ (m : ℝ) := by exact_mod_cast hp
    have hmono : r ^ ((2 : ℕ) ^ j) ≤ r ^ m := by
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hr.le hpR
    exact hmono.trans_eq hrpow
  · simpa only [pow_zero, pow_one] using hr

variable [Nontrivial G]

/-- Explicit relative root bound on the genuine finite Wilson OS norm. -/
theorem p4Q2PZ37AQF_localDyadicRatioRoot
    (H k n : ℕ) (s : Set (PeriodicHypercubicEvenEdge H))
    (beta : ℝ) (hb : 0 ≤ beta)
    (u : Obs H)
    (hu : Supported H s (fun A => u ((P H).positiveRestriction A)))
    (hp : ∀ e ∈ s, periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.positive)
    (hbudget : ∀ e ∈ s, (e.1 0).val + (2 : ℕ) ^ n * k ≤ H)
    (hbase : 0 < ‖Read H beta hb u‖) :
    ‖Read H beta hb (Local H k u)‖ / ‖Read H beta hb u‖ ≤
      ((‖periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
        H 2 (by norm_num) beta hb‖ * ‖L2 H 2 u‖) / ‖Read H beta hb u‖) ^
        ((↑((2 : ℕ) ^ n) : ℝ)⁻¹) := by
  exact p4Q2PZ37AQF_powerRatioRoot _ _ _ _ (norm_nonneg _) hbase
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (pow_pos (by norm_num : 0 < (2 : ℕ)) n)
    (p4Q2PZ37AQE_localDyadicHaarBound H k n s beta hb u hu hp hbudget)

/-- A relative ceiling for the actual terminal OS norm suffices for a
linear bound at the original time step. -/
theorem p4Q2PZ37AQF_localDyadicTerminalThreshold
    (H k n : ℕ) (s : Set (PeriodicHypercubicEvenEdge H))
    (beta : ℝ) (hb : 0 ≤ beta)
    (u : Obs H)
    (hu : Supported H s (fun A => u ((P H).positiveRestriction A)))
    (hp : ∀ e ∈ s, periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.positive)
    (hbudget : ∀ e ∈ s, (e.1 0).val + (2 : ℕ) ^ n * k ≤ H)
    (c : ℝ) (hc : 0 ≤ c)
    (hterminal : ‖Read H beta hb (Local H ((2 : ℕ) ^ n * k) u)‖ ≤
      c ^ ((2 : ℕ) ^ n) * ‖Read H beta hb u‖) :
    ‖Read H beta hb (Local H k u)‖ ≤ c * ‖Read H beta hb u‖ := by
  exact p4Q2PZ37AQF_powerThreshold _ _ _ c _ (norm_nonneg _) (norm_nonneg _) hc
    (pow_pos (by norm_num : 0 < (2 : ℕ)) n)
    (p4Q2PZ37AQE_localDyadicPower H k n s beta hb u hu hp hbudget) hterminal

/-- The genuine Haar majorant is a sufficient, not necessary, threshold
certificate. It does not assume a global OS operator norm. -/
theorem p4Q2PZ37AQF_localDyadicHaarThreshold
    (H k n : ℕ) (s : Set (PeriodicHypercubicEvenEdge H))
    (beta : ℝ) (hb : 0 ≤ beta)
    (u : Obs H)
    (hu : Supported H s (fun A => u ((P H).positiveRestriction A)))
    (hp : ∀ e ∈ s, periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.positive)
    (hbudget : ∀ e ∈ s, (e.1 0).val + (2 : ℕ) ^ n * k ≤ H)
    (c : ℝ) (hc : 0 ≤ c)
    (hmajorant : (‖periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
        H 2 (by norm_num) beta hb‖ * ‖L2 H 2 u‖) ≤
      c ^ ((2 : ℕ) ^ n) * ‖Read H beta hb u‖) :
    ‖Read H beta hb (Local H k u)‖ ≤ c * ‖Read H beta hb u‖ := by
  exact p4Q2PZ37AQF_localDyadicTerminalThreshold H k n s beta hb u hu hp hbudget c hc
    ((p4Q2PZ37AQE_localTerminalBound H ((2 : ℕ) ^ n * k) s beta hb u hu hp hbudget).trans hmajorant)

/-- A genuine expansion beyond c forces the Haar budget to exceed the
dyadic relative threshold. No assertion that such expansion occurs. -/
theorem p4Q2PZ37AQF_localDyadicExpansionForcesHaarBudget
    (H k n : ℕ) (s : Set (PeriodicHypercubicEvenEdge H))
    (beta : ℝ) (hb : 0 ≤ beta)
    (u : Obs H)
    (hu : Supported H s (fun A => u ((P H).positiveRestriction A)))
    (hp : ∀ e ∈ s, periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.positive)
    (hbudget : ∀ e ∈ s, (e.1 0).val + (2 : ℕ) ^ n * k ≤ H)
    (c : ℝ) (hc : 0 ≤ c)
    (hexpand : c * ‖Read H beta hb u‖ < ‖Read H beta hb (Local H k u)‖) :
    c ^ ((2 : ℕ) ^ n) * ‖Read H beta hb u‖ <
      (‖periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
        H 2 (by norm_num) beta hb‖ * ‖L2 H 2 u‖) := by
  apply lt_of_not_ge
  intro hmajorant
  exact (not_le_of_gt hexpand)
    (p4Q2PZ37AQF_localDyadicHaarThreshold H k n s beta hb u hu hp hbudget c hc hmajorant)

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQF_powerRatio
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQF_powerRatioRoot
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQF_powerThreshold
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQF_finiteRecurrence_noContraction
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQF_localDyadicRatioRoot
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQF_localDyadicTerminalThreshold
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQF_localDyadicHaarThreshold
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQF_localDyadicExpansionForcesHaarBudget
