import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUniformCoefficientRelativeQuadraticV5_PZ37AQU
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AQV — volume-uniform weighted probe upper bound
Keep the literal APL observable, vacuum and AQO partition normalization.
A fixed compact SU(2) bound controls all volumes and couplings. Combine it
with AQU and AQO; the partition factor remains an explicit obligation.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 50000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "Hol" => p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy
local notation "Mode" => specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode
local notation "Obs" => p4Q2PZ37APL_originalTwoModeObservable
local notation "W" => p4Q2PZ37APL_originalVacuumWeightedTwoMode
local notation "VacC" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
local notation "Tr" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
local notation "NormZ" => periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
local notation "qC" => p4Q2PZ37AQO_centerCoefficient
local notation "J" => p4Q2PZ37AQO_testAmplitude
local notation "U" => p4Q2PZ37APP_originalTimeOneOSCenteredBoundaryL2

local instance p4Q2PZ37AQV_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AQV_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AQV_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AQV_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AQV_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AQV_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37AQV_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37AQV_probability (H : ℕ) : IsProbabilityMeasure (Mu H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37AQV_nontrivial : Nontrivial G := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun g : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem p4Q2PZ37AQV_scalar_sq (q x y : ℝ) :
    (q*x+y)^2 ≤ (1+q^2)*(x^2+y^2) := by
  nlinarith only [sq_nonneg (x-q*y)]

private theorem p4Q2PZ37AQV_apply_sq {α : Type*} [TopologicalSpace α]
    (f : BoundedContinuousFunction α ℝ) (x : α) : (f x)^2 ≤ ‖f‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (f x)) (f.norm_coe_le_norm x) 2
  simpa only [Real.norm_eq_abs, sq_abs] using h

/-- The two fixed continuous SU(2) modes give one bound for every holonomy. -/
theorem p4Q2PZ37AQV_observableSq_upper :
    ∃ M : ℝ, 0 < M ∧ ∀ (H : ℕ) (q : ℝ) (A : Cfg H 2),
      (Obs H q A)^2 ≤ M*(1+q^2) := by
  let f0 : BoundedContinuousFunction G ℝ := BoundedContinuousFunction.mkOfCompact (Mode 0)
  let f1 : BoundedContinuousFunction G ℝ := BoundedContinuousFunction.mkOfCompact (Mode 1)
  let M : ℝ := ‖f0‖^2 + ‖f1‖^2 + 1
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro H q A
  let g : G := Hol H 2 A
  have h0 : (Mode 0 g)^2 ≤ ‖f0‖^2 := p4Q2PZ37AQV_apply_sq f0 g
  have h1 : (Mode 1 g)^2 ≤ ‖f1‖^2 := p4Q2PZ37AQV_apply_sq f1 g
  change (q*Mode 0 g + 1*Mode 1 g)^2 ≤ M*(1+q^2)
  rw [one_mul]
  calc
    _ ≤ (1+q^2)*((Mode 0 g)^2+(Mode 1 g)^2) :=
      p4Q2PZ37AQV_scalar_sq q _ _
    _ ≤ (1+q^2)*(‖f0‖^2+‖f1‖^2) :=
      mul_le_mul_of_nonneg_left (add_le_add h0 h1) (by positivity)
    _ ≤ M*(1+q^2) := by
      rw [mul_comm (1+q^2)]
      apply mul_le_mul_of_nonneg_right
      · dsimp [M]; linarith
      · positivity

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQV_observableSq_upper

/-- The actual vacuum-weighted probe has a squared norm bound uniform
in volume, coefficient and even nonnegative coupling. -/
theorem p4Q2PZ37AQV_weightedNormSq_upper :
    ∃ M : ℝ, 0 < M ∧ ∀ (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) (q : ℝ),
      ‖W H beta hb q‖^2 ≤ M*(1+q^2) := by
  obtain ⟨M,hM,hbound⟩ := p4Q2PZ37AQV_observableSq_upper
  refine ⟨M,hM,?_⟩
  intro H beta hb q
  let mu := Mu H 2
  let a := Obs H q
  let o := VacC H 2 (by norm_num) beta hb
  have ho : Continuous o :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H 2 (by norm_num) beta hb
  have hI : Integrable (fun A : Cfg H 2 => (a A * o A)^2) mu :=
    ((a.continuous.mul ho).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hB : Integrable (fun A : Cfg H 2 => (M*(1+q^2))*(o A)^2) mu :=
    ((ho.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _
  have hle (A : Cfg H 2) : (a A * o A)^2 ≤ (M*(1+q^2))*(o A)^2 := by
    calc
      _ = (a A)^2*(o A)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound H q A) (sq_nonneg _)
  rw [p4Q2PZ37AQP_weightedNormSq_eq_integral]
  change (∫ A : Cfg H 2, (a A * o A)^2 ∂mu) ≤ _
  calc
    _ ≤ ∫ A : Cfg H 2, (M*(1+q^2))*(o A)^2 ∂mu := integral_mono hI hB hle
    _ = _ := by
      rw [integral_const_mul, show (∫ A : Cfg H 2, (o A)^2 ∂mu) = 1 from
        p4Q2PZ37AQP_vacuumSq_integral H beta hb, mul_one]

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQV_weightedNormSq_upper

private theorem p4Q2PZ37AQV_scalar_normalized_floor
    (p c M m n j : ℝ) (hp : 0 ≤ p) (hc : 0 < c) (hM : 0 < M)
    (hm : 1 ≤ m) (hn : 0 < n) (hN : n^2 ≤ M*m)
    (hj : p*(c*m) ≤ j) : (c/Real.sqrt M)*p ≤ j/n := by
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hm0 : 0 ≤ m := by linarith
  have hm2 : m ≤ m^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hm) hm0]
  have hr : 0 ≤ Real.sqrt M*m := mul_nonneg hs.le hm0
  have hsq : n^2 ≤ (Real.sqrt M*m)^2 := by
    calc
      _ ≤ M*m := hN
      _ ≤ M*m^2 := mul_le_mul_of_nonneg_left hm2 hM.le
      _ = _ := by rw [mul_pow, Real.sq_sqrt hM.le]
  have hn' : n ≤ Real.sqrt M*m := by
    by_contra! h
    have hpos : 0 < n - Real.sqrt M*m := sub_pos.mpr h
    have hsum : 0 < n + Real.sqrt M*m := add_pos_of_pos_of_nonneg hn hr
    nlinarith only [hsq, mul_pos hpos hsum]
  apply (le_div_iff₀ hn).2
  calc
    _ ≤ (c/Real.sqrt M*p)*(Real.sqrt M*m) :=
      mul_le_mul_of_nonneg_left hn' (mul_nonneg (div_nonneg hc.le hs.le) hp)
    _ = (c/Real.sqrt M*Real.sqrt M)*(p*m) := by ring
    _ = p*(c*m) := by rw [div_mul_cancel₀ _ hs.ne']; ring
    _ ≤ _ := hj

/-- Normalize the actual centered endpoint test. Keep the literal
partition factor, rather than substituting an eigenvalue for it. -/
theorem p4Q2PZ37AQV_centered_normalizedTest_scaled_floor
    (beta : ℝ) (hb : 0 < beta) :
    ∃ d : ℝ, 0 < d ∧ ∀ H : ℕ,
      d*(NormZ H 2 (by norm_num) beta hb.le * ‖Tr H 2 (by norm_num) beta hb.le‖^(H+1)) ≤
        J H beta hb.le / ‖W H beta hb.le (qC H beta hb.le)‖ := by
  obtain ⟨M,hM,hN⟩ := p4Q2PZ37AQV_weightedNormSq_upper
  obtain ⟨c,hc,hJ⟩ := p4Q2PZ37AQU_centered_testAmplitude_scaled_floor beta hb
  refine ⟨c/Real.sqrt M,div_pos hc (Real.sqrt_pos.2 hM),?_⟩
  intro H
  let p : ℝ := NormZ H 2 (by norm_num) beta hb.le * ‖Tr H 2 (by norm_num) beta hb.le‖^(H+1)
  have hz : 0 ≤ NormZ H 2 (by norm_num) beta hb.le := by
    unfold periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
    exact Real.sqrt_nonneg _
  have hp : 0 ≤ p := mul_nonneg hz (pow_nonneg (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H 2 (by norm_num) beta hb.le).le (H+1))
  let q := qC H beta hb.le
  let n := ‖W H beta hb.le q‖
  exact p4Q2PZ37AQV_scalar_normalized_floor p c M (1+q^2) n (J H beta hb.le)
    hp hc hM (by nlinarith [sq_nonneg q])
    (p4Q2PZ37AQO_weightedTest_norm_pos H beta hb)
    (hN H beta hb.le q) (hJ H)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQV_centered_normalizedTest_scaled_floor

/-- The actual centered OS boundary norm retains the same unresolved
partition factor, now with no volume-dependent probe denominator. -/
theorem p4Q2PZ37AQV_centeredOS_normSq_scaled_floor
    (beta : ℝ) (hb : 0 < beta) :
    ∃ d : ℝ, 0 < d ∧ ∀ H : ℕ,
      (d*(NormZ H 2 (by norm_num) beta hb.le * ‖Tr H 2 (by norm_num) beta hb.le‖^(H+1)))^2 ≤
        ‖U H beta hb.le‖^2 := by
  obtain ⟨d,hd,hD⟩ := p4Q2PZ37AQV_centered_normalizedTest_scaled_floor beta hb
  refine ⟨d,hd,?_⟩
  intro H
  have hz : 0 ≤ NormZ H 2 (by norm_num) beta hb.le := by
    unfold periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
    exact Real.sqrt_nonneg _
  have hp : 0 ≤ d*(NormZ H 2 (by norm_num) beta hb.le * ‖Tr H 2 (by norm_num) beta hb.le‖^(H+1)) :=
    mul_nonneg hd.le (mul_nonneg hz (pow_nonneg (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H 2 (by norm_num) beta hb.le).le (H+1)))
  exact (pow_le_pow_left₀ hp (hD H) 2).trans
    (p4Q2PZ37AQO_centeredOS_normSq_lower H beta hb)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQV_centeredOS_normSq_scaled_floor

end
end MGAP4D.MathlibAnalytic
