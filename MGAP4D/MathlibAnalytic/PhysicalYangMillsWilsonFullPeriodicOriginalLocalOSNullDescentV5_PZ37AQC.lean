import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicOriginalLocalHaarL2DescentV5_PZ37AQB
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenGibbsReflection
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AQC — actual finite Wilson reflection pairing and double-budget null descent
The true boundary synthesis is paired using the finite Gibbs reflection form.
Two equal supported forward displacements may be moved to one side of that
form when the cumulative support budget holds. This gives null preservation
on the double-budget domain, not an unrestricted half-time semigroup.
The APX/APY obstruction is kept unchanged.
-/
namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 100000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "O" => PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
local notation "P" => periodicHypercubicEvenEdgeOrbitPartition
local notation "L" => PeriodicHypercubicEvenSideLength
local notation "Tau" => periodicHypercubicIntegerTemporalConfigurationTranslation
local notation "Theta" => periodicHypercubicEvenConfigurationReflection
local notation "Section" => periodicHypercubicEvenSpecialUnitaryPositiveHalfSection
local notation "Supported" => p4Q2PZ37APZ_DependsOn
local notation "Local" => p4Q2PZ37AQB_localHalfObservable
local notation "L2" => periodicHypercubicEvenWilsonOpenHalfObservableL2
local notation "HalfMu" => periodicHypercubicEvenOpenHalfHaarMeasure
local notation "BoundaryMu" => periodicHypercubicEvenBoundaryHaarMeasure
local notation "W" => p4Q2PZ37APW_openTimeOneObservable
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure

local instance p4Q2PZ37AQC_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AQC_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AQC_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AQC_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AQC_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AQC_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37AQC_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37AQC_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37AQC_sliceFinite (H : ℕ) : SFinite (Mu H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37AQC_openHalfProbability (H : ℕ) :
    IsProbabilityMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance


local instance p4Q2PZ37AQC_boundaryProbability (H : ℕ) :
    IsProbabilityMeasure (BoundaryMu H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local notation "Gibbs" => periodicHypercubicSpecialUnitaryWilsonSystem

variable [Nontrivial G]

/-- The mixed actual finite Wilson reflection form. -/
def p4Q2PZ37AQC_reflectedPair (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (u v : BoundedContinuousFunction (O H 2) ℝ) : ℝ :=
  ∫ A, u ((P H).positiveRestriction A) *
    v ((P H).positiveRestriction (Theta H A))
    ∂(Gibbs (L H) 2 (by norm_num) beta hb).gibbsMeasure

local notation "Pair" => p4Q2PZ37AQC_reflectedPair

/-- Actual canonical synthesis of a bounded continuous half observable. -/
def p4Q2PZ37AQC_boundaryRead (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) :
    BoundedContinuousFunction (O H 2) ℝ →L[ℝ] Lp ℝ 2 (BoundaryMu H 2) :=
  (periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
    H 2 (by norm_num) beta hb).comp
    (BoundedContinuousFunction.toLp (E := ℝ) 2 (HalfMu H 2) ℝ)

local notation "Read" => p4Q2PZ37AQC_boundaryRead

/-- Mixed reflected observables are integrable for the true Gibbs probability. -/
theorem p4Q2PZ37AQC_reflectedPair_integrable
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (u v : BoundedContinuousFunction (O H 2) ℝ) :
    Integrable (fun A => u ((P H).positiveRestriction A) *
      v ((P H).positiveRestriction (Theta H A)))
      (Gibbs (L H) 2 (by norm_num) beta hb).gibbsMeasure := by
  have hr := (p4Q2PZ37AQB_positiveRestriction_measurePreserving H).measurable
  have ht := (periodicHypercubicSpecialUnitaryWilsonSystem_gibbs_reflection_measurePreserving
    H 2 (by norm_num) beta hb).measurable
  have hm : Measurable (fun A : PeriodicHypercubicEvenEdge H → G =>
      u ((P H).positiveRestriction A) * v ((P H).positiveRestriction (Theta H A))) :=
    (u.continuous.measurable.comp hr).mul
      (v.continuous.measurable.comp (hr.comp ht))
  let mu : Measure (PeriodicHypercubicEvenEdge H → G) :=
    (Gibbs (L H) 2 (by norm_num) beta hb).gibbsMeasure
  have hp : IsProbabilityMeasure mu :=
    periodicHypercubicSpecialUnitaryWilsonSystem_gibbsMeasure_probability
      (L H) 2 (by norm_num) beta hb
  letI : IsFiniteMeasure mu := ⟨by rw [hp.measure_univ]; exact ENNReal.one_lt_top⟩
  change Integrable (fun A => u ((P H).positiveRestriction A) *
    v ((P H).positiveRestriction (Theta H A))) mu
  apply Integrable.of_bound (μ := mu) hm.aestronglyMeasurable (‖u‖ * ‖v‖)
  filter_upwards [] with A
  rw [norm_mul]
  exact mul_le_mul (u.norm_coe_le_norm _) (v.norm_coe_le_norm _)
    (norm_nonneg _) (norm_nonneg _)

/-- Actual Gibbs reflection invariance gives symmetry of the mixed form. -/
theorem p4Q2PZ37AQC_reflectedPair_symm
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (u v : BoundedContinuousFunction (O H 2) ℝ) :
    Pair H beta hb u v = Pair H beta hb v u := by
  let F : (PeriodicHypercubicEvenEdge H → G) → ℝ :=
    fun A => u ((P H).positiveRestriction A) *
      v ((P H).positiveRestriction (Theta H A))
  let mu : Measure (PeriodicHypercubicEvenEdge H → G) :=
    (Gibbs (L H) 2 (by norm_num) beta hb).gibbsMeasure
  have hmp : MeasurePreserving (Theta H : (PeriodicHypercubicEvenEdge H → G) →
      (PeriodicHypercubicEvenEdge H → G)) mu mu :=
    periodicHypercubicSpecialUnitaryWilsonSystem_gibbs_reflection_measurePreserving
      H 2 (by norm_num) beta hb
  have hF : AEStronglyMeasurable F (Measure.map (Theta H) mu) := by
    rw [hmp.map_eq]
    exact (p4Q2PZ37AQC_reflectedPair_integrable H beta hb u v).aestronglyMeasurable
  have hm := MeasureTheory.integral_map hmp.measurable.aemeasurable hF
  rw [hmp.map_eq] at hm
  calc
    Pair H beta hb u v = ∫ A, F (Theta H A) ∂mu := hm
    _ = Pair H beta hb v u := by
      apply integral_congr_ae
      filter_upwards [] with A
      change u ((P H).positiveRestriction (Theta H A)) *
        v ((P H).positiveRestriction (Theta H (Theta H A))) =
        v ((P H).positiveRestriction A) * u ((P H).positiveRestriction (Theta H A))
      have hθ : Theta H (Theta H A) = A :=
        periodicHypercubicEvenConfigurationReflection_involutive (Gauge := G) H A
      calc
        _ = u ((P H).positiveRestriction (Theta H A)) * v ((P H).positiveRestriction A) :=
          congrArg (fun Z => u ((P H).positiveRestriction (Theta H A)) *
            v ((P H).positiveRestriction Z)) hθ
        _ = _ := mul_comm _ _

/-- The original diagonal reflection value is the squared actual synthesis norm. -/
theorem p4Q2PZ37AQC_reflectedPair_diagonal
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (u : BoundedContinuousFunction (O H 2) ℝ) :
    Pair H beta hb u u = ‖Read H beta hb u‖ ^ 2 := by
  let m := periodicHypercubicEvenBoundaryObservableMomentL2 H 2 (by norm_num) beta hb u
  have hs : m = Read H beta hb u :=
    periodicHypercubicEvenBoundaryObservableMomentL2_eq_synthesisOperator
      H 2 (by norm_num) beta hb u
  have hm : ‖m‖ ^ 2 = ∫ b,
      ‖periodicHypercubicEvenBoundaryObservableMoment H 2 (by norm_num) beta hb
        (fun x => u x) b‖ ^ 2 ∂(BoundaryMu H 2) := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [periodicHypercubicEvenBoundaryObservableMomentL2_coeFn
      H 2 (by norm_num) beta hb u] with b hmb
    change inner ℝ (m b) (m b) = _
    rw [show m b = periodicHypercubicEvenBoundaryObservableMoment
      H 2 (by norm_num) beta hb u b from hmb]
    exact real_inner_self_eq_norm_sq _
  change (∫ A, periodicHypercubicEvenFullReflectedObservable H (fun x => u x) A
    ∂(Gibbs (L H) 2 (by norm_num) beta hb).gibbsMeasure) = _
  rw [periodicHypercubicEvenWilsonGibbs_reflectedObservable_integral_eq_boundaryMoment_norm_sq
    H 2 (by norm_num) beta hb u
      (fun b => periodicHypercubicEvenBoundaryObservableGramFeature_integrable_of_boundedContinuous
        H 2 (by norm_num) beta hb u b)]
  rw [← hm, hs]

/-- Polarization identifies the genuine mixed Gibbs reflection form with the
inner product of the unchanged Wilson boundary synthesis. -/
theorem p4Q2PZ37AQC_reflectedPair_eq_inner
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (u v : BoundedContinuousFunction (O H 2) ℝ) :
    Pair H beta hb u v = inner ℝ (Read H beta hb u) (Read H beta hb v) := by
  let mu : Measure (PeriodicHypercubicEvenEdge H → G) :=
    (Gibbs (L H) 2 (by norm_num) beta hb).gibbsMeasure
  let F (a b : BoundedContinuousFunction (O H 2) ℝ)
      (A : PeriodicHypercubicEvenEdge H → G) : ℝ :=
    a ((P H).positiveRestriction A) * b ((P H).positiveRestriction (Theta H A))
  have hi (a b : BoundedContinuousFunction (O H 2) ℝ) : Integrable (F a b) mu :=
    p4Q2PZ37AQC_reflectedPair_integrable H beta hb a b
  have he : F (u + v) (u + v) = (F u u + F u v + F v u + F v v) := by
    funext A
    simp only [F, Pi.add_apply, BoundedContinuousFunction.add_apply]
    ring
  have ha : Pair H beta hb (u + v) (u + v) =
      ((Pair H beta hb u u + Pair H beta hb u v) + Pair H beta hb v u) +
        Pair H beta hb v v := by
    change (∫ A, F (u + v) (u + v) A ∂mu) =
      ((∫ A, F u u A ∂mu) + (∫ A, F u v A ∂mu) + (∫ A, F v u A ∂mu)) +
        (∫ A, F v v A ∂mu)
    rw [he]
    exact (integral_add (((hi u u).add (hi u v)).add (hi v u)) (hi v v)).trans
      (congrArg (fun z => z + (∫ A, F v v A ∂mu))
        ((integral_add ((hi u u).add (hi u v)) (hi v u)).trans
          (congrArg (fun z => z + (∫ A, F v u A ∂mu))
            (integral_add (hi u u) (hi u v)))))
  have hd := p4Q2PZ37AQC_reflectedPair_diagonal H beta hb (u + v)
  rw [ha, map_add, norm_add_sq_real,
    ← p4Q2PZ37AQC_reflectedPair_diagonal H beta hb u,
    ← p4Q2PZ37AQC_reflectedPair_diagonal H beta hb v,
    p4Q2PZ37AQC_reflectedPair_symm H beta hb v u] at hd
  linarith

/-- The shifted quadratic value equals the mixed value with a doubled
displacement, whenever both displacements fit the original edge support. -/
theorem p4Q2PZ37AQC_local_doubleBudget_pair
    (H k : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (s : Set (PeriodicHypercubicEvenEdge H))
    (u : BoundedContinuousFunction (O H 2) ℝ)
    (hu : Supported H s (fun A => u ((P H).positiveRestriction A)))
    (hp : ∀ e ∈ s, periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.positive)
    (hkk : ∀ e ∈ s, (e.1 0).val + k + k ≤ H) :
    Pair H beta hb (Local H k u) (Local H k u) =
      Pair H beta hb u (Local H (k + k) u) := by
  have hk : ∀ e ∈ s, (e.1 0).val + k ≤ H := by
    intro e he
    have hh := hkk e he
    omega
  have hk2 : ∀ e ∈ s, (e.1 0).val + (k + k) ≤ H := by
    intro e he
    have hh := hkk e he
    omega
  have hpt (j : ℕ) (hj : ∀ e ∈ s, (e.1 0).val + j ≤ H)
      (A : PeriodicHypercubicEvenEdge H → G) :
      Local H j u ((P H).positiveRestriction A) =
        u ((P H).positiveRestriction (Tau (L H) (-(j : ℤ)) A)) := by
    change u ((P H).positiveRestriction
      (Tau (L H) (-(j : ℤ)) (Section H 2 ((P H).positiveRestriction A)))) = _
    exact (p4Q2PZ37APZ_dependsOn_shift_factor_of_budget H j s
      (fun Z => u ((P H).positiveRestriction Z)) hu hp hj A).symm
  let mu : Measure (PeriodicHypercubicEvenEdge H → G) :=
    (Gibbs (L H) 2 (by norm_num) beta hb).gibbsMeasure
  let F : (PeriodicHypercubicEvenEdge H → G) → ℝ :=
    fun A => u ((P H).positiveRestriction A) *
      Local H (k + k) u ((P H).positiveRestriction (Theta H A))
  let t := periodicHypercubicIntegerTemporalConfigurationTranslation
    (Gauge := G) (L H) (-(k : ℤ))
  have hmp := periodicHypercubicSpecialUnitary_gibbs_measurePreserving_integerTemporalTranslation
    (L H) 2 (by norm_num) beta hb (-(k : ℤ))
  have hsum : -((k + k : ℕ) : ℤ) + (k : ℤ) = -(k : ℤ) := by omega
  calc
    Pair H beta hb (Local H k u) (Local H k u) = ∫ A, F (t A) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with A
      change Local H k u ((P H).positiveRestriction A) *
        Local H k u ((P H).positiveRestriction (Theta H A)) =
        u ((P H).positiveRestriction (Tau (L H) (-(k : ℤ)) A)) *
        Local H (k + k) u ((P H).positiveRestriction
          (Theta H (Tau (L H) (-(k : ℤ)) A)))
      rw [hpt k hk A, hpt k hk (Theta H A), hpt (k + k) hk2]
      have hc : Theta H (Tau (L H) (-(k : ℤ)) A) =
          Tau (L H) (k : ℤ) (Theta H A) := by
        simpa only [neg_neg] using
          (periodicHypercubicEvenConfigurationReflection_integerTemporalTranslation
            (Gauge := G) H (-(k : ℤ)) A)
      have hd : Tau (L H) (-((k + k : ℕ) : ℤ))
          (Tau (L H) (k : ℤ) (Theta H A)) =
          Tau (L H) (-(k : ℤ)) (Theta H A) := by
        calc
          _ = Tau (L H) (-((k + k : ℕ) : ℤ) + (k : ℤ)) (Theta H A) :=
            (periodicHypercubicIntegerTemporalConfigurationTranslation_add_apply
              (L H) (-((k + k : ℕ) : ℤ)) (k : ℤ) (Theta H A)).symm
          _ = _ := by rw [hsum]
      have heq : Tau (L H) (-((k + k : ℕ) : ℤ))
          (Theta H (Tau (L H) (-(k : ℤ)) A)) =
          Tau (L H) (-(k : ℤ)) (Theta H A) :=
        (congrArg (fun Z => Tau (L H) (-((k + k : ℕ) : ℤ)) Z) hc).trans hd
      exact congrArg (fun Z => u ((P H).positiveRestriction (Tau (L H) (-(k : ℤ)) A)) *
        u ((P H).positiveRestriction Z)) heq.symm
    _ = Pair H beta hb u (Local H (k + k) u) :=
      hmp.integral_comp t.measurableEmbedding F

/-- Exact double-budget OS norm identity. The actual boundary synthesis has
not been replaced with an abstract transport operator. -/
theorem p4Q2PZ37AQC_local_doubleBudget_norm_sq
    (H k : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (s : Set (PeriodicHypercubicEvenEdge H))
    (u : BoundedContinuousFunction (O H 2) ℝ)
    (hu : Supported H s (fun A => u ((P H).positiveRestriction A)))
    (hp : ∀ e ∈ s, periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.positive)
    (hkk : ∀ e ∈ s, (e.1 0).val + k + k ≤ H) :
    ‖Read H beta hb (Local H k u)‖ ^ 2 =
      inner ℝ (Read H beta hb u) (Read H beta hb (Local H (k + k) u)) := by
  rw [← p4Q2PZ37AQC_reflectedPair_diagonal H beta hb (Local H k u),
    p4Q2PZ37AQC_local_doubleBudget_pair H k beta hb s u hu hp hkk,
    p4Q2PZ37AQC_reflectedPair_eq_inner]

/-- The genuine Wilson OS null space is preserved on the double-budget domain. -/
theorem p4Q2PZ37AQC_local_null_of_doubleBudget
    (H k : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (s : Set (PeriodicHypercubicEvenEdge H))
    (u : BoundedContinuousFunction (O H 2) ℝ)
    (hu : Supported H s (fun A => u ((P H).positiveRestriction A)))
    (hp : ∀ e ∈ s, periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.positive)
    (hkk : ∀ e ∈ s, (e.1 0).val + k + k ≤ H)
    (hz : Read H beta hb u = 0) :
    Read H beta hb (Local H k u) = 0 := by
  have he := p4Q2PZ37AQC_local_doubleBudget_norm_sq H k beta hb s u hu hp hkk
  rw [hz, inner_zero_left] at he
  apply norm_eq_zero.mp
  nlinarith

/-- Equality in the true Wilson boundary carrier is preserved for two
representatives with a common double-budget support. -/
theorem p4Q2PZ37AQC_local_congr_of_doubleBudget
    (H k : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (s : Set (PeriodicHypercubicEvenEdge H))
    (u v : BoundedContinuousFunction (O H 2) ℝ)
    (hu : Supported H s (fun A => u ((P H).positiveRestriction A)))
    (hv : Supported H s (fun A => v ((P H).positiveRestriction A)))
    (hp : ∀ e ∈ s, periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.positive)
    (hkk : ∀ e ∈ s, (e.1 0).val + k + k ≤ H)
    (he : Read H beta hb u = Read H beta hb v) :
    Read H beta hb (Local H k u) = Read H beta hb (Local H k v) := by
  have hs : Supported H s (fun A => (u - v) ((P H).positiveRestriction A)) := by
    intro A B hAB
    simp only [BoundedContinuousFunction.sub_apply, hu A B hAB, hv A B hAB]
  have hz : Read H beta hb (u - v) = 0 := by
    rw [map_sub, he, sub_self]
  have hloc : Local H k (u - v) = Local H k u - Local H k v := by
    ext x
    rfl
  have hh := p4Q2PZ37AQC_local_null_of_doubleBudget H k beta hb s (u - v) hs hp hkk hz
  rw [hloc, map_sub] at hh
  exact sub_eq_zero.mp hh

/-- The literal time-one insertion obeys the same double-budget identity. -/
theorem p4Q2PZ37AQC_timeOne_doubleBudget_norm_sq
    (H k : ℕ) (hH : 0 < H) (hkk : 1 + k + k ≤ H)
    (beta : ℝ) (hb : 0 ≤ beta) (c0 c1 : ℝ) :
    ‖Read H beta hb (Local H k (W H hH c0 c1))‖ ^ 2 =
      inner ℝ (Read H beta hb (W H hH c0 c1))
        (Read H beta hb (Local H (k + k) (W H hH c0 c1))) := by
  apply p4Q2PZ37AQC_local_doubleBudget_norm_sq H k beta hb
    (p4Q2PZ37APZ_timeOneEdgeSupport H hH) (W H hH c0 c1)
    (p4Q2PZ37APZ_timeOneFullObservable_dependsOn H hH c0 c1)
  · rintro e ⟨a, rfl⟩
    exact periodicHypercubicEvenPositiveHalfInteriorSpatialEdge_positive H (⟨0, hH⟩, a)
  · rintro e ⟨a, rfl⟩
    change ((periodicHypercubicEvenPositiveHalfInteriorSpatialEdge H
      (⟨0, hH⟩, a)).1 0).val + k + k ≤ H
    rw [periodicHypercubicEvenPositiveHalfInteriorSpatialEdge_time_val]
    exact hkk

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQC_reflectedPair
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQC_boundaryRead
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQC_reflectedPair_integrable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQC_reflectedPair_symm
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQC_reflectedPair_diagonal
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQC_reflectedPair_eq_inner
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQC_local_doubleBudget_pair
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQC_local_doubleBudget_norm_sq
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQC_local_null_of_doubleBudget
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQC_local_congr_of_doubleBudget
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQC_timeOne_doubleBudget_norm_sq
