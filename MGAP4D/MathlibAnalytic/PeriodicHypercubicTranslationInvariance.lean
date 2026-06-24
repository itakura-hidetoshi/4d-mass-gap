import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonGaugeInvariance
import MGAP4D.MathlibAnalytic.SpecialUnitaryBorelReceipts
import Mathlib.MeasureTheory.Constructions.Pi

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
open MeasureTheory

noncomputable section

local instance specialUnitaryTranslationIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance specialUnitaryTranslationCompactSpace (N : ℕ) :
    CompactSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupCompactSpace N

local instance specialUnitaryTranslationSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupSecondCountableTopology N

local instance specialUnitaryTranslationMeasurableSpace (N : ℕ) :
    MeasurableSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupMeasurableSpace N

local instance specialUnitaryTranslationBorelSpace (N : ℕ) :
    BorelSpace (SpecialUnitaryMatrixGroup N) :=
  specialUnitaryGroupBorelSpace N

/-- Translation of periodic vertices by a fixed displacement. -/
def periodicHypercubicVertexTranslationEquiv
    (n : ℕ) (a : PeriodicHypercubicVertex n) :
    PeriodicHypercubicVertex n ≃ PeriodicHypercubicVertex n where
  toFun x := x + a
  invFun x := x - a
  left_inv x := by
    ext i
    simp
  right_inv x := by
    ext i
    simp

@[simp]
theorem periodicHypercubicVertexTranslationEquiv_apply
    (n : ℕ) (a x : PeriodicHypercubicVertex n) :
    periodicHypercubicVertexTranslationEquiv n a x = x + a :=
  rfl

@[simp]
theorem periodicHypercubicVertexTranslationEquiv_symm_apply
    (n : ℕ) (a x : PeriodicHypercubicVertex n) :
    (periodicHypercubicVertexTranslationEquiv n a).symm x = x - a :=
  rfl

/-- Translation of physical positive links by translating their source vertex. -/
def periodicHypercubicEdgeTranslationEquiv
    (n : ℕ) (a : PeriodicHypercubicVertex n) :
    PeriodicHypercubicEdge n ≃ PeriodicHypercubicEdge n where
  toFun e := (e.1 + a, e.2)
  invFun e := (e.1 - a, e.2)
  left_inv e := by
    cases e
    simp
  right_inv e := by
    cases e
    simp

@[simp]
theorem periodicHypercubicEdgeTranslationEquiv_apply
    (n : ℕ) (a : PeriodicHypercubicVertex n)
    (e : PeriodicHypercubicEdge n) :
    periodicHypercubicEdgeTranslationEquiv n a e = (e.1 + a, e.2) :=
  rfl

@[simp]
theorem periodicHypercubicEdgeTranslationEquiv_symm_apply
    (n : ℕ) (a : PeriodicHypercubicVertex n)
    (e : PeriodicHypercubicEdge n) :
    (periodicHypercubicEdgeTranslationEquiv n a).symm e =
      (e.1 - a, e.2) :=
  rfl

/-- Translation of periodic plaquettes by translating their base vertex. -/
def periodicHypercubicPlaquetteTranslationEquiv
    (n : ℕ) (a : PeriodicHypercubicVertex n) :
    PeriodicHypercubicPlaquette n ≃ PeriodicHypercubicPlaquette n where
  toFun p := (p.1 + a, p.2)
  invFun p := (p.1 - a, p.2)
  left_inv p := by
    cases p
    simp
  right_inv p := by
    cases p
    simp

@[simp]
theorem periodicHypercubicPlaquetteTranslationEquiv_apply
    (n : ℕ) (a : PeriodicHypercubicVertex n)
    (p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteTranslationEquiv n a p = (p.1 + a, p.2) :=
  rfl

/-- Translation of a signed boundary incidence. -/
def periodicHypercubicBoundaryStepTranslate
    {n : ℕ} (a : PeriodicHypercubicVertex n)
    (s : PeriodicHypercubicBoundaryStep n) :
    PeriodicHypercubicBoundaryStep n :=
  ⟨periodicHypercubicEdgeTranslationEquiv n a s.edge, s.orientation⟩

/-- Lattice shifts commute with an arbitrary periodic displacement. -/
theorem periodicHypercubicShift_add
    (n : ℕ) (x a : PeriodicHypercubicVertex n)
    (mu : PeriodicHypercubicAxis) :
    periodicHypercubicShift n (x + a) mu =
      periodicHypercubicShift n x mu + a := by
  unfold periodicHypercubicShift
  abel

/-- Translating a plaquette translates each of its signed boundary incidences. -/
theorem periodicHypercubicBoundaryStep_translation
    (n : ℕ) (a : PeriodicHypercubicVertex n)
    (p : PeriodicHypercubicPlaquette n) (k : Fin 4) :
    periodicHypercubicBoundaryStep n
        (periodicHypercubicPlaquetteTranslationEquiv n a p) k =
      periodicHypercubicBoundaryStepTranslate a
        (periodicHypercubicBoundaryStep n p k) := by
  fin_cases k <;>
    simp [periodicHypercubicBoundaryStepTranslate,
      periodicHypercubicPlaquetteFirstAxis,
      periodicHypercubicPlaquetteSecondAxis,
      periodicHypercubicShift_add]

/-- Coordinate reindexing of physical-link configurations induced by periodic
translation. -/
noncomputable def periodicHypercubicConfigurationTranslationMeasurableEquiv
    {Gauge : Type} [MeasurableSpace Gauge]
    (n : ℕ) (a : PeriodicHypercubicVertex n) :
    (PeriodicHypercubicEdge n → Gauge) ≃ᵐ
      (PeriodicHypercubicEdge n → Gauge) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : PeriodicHypercubicEdge n => Gauge)
    (periodicHypercubicEdgeTranslationEquiv n a)

@[simp]
theorem periodicHypercubicConfigurationTranslation_apply_translatedEdge
    {Gauge : Type} [MeasurableSpace Gauge]
    (n : ℕ) (a : PeriodicHypercubicVertex n)
    (A : PeriodicHypercubicEdge n → Gauge)
    (e : PeriodicHypercubicEdge n) :
    periodicHypercubicConfigurationTranslationMeasurableEquiv n a A
        (periodicHypercubicEdgeTranslationEquiv n a e) =
      A e := by
  simpa [periodicHypercubicConfigurationTranslationMeasurableEquiv] using
    (Equiv.piCongrLeft_apply_apply
      (fun _ : PeriodicHypercubicEdge n => Gauge)
      (periodicHypercubicEdgeTranslationEquiv n a) A e)

/-- Signed boundary values are unchanged after simultaneous translation of the
configuration and boundary incidence. -/
theorem periodicHypercubicStepValue_configurationTranslation
    {n : ℕ} {Gauge : Type} [Group Gauge] [MeasurableSpace Gauge]
    (a : PeriodicHypercubicVertex n)
    (A : PeriodicHypercubicEdge n → Gauge)
    (s : PeriodicHypercubicBoundaryStep n) :
    periodicHypercubicStepValue
        (periodicHypercubicConfigurationTranslationMeasurableEquiv n a A)
        (periodicHypercubicBoundaryStepTranslate a s) =
      periodicHypercubicStepValue A s := by
  cases s with
  | mk edge orientation =>
      cases orientation <;>
        simp [periodicHypercubicBoundaryStepTranslate,
          periodicHypercubicStepValue]

/-- Periodic plaquette holonomy is covariant under simultaneous translation of
configuration and plaquette. -/
theorem periodicHypercubicPlaquetteHolonomy_configurationTranslation
    {n : ℕ} {Gauge : Type} [Group Gauge] [MeasurableSpace Gauge]
    (a : PeriodicHypercubicVertex n)
    (A : PeriodicHypercubicEdge n → Gauge)
    (p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicConfigurationTranslationMeasurableEquiv n a A)
        (periodicHypercubicPlaquetteTranslationEquiv n a p) =
      periodicHypercubicPlaquetteHolonomy A p := by
  unfold periodicHypercubicPlaquetteHolonomy
  rw [periodicHypercubicBoundaryStep_translation,
    periodicHypercubicBoundaryStep_translation,
    periodicHypercubicBoundaryStep_translation,
    periodicHypercubicBoundaryStep_translation]
  simp only [periodicHypercubicStepValue_configurationTranslation]

/-- The canonical periodic `SU(N)` Wilson action is invariant under every
periodic lattice displacement. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction_translation
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (beta_nonneg : 0 ≤ beta)
    (a : PeriodicHypercubicVertex n)
    (A : PeriodicHypercubicEdge n →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.wilsonAction
      (periodicHypercubicConfigurationTranslationMeasurableEquiv n a A) =
    (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.wilsonAction A := by
  rw [periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction,
    periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction]
  refine Fintype.sum_equiv
    (periodicHypercubicPlaquetteTranslationEquiv n a).symm _ _ ?_
  intro p
  simpa using
    periodicHypercubicPlaquetteHolonomy_configurationTranslation
      a A ((periodicHypercubicPlaquetteTranslationEquiv n a).symm p)

/-- Product normalized Haar measure on physical links is invariant under periodic
coordinate translation. -/
theorem periodicHypercubicSpecialUnitary_configurationHaar_map_translation_eq_self
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (beta_nonneg : 0 ≤ beta)
    (a : PeriodicHypercubicVertex n) :
    Measure.map
        (periodicHypercubicConfigurationTranslationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) n a)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).base.configurationHaarMeasure =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.configurationHaarMeasure := by
  unfold CompactOrientedGaugeWilsonSystem.configurationHaarMeasure
  simpa using
    (Measure.pi_map_piCongrLeft
      (periodicHypercubicEdgeTranslationEquiv n a)
      (fun _ : PeriodicHypercubicEdge n =>
        normalizedCompactHaar
          (Matrix.specialUnitaryGroup (Fin N) ℂ)))

/-- The periodic coordinate translation preserves product normalized Haar
probability measure. -/
theorem periodicHypercubicSpecialUnitary_configurationHaar_measurePreserving_translation
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (beta_nonneg : 0 ≤ beta)
    (a : PeriodicHypercubicVertex n) :
    MeasurePreserving
      (periodicHypercubicConfigurationTranslationMeasurableEquiv
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) n a)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.configurationHaarMeasure
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.configurationHaarMeasure :=
  ⟨(periodicHypercubicConfigurationTranslationMeasurableEquiv
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) n a).measurable,
    periodicHypercubicSpecialUnitary_configurationHaar_map_translation_eq_self
      n N hN beta beta_nonneg a⟩

/-- The canonical finite-volume periodic `SU(N)` Wilson Gibbs probability law is
invariant under every periodic lattice displacement. -/
theorem periodicHypercubicSpecialUnitary_gibbs_measurePreserving_translation
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (beta_nonneg : 0 ≤ beta)
    (a : PeriodicHypercubicVertex n) :
    MeasurePreserving
      (periodicHypercubicConfigurationTranslationMeasurableEquiv
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) n a)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsMeasure
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsMeasure := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeasure
  apply measurePreserving_tilted_of_invariant
  · exact
      periodicHypercubicSpecialUnitary_configurationHaar_measurePreserving_translation
        n N hN beta beta_nonneg a
  · exact
      (continuous_compact_oriented_gibbsExponent
        (periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg)).measurable
  · intro A
    unfold CompactOrientedGaugeWilsonSystem.gibbsExponent
    rw [periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction_translation]
  · exact
      continuous_compact_oriented_boltzmannIntegrable
        (periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg)

/-- Pushforward form of finite-volume periodic translation invariance. -/
theorem periodicHypercubicSpecialUnitary_gibbs_map_translation_eq_self
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (beta_nonneg : 0 ≤ beta)
    (a : PeriodicHypercubicVertex n) :
    Measure.map
      (periodicHypercubicConfigurationTranslationMeasurableEquiv
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) n a)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsMeasure =
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).gibbsMeasure :=
  (periodicHypercubicSpecialUnitary_gibbs_measurePreserving_translation
    n N hN beta beta_nonneg a).map_eq

end

end MathlibAnalytic
end MGAP4D
