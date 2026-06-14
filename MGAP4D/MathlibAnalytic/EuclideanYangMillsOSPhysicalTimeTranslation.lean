import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalHilbertReconstructedModel
import MGAP4D.MathlibAnalytic.WightmanOSEuclideanTimeSemigroupLaplaceBridge

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Euclidean time translation reconstructed simultaneously on configurations,
positive-time observables, and the completed OS physical Hilbert space.

The equality on dense observable states prevents the Hilbert-space semigroup from
being an unrelated postulated operator family. -/
structure EuclideanYangMillsOSPhysicalTimeTranslation
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) where
  configurationTranslate :
    ℝ → S.measurePackage.configurationSpace →
      S.measurePackage.configurationSpace
  observableTranslate :
    ℝ → M.observables.PositiveTimeObservable →ₗ[ℝ]
      M.observables.PositiveTimeObservable
  realization_translate :
    ∀ (t : ℝ) (F : M.observables.PositiveTimeObservable)
      (ω : S.measurePackage.configurationSpace),
      M.observables.realization (observableTranslate t F) ω =
        M.observables.realization F (configurationTranslate t ω)
  positiveTimeSupported_preserved :
    ∀ (t : ℝ), 0 ≤ t → ∀ F,
      M.observables.positiveTimeSupported F →
        M.observables.positiveTimeSupported (observableTranslate t F)
  gaugeInvariant_preserved :
    ∀ (t : ℝ), 0 ≤ t → ∀ F,
      M.observables.gaugeInvariant F →
        M.observables.gaugeInvariant (observableTranslate t F)
  operator :
    ℝ → M.observables.PhysicalHilbert →L[ℝ]
      M.observables.PhysicalHilbert
  operator_on_dense_state :
    ∀ (t : ℝ) (F : M.observables.PositiveTimeObservable), 0 ≤ t →
      operator t (M.observables.physicalState F) =
        M.observables.physicalState (observableTranslate t F)
  zero_observable :
    ∀ F, observableTranslate 0 F = F
  add_observable :
    ∀ (s t : ℝ), 0 ≤ s → 0 ≤ t → ∀ F,
      observableTranslate (s + t) F =
        observableTranslate s (observableTranslate t F)
  zero_operator :
    ∀ ψ, operator 0 ψ = ψ
  add_operator :
    ∀ (s t : ℝ), 0 ≤ s → 0 ≤ t → ∀ ψ,
      operator (s + t) ψ = operator s (operator t ψ)
  vacuum_fixed :
    ∀ (t : ℝ), 0 ≤ t → operator t M.vacuum = M.vacuum
  contraction :
    ∀ (t : ℝ), 0 ≤ t → ∀ ψ, ‖operator t ψ‖ ≤ ‖ψ‖

/-- The reconstructed physical time translations supply the existing bounded
Euclidean semigroup interface on the explicit OS/Wightman model. -/
def EuclideanYangMillsOSPhysicalTimeTranslation.toEuclideanTimeSemigroup
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) :
    ExplicitWightmanOSEuclideanTimeSemigroup M.toExplicitModel :=
  { operator := T.operator
    zero_apply := T.zero_operator
    add_apply := T.add_operator
    vacuum_fixed := T.vacuum_fixed
    contraction := T.contraction }

/-- Time translation of an OS dense state is definitionally controlled by the
translated Euclidean observable. -/
theorem os_physical_time_translation_on_dense_state
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (t : ℝ) (ht : 0 ≤ t)
    (F : M.observables.PositiveTimeObservable) :
    T.operator t (M.observables.physicalState F) =
      M.observables.physicalState (T.observableTranslate t F) :=
  T.operator_on_dense_state t F ht

/-- OS-null-equivalent observables remain physically identical after nonnegative
time translation. -/
theorem os_physical_time_translation_respects_physical_equivalence
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (t : ℝ) (ht : 0 ≤ t)
    {F G : M.observables.PositiveTimeObservable}
    (hFG : M.observables.physicalState F =
      M.observables.physicalState G) :
    M.observables.physicalState (T.observableTranslate t F) =
      M.observables.physicalState (T.observableTranslate t G) := by
  rw [← T.operator_on_dense_state t F ht,
    ← T.operator_on_dense_state t G ht, hFG]

/-- The physical semigroup is contractive on the OS completion. -/
theorem os_physical_time_translation_contracts
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (t : ℝ) (ht : 0 ≤ t)
    (ψ : M.observables.PhysicalHilbert) :
    ‖T.operator t ψ‖ ≤ ‖ψ‖ :=
  T.contraction t ht ψ

/-- The OS vacuum, represented by the constant positive-time observable, is fixed
by the reconstructed Euclidean-time semigroup. -/
theorem os_physical_time_translation_fixes_vacuum
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (t : ℝ) (ht : 0 ≤ t) :
    T.operator t M.observables.vacuum = M.observables.vacuum := by
  rw [← M.vacuum_eq_os_vacuum]
  exact T.vacuum_fixed t ht

/-- Certificate joining the Euclidean and physical meanings of time translation. -/
structure EuclideanYangMillsOSPhysicalTimeTranslationCertificate
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) where
  semigroup : ExplicitWightmanOSEuclideanTimeSemigroup M.toExplicitModel
  denseStateCompatibility :
    ∀ (t : ℝ) (F : M.observables.PositiveTimeObservable), 0 ≤ t →
      T.operator t (M.observables.physicalState F) =
        M.observables.physicalState (T.observableTranslate t F)
  vacuumPreserved :
    ∀ (t : ℝ), 0 ≤ t →
      T.operator t M.observables.vacuum = M.observables.vacuum

/-- Construct the time-translation certificate. -/
def euclideanYangMillsOSPhysicalTimeTranslationCertificate
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) :
    EuclideanYangMillsOSPhysicalTimeTranslationCertificate T :=
  { semigroup := T.toEuclideanTimeSemigroup
    denseStateCompatibility := fun t F ht =>
      T.operator_on_dense_state t F ht
    vacuumPreserved := fun t ht =>
      os_physical_time_translation_fixes_vacuum T t ht }

end

end MathlibAnalytic
end MGAP4D
