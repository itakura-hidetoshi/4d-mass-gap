import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalTimeTranslation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Compile the reconstructed Euclidean semigroup on the physical OS completion. -/
theorem euclidean_yang_mills_os_time_translation_compile_smoke
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) :
    ExplicitWightmanOSEuclideanTimeSemigroup M.toExplicitModel :=
  T.toEuclideanTimeSemigroup

/-- Compile the compatibility between translated Euclidean observables and their
dense physical states. -/
theorem euclidean_yang_mills_os_time_translation_dense_state_compile_smoke
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (t : ℝ) (ht : 0 ≤ t)
    (F : M.observables.PositiveTimeObservable) :
    T.operator t (M.observables.physicalState F) =
      M.observables.physicalState (T.observableTranslate t F) := by
  exact T.operator_on_dense_state t F ht

/-- Compile vacuum preservation and contractivity on the OS Hilbert completion. -/
theorem euclidean_yang_mills_os_time_translation_physical_compile_smoke
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (t : ℝ) (ht : 0 ≤ t)
    (ψ : M.observables.PhysicalHilbert) :
    T.operator t M.observables.vacuum = M.observables.vacuum ∧
      ‖T.operator t ψ‖ ≤ ‖ψ‖ := by
  exact ⟨os_physical_time_translation_fixes_vacuum T t ht,
    T.contraction t ht ψ⟩

end

end MathlibAnalytic
end MGAP4D
