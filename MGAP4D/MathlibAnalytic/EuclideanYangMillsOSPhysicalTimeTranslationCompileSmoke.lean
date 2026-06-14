import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalStrongContinuityCore

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Compile the lightweight physical semigroup without importing the downstream
spectral-Laplace bridge. -/
theorem euclidean_yang_mills_os_time_translation_compile_smoke
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslationCore M) :
    EuclideanYangMillsOSPhysicalSemigroup M :=
  T.toSemigroup

/-- Compile the compatibility between translated Euclidean observables and their
dense physical states. -/
theorem euclidean_yang_mills_os_time_translation_dense_state_compile_smoke
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslationCore M)
    (t : ℝ) (ht : 0 ≤ t)
    (F : M.observables.PositiveTimeObservable) :
    T.operator t (M.observables.physicalState F) =
      M.observables.physicalState (T.observableTranslate t F) := by
  exact T.operator_on_dense_state t F ht

/-- Compile vacuum preservation and contractivity on the OS Hilbert completion. -/
theorem euclidean_yang_mills_os_time_translation_physical_compile_smoke
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslationCore M)
    (t : ℝ) (ht : 0 ≤ t)
    (psi : M.observables.PhysicalHilbert) :
    T.operator t M.observables.vacuum = M.observables.vacuum ∧
      ‖T.operator t psi‖ ≤ ‖psi‖ := by
  rw [← M.vacuum_eq_os_vacuum]
  exact ⟨T.vacuum_fixed t ht, T.contraction t ht psi⟩

/-- Compile strong continuity and the right derivative equal to the negative
Hamiltonian action on its domain. -/
theorem euclidean_yang_mills_os_hamiltonian_generator_compile_smoke
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslationCore M}
    (G : EuclideanYangMillsOSPhysicalStrongContinuityCore T)
    (x : M.hamiltonian.domain) :
    Tendsto
      (fun t : ℝ =>
        t⁻¹ •
          (T.operator t (x : M.observables.PhysicalHilbert) -
            (x : M.observables.PhysicalHilbert)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-(M.hamiltonian x))) := by
  exact G.rightDerivativeLimit x

end

end MathlibAnalytic
end MGAP4D
