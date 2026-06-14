import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalTimeTranslation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Generator identification for the reconstructed OS time-translation
semigroup.

The right derivative at time zero is `-H` on the displayed Hamiltonian domain.
This ties the unbounded self-adjoint Hamiltonian to Euclidean time translation
instead of allowing it to be an unrelated operator field. -/
structure EuclideanYangMillsOSPhysicalHamiltonianGenerator
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) where
  stronglyContinuousAtZero :
    ∀ ψ : M.observables.PhysicalHilbert,
      Tendsto (fun t : ℝ => T.operator t ψ)
        (nhdsWithin 0 (Set.Ici 0)) (nhds ψ)
  generatorLimit :
    ∀ x : M.hamiltonian.domain,
      Tendsto
        (fun t : ℝ =>
          t⁻¹ •
            (T.operator t (x : M.observables.PhysicalHilbert) -
              (x : M.observables.PhysicalHilbert)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (-(M.hamiltonian x)))

/-- Strong continuity at the semigroup origin. -/
theorem os_physical_time_translation_stronglyContinuousAtZero
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (ψ : M.observables.PhysicalHilbert) :
    Tendsto (fun t : ℝ => T.operator t ψ)
      (nhdsWithin 0 (Set.Ici 0)) (nhds ψ) :=
  G.stronglyContinuousAtZero ψ

/-- The reconstructed Hamiltonian is the negative right generator of the OS
Euclidean-time contraction semigroup. -/
theorem os_physical_hamiltonian_generator_limit
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (x : M.hamiltonian.domain) :
    Tendsto
      (fun t : ℝ =>
        t⁻¹ •
          (T.operator t (x : M.observables.PhysicalHilbert) -
            (x : M.observables.PhysicalHilbert)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-(M.hamiltonian x))) :=
  G.generatorLimit x

/-- The physical package now joins all three layers:
Euclidean observable translation, the contraction semigroup on the OS
completion, and its self-adjoint Hamiltonian generator. -/
structure EuclideanYangMillsOSPhysicalDynamicsCertificate
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T) where
  semigroup : ExplicitWightmanOSEuclideanTimeSemigroup M.toExplicitModel
  hamiltonianSelfAdjoint : IsSelfAdjoint M.hamiltonian
  strongContinuity :
    ∀ ψ : M.observables.PhysicalHilbert,
      Tendsto (fun t : ℝ => T.operator t ψ)
        (nhdsWithin 0 (Set.Ici 0)) (nhds ψ)
  generatorIdentification :
    ∀ x : M.hamiltonian.domain,
      Tendsto
        (fun t : ℝ =>
          t⁻¹ •
            (T.operator t (x : M.observables.PhysicalHilbert) -
              (x : M.observables.PhysicalHilbert)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (-(M.hamiltonian x)))

/-- Construct the physical-dynamics certificate. -/
def euclideanYangMillsOSPhysicalDynamicsCertificate
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T) :
    EuclideanYangMillsOSPhysicalDynamicsCertificate T G :=
  { semigroup := T.toEuclideanTimeSemigroup
    hamiltonianSelfAdjoint := M.hamiltonianSelfAdjoint
    strongContinuity := G.stronglyContinuousAtZero
    generatorIdentification := G.generatorLimit }

end

end MathlibAnalytic
end MGAP4D
