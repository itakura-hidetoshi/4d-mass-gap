import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalHamiltonianGenerator
import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalExactGapRealResolvent

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Compact endpoint in which the Hamiltonian carrying the exact-gap real
resolvent is simultaneously identified as the negative right generator of the
reconstructed Euclidean-time contraction semigroup. -/
abbrev EuclideanYangMillsOSPhysicalGeneratorExactGapRealResolventProp
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M.toExplicitModel)
    (hRelGap :
      HasRelativisticMassGap M.energyMomentumSpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum)
    (hRayleigh :
      ∀ x : M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian.domain,
        exactGapValueReal *
            ‖(x : M.toExplicitModel.VacuumOrthogonalHilbert)‖ ^ 2 ≤
          inner ℝ
            (M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian x)
            (x : M.toExplicitModel.VacuumOrthogonalHilbert)) : Prop :=
  M.toExplicitModel.axioms.toLegacy = S.definitionBridge.spine.axioms ∧
    (∀ psi : M.observables.PhysicalHilbert,
      Tendsto (fun t : ℝ => T.operator t psi)
        (nhdsWithin 0 (Set.Ici 0)) (nhds psi)) ∧
    (∀ x : M.hamiltonian.domain,
      Tendsto
        (fun t : ℝ =>
          t⁻¹ •
            (T.operator t (x : M.observables.PhysicalHilbert) -
              (x : M.observables.PhysicalHilbert)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (-(M.hamiltonian x)))) ∧
    IsLeast M.toExplicitModel.vacuumOrthogonalPVMOpenSupport
      exactGapValueReal ∧
    Set.Iio exactGapValueReal ⊆
      LinearPMap.realBijectiveResolventSet
        M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian ∧
    LinearPMap.realBijectiveSpectrum
        M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian ∩
      Set.Iio exactGapValueReal = ∅

/-- End-to-end dynamics theorem for the continuum OS physical reconstruction.

The exact support threshold and real resolvent exclusion are attached to the
same self-adjoint Hamiltonian that occurs as the generator of Euclidean-time
translation on the completed OS Hilbert space. -/
theorem euclidean_yang_mills_os_physical_generator_exact_gap_real_resolvent
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M.toExplicitModel)
    (hRelGap :
      HasRelativisticMassGap M.energyMomentumSpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum)
    (hRayleigh :
      ∀ x : M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian.domain,
        exactGapValueReal *
            ‖(x : M.toExplicitModel.VacuumOrthogonalHilbert)‖ ^ 2 ≤
          inner ℝ
            (M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian x)
            (x : M.toExplicitModel.VacuumOrthogonalHilbert)) :
    EuclideanYangMillsOSPhysicalGeneratorExactGapRealResolventProp
      T G B hRelGap hExactSpectrum hRayleigh := by
  have hResolvent :=
    euclidean_yang_mills_os_physical_exact_gap_real_resolvent
      M B hRelGap hExactSpectrum hRayleigh
  exact ⟨
    hResolvent.1,
    G.stronglyContinuousAtZero,
    G.generatorLimit,
    hResolvent.2.1,
    hResolvent.2.2.1,
    hResolvent.2.2.2⟩

end

end MathlibAnalytic
end MGAP4D
