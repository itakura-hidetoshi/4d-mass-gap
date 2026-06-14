import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalTimeTranslationCore

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

structure EuclideanYangMillsOSPhysicalStrongContinuityCore
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslationCore M) where
  stronglyContinuousAtZero :
    ∀ psi : M.observables.PhysicalHilbert,
      Tendsto (fun t : ℝ => T.operator t psi)
        (nhdsWithin 0 (Set.Ici 0)) (nhds psi)
  rightDerivativeLimit :
    ∀ x : M.hamiltonian.domain,
      Tendsto
        (fun t : ℝ =>
          t⁻¹ •
            (T.operator t (x : M.observables.PhysicalHilbert) -
              (x : M.observables.PhysicalHilbert)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (-(M.hamiltonian x)))

end

end MathlibAnalytic
end MGAP4D
