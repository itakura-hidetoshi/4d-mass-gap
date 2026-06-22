import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryDensityGramKernel

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def periodicHypercubicEvenBoundaryObservableGramFeature
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
    H N hN beta hbeta b x * f x

end

end MathlibAnalytic
end MGAP4D
