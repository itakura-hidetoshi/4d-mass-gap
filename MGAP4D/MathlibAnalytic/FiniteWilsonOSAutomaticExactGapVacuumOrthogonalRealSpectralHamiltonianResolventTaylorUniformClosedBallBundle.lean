import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventTaylorUniformClosedBallBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianResolventTaylorSeriesBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- Finite Wilson `Ω⊥` exact-derivative Taylor truncations obey one uniform
geometric envelope on every strict closed subgap ball. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_sub_taylor_partialSum_norm_le_closedBall
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n N : ℕ) {lambda r mu : ℝ}
    (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) :
    ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
            lambda)‖ ≤
      (r * (exactGapValueReal - lambda)⁻¹) ^ N *
        (exactGapValueReal - lambda - r)⁻¹ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_taylor_partialSum_norm_le_closedBall
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n N hlambda hr0 hrlt hmu

/-- Finite Wilson `Ω⊥` exact-derivative Taylor partial sums converge uniformly
in operator norm on every strict closed subgap ball. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_taylor_partialSum_tendstoUniformlyOn_closedBall
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda r : ℝ}
    (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda) :
    TendstoUniformlyOn
      (fun N : ℕ => fun mu : ℝ =>
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
            lambda)
      (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
      atTop (Metric.closedBall lambda r) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_partialSum_tendstoUniformlyOn_closedBall
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n hlambda hr0 hrlt

end MathlibAnalytic
end MGAP4D

end