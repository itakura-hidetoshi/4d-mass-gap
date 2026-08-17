import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationTimeAverage
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonian
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The infinitesimal loss of the physical OS autocorrelation along the
positive Euclidean-time axis is exactly the quadratic form of the canonical
right Hamiltonian.

This is the direct correlation/Hamiltonian bridge on the canonical generator
domain.  It uses only the defining strong right-generator limit and the
Euclidean sign convention `T_t = exp (-t H)`; no spectral theorem,
self-adjointness hypothesis, or additional physical assumption is used. -/
theorem physicalCorrelation_rightSlope_tendsto_rightHamiltonian_inner
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.rightGeneratorDomain) :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (T.physicalCorrelation (psi : P.PhysicalHilbert) 0 -
            T.physicalCorrelation (psi : P.PhysicalHilbert) t))
      (nhdsWithin 0 (Ioi 0))
      (nhds
        ⟪T.rightHamiltonian psi,
          (psi : P.PhysicalHilbert)⟫_ℝ) := by
  have hgenerator := T.rightGenerator_hasRightGeneratorValue psi
  unfold HasRightGeneratorValue at hgenerator
  have hham :
      Tendsto
        (fun t : NNReal =>
          T.rightHamiltonianDifferenceQuotient
            (psi : P.PhysicalHilbert) t)
        (nhdsWithin 0 (Ioi 0))
        (nhds (T.rightHamiltonian psi)) := by
    have hneg := hgenerator.neg
    simpa only [T.rightHamiltonianDifferenceQuotient_eq_neg,
      T.rightHamiltonian_apply] using hneg
  have hinner :
      Tendsto
        (fun t : NNReal =>
          ⟪T.rightHamiltonianDifferenceQuotient
              (psi : P.PhysicalHilbert) t,
            (psi : P.PhysicalHilbert)⟫_ℝ)
        (nhdsWithin 0 (Ioi 0))
        (nhds
          ⟪T.rightHamiltonian psi,
            (psi : P.PhysicalHilbert)⟫_ℝ) :=
    hham.inner tendsto_const_nhds
  have hcorr (t : NNReal) :
      T.physicalCorrelation (psi : P.PhysicalHilbert) t =
        ⟪T.toPhysicalSemigroup.operator t (psi : P.PhysicalHilbert),
          (psi : P.PhysicalHilbert)⟫_ℝ := by
    rw [physicalCorrelation, real_inner_comm]
  simpa [rightHamiltonianDifferenceQuotient, hcorr,
    T.toPhysicalSemigroup.operator_zero, real_inner_smul_left,
    inner_sub_left] using hinner

/-- The preceding infinitesimal OS decay rate is nonnegative, in agreement
with contractivity of Euclidean time evolution. -/
theorem physicalCorrelation_rightSlope_limit_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.rightGeneratorDomain) :
    0 ≤ ⟪T.rightHamiltonian psi,
      (psi : P.PhysicalHilbert)⟫_ℝ :=
  T.rightHamiltonian_inner_nonneg psi

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
