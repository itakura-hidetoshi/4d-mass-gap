import MGAP4D.MathlibAnalytic.ContinuousAntitoneNonnegativeNNRealUniformContinuous
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationTimeAverage

/-!
# Uniform continuity of physical OS two-point correlations

For the actual completed strongly continuous physical OS contraction semigroup,
an inner-product symmetric time evolution has scalar autocorrelation

`C_ψ(t) = ⟪ψ, T_t ψ⟫_ℝ`.

The existing OS layer proves that this correlation is antitone and nonnegative.
Strong continuity gives ordinary continuity.  The generic half-line theorem then
upgrades these three facts to global uniform continuity on nonnegative Euclidean
time, without using a spectral theorem or adding a mass-gap hypothesis.
-/

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

/-- Strong continuity of the physical orbit implies continuity of its scalar
OS autocorrelation. -/
theorem physicalCorrelation_continuous
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    Continuous (T.physicalCorrelation psi) := by
  unfold physicalCorrelation
  exact continuous_const.inner (T.physicalOrbit_continuous psi)

/-- Every symmetric physical OS autocorrelation has a finite nonnegative-time
limit, namely the infimum of its values. -/
theorem physicalCorrelation_tendsto_atTop_ciInf
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert) :
    Tendsto (T.physicalCorrelation psi) atTop
      (nhds (⨅ t : NNReal, T.physicalCorrelation psi t)) := by
  exact MGAP4D.antitone_nonnegative_nnreal_tendsto_atTop_ciInf
    (T.physicalCorrelation psi)
    (T.physicalCorrelation_antitone hSymmetric psi)
    (fun t => T.physicalCorrelation_nonneg hSymmetric t psi)

/-- The physical symmetric-semigroup two-point autocorrelation is globally
uniformly continuous in nonnegative Euclidean time.  No spectral theorem,
decay estimate, or mass-gap input is required. -/
theorem physicalCorrelation_uniformContinuous
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert) :
    UniformContinuous (T.physicalCorrelation psi) := by
  exact MGAP4D.uniformContinuous_of_continuous_antitone_nonnegative_nnreal
    (T.physicalCorrelation psi)
    (T.physicalCorrelation_continuous psi)
    (T.physicalCorrelation_antitone hSymmetric psi)
    (fun t => T.physicalCorrelation_nonneg hSymmetric t psi)

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
