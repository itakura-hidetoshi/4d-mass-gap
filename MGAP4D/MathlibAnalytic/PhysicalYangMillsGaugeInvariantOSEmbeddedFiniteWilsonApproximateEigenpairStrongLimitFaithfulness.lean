import MGAP4D.MathlibAnalytic.EmbeddedFiniteEigenpairResidualStrongLimit
import MGAP4D.MathlibAnalytic.FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitness
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSContinuumResolventApproximateEigenpairStrongLimitFaithfulness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Finite Wilson selected Hamiltonian eigenpairs embedded into the common
continuum excitation carrier and lifted into the target closed-Hamiltonian
domain.

The common spectral index explicitly tracks the selected eigenpair at every
scale. Isometric embedding and strong convergence make nonvanishing of the
continuum limiting vectors automatic. Pairwise distinct limiting energies
remain an explicit field; finite-scale injectivity alone is not used to infer
injectivity after passage to the limit. -/
structure VacuumSemigroupGapSlope.EmbeddedFiniteWilsonApproximateEigenpairStrongLimitData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    [DecidableEq G.BelowHalfMassShift]
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ) where
  finiteWitness :
    (n : ℕ) →
      FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
        F n (fun sigma : G.BelowHalfMassShift => sigma.1) nodes orderCap
  SpectralIndex : Type*
  [spectralFintype : Fintype SpectralIndex]
  finiteIndexEquiv :
    ∀ n, SpectralIndex ≃ (finiteWitness n).SpectralIndex
  embed :
    ℕ → F.StateSpace →L[ℝ] P.VacuumOrthogonalHilbert
  embed_norm :
    ∀ n phi, ‖embed n phi‖ = ‖phi‖
  approximateVector :
    ℕ → SpectralIndex →
      (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain
  approximateVector_coe :
    ∀ n k,
      (approximateVector n k : P.VacuumOrthogonalHilbert) =
        embed n ((finiteWitness n).spectralVector (finiteIndexEquiv n k))
  spectralValue : SpectralIndex → ℝ
  spectralValue_injective : Function.Injective spectralValue
  spectralVector : SpectralIndex → P.VacuumOrthogonalHilbert
  approximateValue_tendsto :
    ∀ k,
      Tendsto
        (fun n => (finiteWitness n).spectralValue (finiteIndexEquiv n k))
        atTop (nhds (spectralValue k))
  approximateVector_tendsto :
    ∀ k,
      Tendsto
        (fun n =>
          (approximateVector n k : P.VacuumOrthogonalHilbert))
        atTop (nhds (spectralVector k))
  operatorCompatibility_tendsto_zero :
    ∀ k,
      Tendsto
        (fun n =>
          T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
              (approximateVector n k) -
            embed n
              (F.hamiltonian n
                ((finiteWitness n).spectralVector
                  (finiteIndexEquiv n k))))
        atTop (nhds 0)

attribute [instance]
  VacuumSemigroupGapSlope.EmbeddedFiniteWilsonApproximateEigenpairStrongLimitData.spectralFintype

namespace VacuumSemigroupGapSlope.EmbeddedFiniteWilsonApproximateEigenpairStrongLimitData

variable {T : P.StronglyContinuousPhysicalSemigroup}
variable {G : T.VacuumSemigroupGapSlope}
variable [DecidableEq G.BelowHalfMassShift]
variable {hSelf : IsSelfAdjoint T.closedRightHamiltonian}
variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable {F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W}
variable {nodes : Finset G.BelowHalfMassShift}
variable {orderCap : ℕ}

/-- The finite Wilson energy tracked by the common spectral index. -/
def approximateValue
    (R : G.EmbeddedFiniteWilsonApproximateEigenpairStrongLimitData
      T hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : ℝ :=
  (R.finiteWitness n).spectralValue (R.finiteIndexEquiv n k)

/-- The finite Wilson eigenvector tracked by the common spectral index. -/
def finiteVector
    (R : G.EmbeddedFiniteWilsonApproximateEigenpairStrongLimitData
      T hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : F.StateSpace :=
  (R.finiteWitness n).spectralVector (R.finiteIndexEquiv n k)

/-- Every embedded lifted finite eigenvector has unit norm. -/
theorem approximateVector_norm
    (R : G.EmbeddedFiniteWilsonApproximateEigenpairStrongLimitData
      T hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    ‖(R.approximateVector n k : P.VacuumOrthogonalHilbert)‖ = 1 := by
  rw [R.approximateVector_coe, R.embed_norm]
  simpa [FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData.spectralVector,
    FiniteDimensionalSymmetricEigenbasisSelectionData.spectralVector] using
    ((F.hamiltonianSymmetric n).eigenvectorBasis F.stateFinrank).orthonormal.norm_eq_one
      ((R.finiteIndexEquiv n k).1)

/-- Strong convergence of unit embedded vectors preserves unit norm at the
continuum limit. -/
theorem spectralVector_norm
    (R : G.EmbeddedFiniteWilsonApproximateEigenpairStrongLimitData
      T hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    ‖R.spectralVector k‖ = 1 := by
  have hNormTendsto := (R.approximateVector_tendsto k).norm
  have hConstant :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
        (nhds ‖R.spectralVector k‖) := by
    simpa only [R.approximateVector_norm] using hNormTendsto
  exact tendsto_nhds_unique hConstant tendsto_const_nhds

/-- Nonvanishing of limiting continuum vectors is automatic from norm
preservation and strong convergence. -/
theorem spectralVector_ne_zero
    (R : G.EmbeddedFiniteWilsonApproximateEigenpairStrongLimitData
      T hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    R.spectralVector k ≠ 0 := by
  intro hzero
  have hnorm := R.spectralVector_norm k
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- Forget the finite Wilson presentation while retaining the exact finite
Hamiltonians, common-carrier embeddings, graph-compatible lifts, and vanishing
operator compatibility defect. -/
noncomputable def toEmbeddedFiniteDistinctEigenpairStrongLimitData
    (R : G.EmbeddedFiniteWilsonApproximateEigenpairStrongLimitData
      T hSelf F nodes orderCap) :
    EmbeddedFiniteDistinctEigenpairStrongLimitData
      (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
      (nodes.card * orderCap) :=
  { FiniteState := fun _ => F.StateSpace
    finiteNormedAddCommGroup := fun _ => F.stateNormedAddCommGroup
    finiteInnerProductSpace := fun _ => F.stateInnerProductSpace
    finiteOperator := F.hamiltonian
    finiteEigenpair := fun n => (R.finiteWitness n).toFiniteDistinctEigenpairData
    SpectralIndex := R.SpectralIndex
    spectralFintype := R.spectralFintype
    finiteIndexEquiv := R.finiteIndexEquiv
    embed := R.embed
    approximateVector := R.approximateVector
    approximateVector_coe := by
      intro n k
      simpa [FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData.toFiniteDistinctEigenpairData,
        FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData.spectralVector] using
        R.approximateVector_coe n k
    spectralValue := R.spectralValue
    spectralValue_injective := R.spectralValue_injective
    spectralVector := R.spectralVector
    spectralVector_ne_zero := R.spectralVector_ne_zero
    approximateValue_tendsto := by
      intro k
      simpa [FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData.toFiniteDistinctEigenpairData,
        FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData.spectralValue] using
        R.approximateValue_tendsto k
    approximateVector_tendsto := R.approximateVector_tendsto
    operatorCompatibility_tendsto_zero := by
      intro k
      simpa [FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData.toFiniteDistinctEigenpairData,
        FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData.spectralVector] using
        R.operatorCompatibility_tendsto_zero k }

/-- Embedded finite Wilson spectra construct the exact strong-limit transport
package consumed by the continuum resolvent faithfulness layer. -/
noncomputable def toContinuumResolventApproximateEigenpairStrongLimitData
    (R : G.EmbeddedFiniteWilsonApproximateEigenpairStrongLimitData
      T hSelf F nodes orderCap) :
    G.ContinuumResolventApproximateEigenpairStrongLimitData
      T hSelf nodes orderCap :=
  R.toEmbeddedFiniteDistinctEigenpairStrongLimitData
    |>.toClosedLinearPMapFiniteApproximateEigenpairStrongLimitData

/-- Embedded finite Wilson selected spectra with graph-compatible strong limits
supply continuum confluent resolvent linear independence. -/
theorem continuumResolventConfluentCauchy_linearIndependent
    (R : G.EmbeddedFiniteWilsonApproximateEigenpairStrongLimitData
      T hSelf F nodes orderCap)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    LinearIndependent ℝ
      (fun p : nodes × Fin orderCap =>
        ContinuousLinearMap.positivePowerJetOperatorFamily
          (fun sigma : G.BelowHalfMassShift =>
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf sigma.property)
          (p.1.1, p.2.1)) :=
  G.continuumResolventConfluentCauchy_linearIndependent_of_approximateEigenpairStrongLimit
    T hP hInnerSymmetric hSelf nodes orderCap
    R.toContinuumResolventApproximateEigenpairStrongLimitData

/-- The same embedded finite Wilson transport gives support-local continuum
positive-power jet coefficient-map faithfulness. -/
theorem continuumResolventPositivePowerJetCoefficientMapsIndependent
    (R : G.EmbeddedFiniteWilsonApproximateEigenpairStrongLimitData
      T hSelf F nodes orderCap)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (left right : ContinuousLinearMap.PositivePowerJetCoefficientMap
      G.BelowHalfMassShift)
    (hFit : G.PositivePowerJetCoefficientMapsFitWindow
      nodes orderCap left right) :
    G.ContinuumResolventPositivePowerJetCoefficientMapsIndependent
      T hP hInnerSymmetric hSelf left right :=
  G.continuumResolventPositivePowerJetCoefficientMapsIndependent_of_approximateEigenpairStrongLimit
    T hP hInnerSymmetric hSelf nodes orderCap
    R.toContinuumResolventApproximateEigenpairStrongLimitData left right hFit

end VacuumSemigroupGapSlope.EmbeddedFiniteWilsonApproximateEigenpairStrongLimitData

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
