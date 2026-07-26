import MGAP4D.MathlibAnalytic.ConfluentCauchyKernelFiniteEvaluationLinearIndependence
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSContinuumResolventFiniteSpectralWitnessFaithfulness
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

/-- A finite confluent continuum spectral witness package.  Scalar Cauchy
linear independence is not a field: it is derived from injective spectral
values and the exact node-order cardinality. -/
structure VacuumSemigroupGapSlope.ContinuumResolventConfluentSpectralWitnessData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ) where
  SpectralIndex : Type*
  [spectralFintype : Fintype SpectralIndex]
  spectralValue : SpectralIndex → ℝ
  spectralValue_injective : Function.Injective spectralValue
  spectralCard : Fintype.card SpectralIndex = nodes.card * orderCap
  spectralVector : SpectralIndex →
    (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain
  spectralVector_ne_zero :
    ∀ k, (spectralVector k : P.VacuumOrthogonalHilbert) ≠ 0
  hamiltonian_apply_spectralVector :
    ∀ k,
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (spectralVector k) =
        spectralValue k •
          (spectralVector k : P.VacuumOrthogonalHilbert)

attribute [instance]
  VacuumSemigroupGapSlope.ContinuumResolventConfluentSpectralWitnessData.spectralFintype

/-- Every confluent spectral witness value lies above the continuum half-mass
Rayleigh threshold. -/
theorem VacuumSemigroupGapSlope.ContinuumResolventConfluentSpectralWitnessData.spectralValue_ge_halfMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {nodes : Finset G.BelowHalfMassShift}
    {orderCap : ℕ}
    (R : G.ContinuumResolventConfluentSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes orderCap)
    (k : R.SpectralIndex) :
    G.mass / 2 ≤ R.spectralValue k := by
  have hGap :=
    G.vacuumOrthogonalClosedRightHamiltonian_halfGap
      T hP hInnerSymmetric hSelf (R.spectralVector k)
  rw [R.hamiltonian_apply_spectralVector k,
    real_inner_smul_left, real_inner_self_eq_norm_sq] at hGap
  have hNormPos :
      0 < ‖(R.spectralVector k : P.VacuumOrthogonalHilbert)‖ :=
    norm_pos_iff.mpr (R.spectralVector_ne_zero k)
  nlinarith [sq_pos_of_pos hNormPos]

/-- No below-half-mass shift is a pole at a confluent spectral witness value. -/
theorem VacuumSemigroupGapSlope.ContinuumResolventConfluentSpectralWitnessData.spectralValue_ne_shift
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {nodes : Finset G.BelowHalfMassShift}
    {orderCap : ℕ}
    (R : G.ContinuumResolventConfluentSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes orderCap)
    (k : R.SpectralIndex)
    (sigma : G.BelowHalfMassShift) :
    R.spectralValue k ≠ sigma.1 := by
  exact ne_of_gt
    (lt_of_lt_of_le sigma.property
      (R.spectralValue_ge_halfMass T G hP hInnerSymmetric hSelf k))

/-- Distinct spectral values with the exact node-order cardinality automatically
separate every selected confluent Cauchy column. -/
theorem VacuumSemigroupGapSlope.ContinuumResolventConfluentSpectralWitnessData.scalarEvaluationLinearIndependent
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {nodes : Finset G.BelowHalfMassShift}
    {orderCap : ℕ}
    (R : G.ContinuumResolventConfluentSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes orderCap) :
    LinearIndependent ℝ
      (fun p : nodes × Fin orderCap =>
        fun k : R.SpectralIndex =>
          ((R.spectralValue k - p.1.1.1)⁻¹ ^ (p.2.1 + 1))) := by
  classical
  have hNodeInjective : Function.Injective
      (fun sigma : nodes => sigma.1.1) := by
    intro left right hvalue
    apply Subtype.ext
    apply Subtype.ext
    exact hvalue
  have hCard :
      Fintype.card R.SpectralIndex = Fintype.card nodes * orderCap := by
    simpa using R.spectralCard
  exact ContinuousLinearMap.confluentCauchyKernel_linearIndependent
    (fun sigma : nodes => sigma.1.1)
    orderCap
    R.spectralValue
    hNodeInjective
    R.spectralValue_injective
    hCard
    (fun k sigma =>
      R.spectralValue_ne_shift T G hP hInnerSymmetric hSelf k sigma.1)

/-- A confluent continuum spectral witness package canonically supplies the
general finite spectral witness package at the same `orderCap`. -/
noncomputable def VacuumSemigroupGapSlope.ContinuumResolventConfluentSpectralWitnessData.toContinuumResolventFiniteSpectralWitnessData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {nodes : Finset G.BelowHalfMassShift}
    {orderCap : ℕ}
    (R : G.ContinuumResolventConfluentSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes orderCap) :
    G.ContinuumResolventFiniteSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes orderCap :=
  { SpectralIndex := R.SpectralIndex
    spectralFintype := R.spectralFintype
    spectralValue := R.spectralValue
    spectralVector := R.spectralVector
    spectralVector_ne_zero := R.spectralVector_ne_zero
    hamiltonian_apply_spectralVector := R.hamiltonian_apply_spectralVector
    scalarEvaluationLinearIndependent :=
      R.scalarEvaluationLinearIndependent T G hP hInnerSymmetric hSelf }

/-- The selected continuum resolvent powers are linearly independent whenever
there are exactly enough distinct Hamiltonian spectral witnesses. -/
theorem VacuumSemigroupGapSlope.continuumResolventConfluentCauchy_linearIndependent_of_confluentSpectralWitness
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.ContinuumResolventConfluentSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes orderCap) :
    LinearIndependent ℝ
      (fun p : nodes × Fin orderCap =>
        ContinuousLinearMap.positivePowerJetOperatorFamily
          (fun sigma : G.BelowHalfMassShift =>
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf sigma.property)
          (p.1.1, p.2.1)) :=
  G.continuumResolventPositivePowerJet_linearIndependent_of_finiteSpectralWitness
    T hP hInnerSymmetric hSelf nodes orderCap
    (R.toContinuumResolventFiniteSpectralWitnessData
      T G hP hInnerSymmetric hSelf)

/-- Confluent spectral witnesses supply support-local faithfulness for all
coefficient maps fitting their node-order window. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositivePowerJetCoefficientMapsIndependent_of_confluentSpectralWitness
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.ContinuumResolventConfluentSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes orderCap)
    (left right : ContinuousLinearMap.PositivePowerJetCoefficientMap
      G.BelowHalfMassShift)
    (hFit : G.PositivePowerJetCoefficientMapsFitWindow
      nodes orderCap left right) :
    G.ContinuumResolventPositivePowerJetCoefficientMapsIndependent
      T hP hInnerSymmetric hSelf left right :=
  G.continuumResolventPositivePowerJetCoefficientMapsIndependent_of_finiteSpectralWitness
    T hP hInnerSymmetric hSelf nodes orderCap
    (R.toContinuumResolventFiniteSpectralWitnessData
      T G hP hInnerSymmetric hSelf)
    left right hFit

/-- Finite distinct confluent Hamiltonian spectral witnesses upgrade profile
permutation invariance to exact recursive coefficient Finsupp equality. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_continuumConfluentSpectralWitness
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.ContinuumResolventConfluentSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes orderCap)
    (first₁ first₂ : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail₁ tail₂ : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂))
    (hPairwise₁ :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first₁ tail₁)
    (hFit : G.PositivePowerJetCoefficientMapsFitWindow nodes orderCap
      (G.resolventPositiveMultiplicityProfileCoefficientMap first₁ tail₁)
      (G.resolventPositiveMultiplicityProfileCoefficientMap first₂ tail₂)) :
    G.resolventPositiveMultiplicityProfileCoefficientMap first₁ tail₁ =
      G.resolventPositiveMultiplicityProfileCoefficientMap first₂ tail₂ :=
  G.resolventPositiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_continuumFiniteSpectralWitness
    T hP hInnerSymmetric hSelf nodes orderCap
    (R.toContinuumResolventFiniteSpectralWitnessData
      T G hP hInnerSymmetric hSelf)
    first₁ first₂ tail₁ tail₂ hPerm hPairwise₁ hFit

/-- Finite distinct confluent Hamiltonian spectral witnesses identify the
permutation-canonical coefficient map with the recursive coefficient map. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_continuumConfluentSpectralWitness
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.ContinuumResolventConfluentSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes orderCap)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPairwise :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first tail)
    (hFit : G.PositivePowerJetCoefficientMapsFitWindow nodes orderCap
      (G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap
        first tail)
      (G.resolventPositiveMultiplicityProfileCoefficientMap first tail)) :
    G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap
        first tail =
      G.resolventPositiveMultiplicityProfileCoefficientMap first tail :=
  G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_continuumFiniteSpectralWitness
    T hP hInnerSymmetric hSelf nodes orderCap
    (R.toContinuumResolventFiniteSpectralWitnessData
      T G hP hInnerSymmetric hSelf)
    first tail hPairwise hFit

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D