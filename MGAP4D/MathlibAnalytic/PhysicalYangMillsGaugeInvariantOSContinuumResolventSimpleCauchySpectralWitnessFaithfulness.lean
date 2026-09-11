import MGAP4D.MathlibAnalytic.SimpleCauchyKernelFiniteEvaluationLinearIndependence
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

/-- A simple-pole continuum spectral witness package.  Unlike the general
finite spectral witness data, scalar Cauchy linear independence is not a field:
it is derived from injective spectral values and exact cardinality. -/
structure VacuumSemigroupGapSlope.ContinuumResolventSimpleSpectralWitnessData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift) where
  SpectralIndex : Type*
  [spectralFintype : Fintype SpectralIndex]
  spectralValue : SpectralIndex → ℝ
  spectralValue_injective : Function.Injective spectralValue
  spectralCard : Fintype.card SpectralIndex = nodes.card
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
  VacuumSemigroupGapSlope.ContinuumResolventSimpleSpectralWitnessData.spectralFintype

/-- Every simple spectral witness value lies above the continuum half-mass
Rayleigh threshold. -/
theorem VacuumSemigroupGapSlope.ContinuumResolventSimpleSpectralWitnessData.spectralValue_ge_halfMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {nodes : Finset G.BelowHalfMassShift}
    (R : G.ContinuumResolventSimpleSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes)
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

/-- No below-half-mass shift is a pole at a simple spectral witness value. -/
theorem VacuumSemigroupGapSlope.ContinuumResolventSimpleSpectralWitnessData.spectralValue_ne_shift
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {nodes : Finset G.BelowHalfMassShift}
    (R : G.ContinuumResolventSimpleSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes)
    (k : R.SpectralIndex)
    (sigma : G.BelowHalfMassShift) :
    R.spectralValue k ≠ sigma.1 := by
  exact ne_of_gt
    (lt_of_lt_of_le sigma.property
      (R.spectralValue_ge_halfMass T G hP hInnerSymmetric hSelf k))

/-- Distinct simple spectral values with the exact node cardinality automatically
separate all ordinary Cauchy columns. -/
theorem VacuumSemigroupGapSlope.ContinuumResolventSimpleSpectralWitnessData.scalarEvaluationLinearIndependent
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {nodes : Finset G.BelowHalfMassShift}
    (R : G.ContinuumResolventSimpleSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes) :
    LinearIndependent ℝ
      (fun p : nodes × Fin 1 =>
        fun k : R.SpectralIndex =>
          ((R.spectralValue k - p.1.1.1)⁻¹ ^ (p.2.1 + 1))) := by
  classical
  have hNodeInjective : Function.Injective
      (fun sigma : nodes => sigma.1.1) := by
    intro left right hvalue
    apply Subtype.ext
    apply Subtype.ext
    exact hvalue
  have hCard : Fintype.card R.SpectralIndex = Fintype.card nodes := by
    simpa using R.spectralCard
  have hSimple :=
    ContinuousLinearMap.simpleCauchyKernel_linearIndependent
      (fun sigma : nodes => sigma.1.1)
      R.spectralValue
      hNodeInjective
      R.spectralValue_injective
      hCard
      (fun k sigma =>
        R.spectralValue_ne_shift T G hP hInnerSymmetric hSelf k sigma.1)
  have hProjection : Function.Injective
      (fun p : nodes × Fin 1 => p.1) := by
    intro left right hleft
    apply Prod.ext hleft
    exact Subsingleton.elim _ _
  have hComposed := hSimple.comp
    (fun p : nodes × Fin 1 => p.1) hProjection
  simpa using hComposed

/-- A simple continuum spectral witness package canonically supplies the general
finite spectral witness package at `orderCap = 1`. -/
noncomputable def VacuumSemigroupGapSlope.ContinuumResolventSimpleSpectralWitnessData.toContinuumResolventFiniteSpectralWitnessData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {nodes : Finset G.BelowHalfMassShift}
    (R : G.ContinuumResolventSimpleSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes) :
    G.ContinuumResolventFiniteSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes 1 :=
  { SpectralIndex := R.SpectralIndex
    spectralFintype := R.spectralFintype
    spectralValue := R.spectralValue
    spectralVector := R.spectralVector
    spectralVector_ne_zero := R.spectralVector_ne_zero
    hamiltonian_apply_spectralVector := R.hamiltonian_apply_spectralVector
    scalarEvaluationLinearIndependent :=
      R.scalarEvaluationLinearIndependent T G hP hInnerSymmetric hSelf }

/-- The selected ordinary continuum resolvents are linearly independent whenever
there are equally many distinct Hamiltonian spectral witnesses. -/
theorem VacuumSemigroupGapSlope.continuumResolventSimpleCauchy_linearIndependent_of_simpleSpectralWitness
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (R : G.ContinuumResolventSimpleSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes) :
    LinearIndependent ℝ
      (fun p : nodes × Fin 1 =>
        ContinuousLinearMap.positivePowerJetOperatorFamily
          (fun sigma : G.BelowHalfMassShift =>
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf sigma.property)
          (p.1.1, p.2.1)) :=
  G.continuumResolventPositivePowerJet_linearIndependent_of_finiteSpectralWitness
    T hP hInnerSymmetric hSelf nodes 1
    (R.toContinuumResolventFiniteSpectralWitnessData
      T G hP hInnerSymmetric hSelf)

/-- Simple spectral witnesses supply support-local faithfulness for coefficient
maps whose orders all fit the simple-pole window. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositivePowerJetCoefficientMapsIndependent_of_simpleSpectralWitness
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (R : G.ContinuumResolventSimpleSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes)
    (left right : ContinuousLinearMap.PositivePowerJetCoefficientMap
      G.BelowHalfMassShift)
    (hFit : G.PositivePowerJetCoefficientMapsFitWindow nodes 1 left right) :
    G.ContinuumResolventPositivePowerJetCoefficientMapsIndependent
      T hP hInnerSymmetric hSelf left right :=
  G.continuumResolventPositivePowerJetCoefficientMapsIndependent_of_finiteSpectralWitness
    T hP hInnerSymmetric hSelf nodes 1
    (R.toContinuumResolventFiniteSpectralWitnessData
      T G hP hInnerSymmetric hSelf)
    left right hFit

/-- For simple-pole coefficient windows, finite distinct Hamiltonian spectral
witnesses upgrade profile permutation invariance to exact recursive Finsupp
equality without assuming scalar Cauchy linear independence separately. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_continuumSimpleSpectralWitness
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (R : G.ContinuumResolventSimpleSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes)
    (first₁ first₂ : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail₁ tail₂ : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂))
    (hPairwise₁ :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first₁ tail₁)
    (hFit : G.PositivePowerJetCoefficientMapsFitWindow nodes 1
      (G.resolventPositiveMultiplicityProfileCoefficientMap first₁ tail₁)
      (G.resolventPositiveMultiplicityProfileCoefficientMap first₂ tail₂)) :
    G.resolventPositiveMultiplicityProfileCoefficientMap first₁ tail₁ =
      G.resolventPositiveMultiplicityProfileCoefficientMap first₂ tail₂ :=
  G.resolventPositiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_continuumFiniteSpectralWitness
    T hP hInnerSymmetric hSelf nodes 1
    (R.toContinuumResolventFiniteSpectralWitnessData
      T G hP hInnerSymmetric hSelf)
    first₁ first₂ tail₁ tail₂ hPerm hPairwise₁ hFit

/-- For simple-pole coefficient windows, finite distinct Hamiltonian spectral
witnesses identify the permutation-canonical and recursive coefficient maps. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_continuumSimpleSpectralWitness
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (R : G.ContinuumResolventSimpleSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPairwise :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first tail)
    (hFit : G.PositivePowerJetCoefficientMapsFitWindow nodes 1
      (G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap
        first tail)
      (G.resolventPositiveMultiplicityProfileCoefficientMap first tail)) :
    G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap
        first tail =
      G.resolventPositiveMultiplicityProfileCoefficientMap first tail :=
  G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_continuumFiniteSpectralWitness
    T hP hInnerSymmetric hSelf nodes 1
    (R.toContinuumResolventFiniteSpectralWitnessData
      T G hP hInnerSymmetric hSelf)
    first tail hPairwise hFit

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
