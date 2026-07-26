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

/-- Finite nonzero eigenvectors of the closed continuum excitation Hamiltonian
with pairwise distinct eigenvalues and exactly as many witnesses as selected
below-half-mass nodes.  Ordinary Cauchy separation then supplies the scalar
linear-independence field needed by the order-one spectral-witness package. -/
structure VacuumSemigroupGapSlope.ContinuumSimpleResolventFiniteSpectralWitnessData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift) where
  SpectralIndex : Type*
  [spectralFintype : Fintype SpectralIndex]
  spectralValue : SpectralIndex → ℝ
  spectralValueInjective : Function.Injective spectralValue
  spectralCard_eq_nodes : Fintype.card SpectralIndex = Fintype.card nodes
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
  VacuumSemigroupGapSlope.ContinuumSimpleResolventFiniteSpectralWitnessData.spectralFintype

/-- Every simple spectral witness value lies above the continuum half-mass
Rayleigh threshold. -/
theorem VacuumSemigroupGapSlope.ContinuumSimpleResolventFiniteSpectralWitnessData.spectralValue_ge_halfMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {nodes : Finset G.BelowHalfMassShift}
    (R : G.ContinuumSimpleResolventFiniteSpectralWitnessData
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

/-- Every below-half-mass node is a non-pole at every simple spectral witness
value. -/
theorem VacuumSemigroupGapSlope.ContinuumSimpleResolventFiniteSpectralWitnessData.spectralValue_ne_shift
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {nodes : Finset G.BelowHalfMassShift}
    (R : G.ContinuumSimpleResolventFiniteSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes)
    (k : R.SpectralIndex)
    (sigma : G.BelowHalfMassShift) :
    R.spectralValue k ≠ sigma.1 := by
  exact ne_of_gt
    (lt_of_lt_of_le sigma.property
      (R.spectralValue_ge_halfMass T G hP hInnerSymmetric hSelf k))

/-- Distinct simple spectral values, with the same cardinality as the selected
nodes, automatically separate the ordinary Cauchy kernel columns. -/
theorem VacuumSemigroupGapSlope.ContinuumSimpleResolventFiniteSpectralWitnessData.scalarEvaluationLinearIndependent
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {nodes : Finset G.BelowHalfMassShift}
    (R : G.ContinuumSimpleResolventFiniteSpectralWitnessData
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
  have hSimple : LinearIndependent ℝ
      (fun sigma : nodes =>
        fun k : R.SpectralIndex =>
          (R.spectralValue k - sigma.1.1)⁻¹) :=
    ContinuousLinearMap.simpleCauchyKernel_linearIndependent
      (fun sigma : nodes => sigma.1.1)
      R.spectralValue
      hNodeInjective
      R.spectralValueInjective
      R.spectralCard_eq_nodes
      (fun k sigma =>
        R.spectralValue_ne_shift T G hP hInnerSymmetric hSelf k sigma.1)
  have hProjection : Function.Injective
      (fun p : nodes × Fin 1 => p.1) := by
    intro left right hfirst
    apply Prod.ext
    · exact hfirst
    · exact Subsingleton.elim _ _
  have hComp := hSimple.comp (fun p : nodes × Fin 1 => p.1) hProjection
  have hFamily :
      (fun p : nodes × Fin 1 =>
        fun k : R.SpectralIndex =>
          ((R.spectralValue k - p.1.1.1)⁻¹ ^ (p.2.1 + 1))) =
      (fun p : nodes × Fin 1 =>
        fun k : R.SpectralIndex =>
          (R.spectralValue k - p.1.1.1)⁻¹) := by
    funext p k
    have hp : p.2 = 0 := Subsingleton.elim _ _
    rw [hp]
    simp
  rw [hFamily]
  exact hComp

/-- Convert distinct finite continuum eigenvalue data into the existing
order-one continuum resolvent spectral-witness package. -/
noncomputable def VacuumSemigroupGapSlope.ContinuumSimpleResolventFiniteSpectralWitnessData.toContinuumResolventFiniteSpectralWitnessData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {nodes : Finset G.BelowHalfMassShift}
    (R : G.ContinuumSimpleResolventFiniteSpectralWitnessData
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

/-- Distinct finite continuum eigenvalues automatically give linear
independence of the selected simple resolvents. -/
theorem VacuumSemigroupGapSlope.continuumSimpleResolvent_linearIndependent_of_distinctFiniteSpectralWitness
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (R : G.ContinuumSimpleResolventFiniteSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes) :
    LinearIndependent ℝ
      (fun p : nodes × Fin 1 =>
        ContinuousLinearMap.positivePowerJetOperatorFamily
          (fun sigma : G.BelowHalfMassShift =>
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf sigma.property)
          (p.1.1, p.2.1)) :=
  G.continuumResolventPositivePowerJet_linearIndependent_of_finiteSpectralWitness
    T G hP hInnerSymmetric hSelf nodes 1
    (R.toContinuumResolventFiniteSpectralWitnessData
      T G hP hInnerSymmetric hSelf)

/-- Distinct finite continuum eigenvalues supply the support-local semantic
faithfulness condition for coefficient maps supported at order zero. -/
theorem VacuumSemigroupGapSlope.continuumSimpleResolventPositivePowerJetCoefficientMapsIndependent_of_distinctFiniteSpectralWitness
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (R : G.ContinuumSimpleResolventFiniteSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes)
    (left right : ContinuousLinearMap.PositivePowerJetCoefficientMap
      G.BelowHalfMassShift)
    (hFit : G.PositivePowerJetCoefficientMapsFitWindow
      nodes 1 left right) :
    G.ContinuumResolventPositivePowerJetCoefficientMapsIndependent
      T hP hInnerSymmetric hSelf left right :=
  G.continuumResolventPositivePowerJetCoefficientMapsIndependent_of_finiteSpectralWitness
    T G hP hInnerSymmetric hSelf nodes 1
    (R.toContinuumResolventFiniteSpectralWitnessData
      T G hP hInnerSymmetric hSelf)
    left right hFit

/-- In the simple-pole window, distinct finite continuum eigenvalues upgrade
operator-level profile permutation invariance to equality of the recursive
coefficient Finsupps. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_continuumDistinctSimpleSpectralWitness
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (R : G.ContinuumSimpleResolventFiniteSpectralWitnessData
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
    T G hP hInnerSymmetric hSelf nodes 1
    (R.toContinuumResolventFiniteSpectralWitnessData
      T G hP hInnerSymmetric hSelf)
    first₁ first₂ tail₁ tail₂ hPerm hPairwise₁ hFit

/-- In the simple-pole window, the permutation-canonical coefficient map is
the recursive coefficient map whenever distinct finite continuum eigenvalues
are available. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_continuumDistinctSimpleSpectralWitness
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (R : G.ContinuumSimpleResolventFiniteSpectralWitnessData
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
    T G hP hInnerSymmetric hSelf nodes 1
    (R.toContinuumResolventFiniteSpectralWitnessData
      T G hP hInnerSymmetric hSelf)
    first tail hPairwise hFit

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
