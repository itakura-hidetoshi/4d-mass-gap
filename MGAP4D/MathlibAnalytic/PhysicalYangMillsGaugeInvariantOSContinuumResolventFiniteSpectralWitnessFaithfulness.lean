import MGAP4D.MathlibAnalytic.LinearPMapFiniteSpectralWitnessPositivePowerJetFaithfulness
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRationalFunctionalCalculusPositivePowerJetFaithfulness
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
whose shifted inverse-power evaluation coordinates separate one selected
node-order window. -/
structure VacuumSemigroupGapSlope.ContinuumResolventFiniteSpectralWitnessData
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
  scalarEvaluationLinearIndependent :
    LinearIndependent ℝ
      (fun p : nodes × Fin orderCap =>
        fun k : SpectralIndex =>
          ((spectralValue k - p.1.1.1)⁻¹ ^ (p.2.1 + 1)))

attribute [instance]
  VacuumSemigroupGapSlope.ContinuumResolventFiniteSpectralWitnessData.spectralFintype

/-- Every spectral witness value lies above the continuum half-mass Rayleigh
threshold. -/
theorem VacuumSemigroupGapSlope.ContinuumResolventFiniteSpectralWitnessData.spectralValue_ge_halfMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {nodes : Finset G.BelowHalfMassShift}
    {orderCap : ℕ}
    (R : G.ContinuumResolventFiniteSpectralWitnessData
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

/-- No below-half-mass shift is a pole at a spectral witness value. -/
theorem VacuumSemigroupGapSlope.ContinuumResolventFiniteSpectralWitnessData.spectralValue_ne_shift
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {nodes : Finset G.BelowHalfMassShift}
    {orderCap : ℕ}
    (R : G.ContinuumResolventFiniteSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes orderCap)
    (k : R.SpectralIndex)
    (sigma : G.BelowHalfMassShift) :
    R.spectralValue k ≠ sigma.1 := by
  exact ne_of_gt
    (lt_of_lt_of_le sigma.property
      (R.spectralValue_ge_halfMass T hP hInnerSymmetric hSelf k))

/-- Closed-Hamiltonian spectral witnesses generate the generic finite spectral
witness package for the selected continuum resolvent powers. -/
noncomputable def VacuumSemigroupGapSlope.ContinuumResolventFiniteSpectralWitnessData.toPositivePowerJetFiniteSpectralWitnessData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {nodes : Finset G.BelowHalfMassShift}
    {orderCap : ℕ}
    (R : G.ContinuumResolventFiniteSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes orderCap) :
    ContinuousLinearMap.PositivePowerJetCoefficientMap.FiniteSpectralWitnessData
      (fun sigma : G.BelowHalfMassShift =>
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property)
      nodes orderCap :=
  { Witness := R.SpectralIndex
    witnessFintype := R.spectralFintype
    witnessVector := fun k =>
      (R.spectralVector k : P.VacuumOrthogonalHilbert)
    witnessVector_ne_zero := R.spectralVector_ne_zero
    scalar := fun p k =>
      ((R.spectralValue k - p.1.1.1)⁻¹ ^ (p.2.1 + 1))
    scalarLinearIndependent := R.scalarEvaluationLinearIndependent
    operatorPower_apply_witness := by
      intro p k
      simpa [
        ContinuousLinearMap.positivePowerJetOperatorFamily,
        VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent] using
        (LinearPMap.realResolvent_pow_apply_eigenvector
          (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
          (mass := G.mass / 2)
          (lambda := p.1.1.1)
          (mu := R.spectralValue k)
          (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
            hP hSelf)
          p.1.1.property
          (G.vacuumOrthogonalClosedRightHamiltonian_halfGap
            T hP hInnerSymmetric hSelf)
          (R.spectralVector k)
          (R.hamiltonian_apply_spectralVector k)
          (R.spectralValue_ne_shift T hP hInnerSymmetric hSelf k p.1.1)
          (p.2.1 + 1)) }

/-- The selected continuum below-half-mass resolvent powers are linearly
independent whenever they are separated by finite Hamiltonian spectral
witnesses. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositivePowerJet_linearIndependent_of_finiteSpectralWitness
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.ContinuumResolventFiniteSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes orderCap) :
    LinearIndependent ℝ
      (fun p : nodes × Fin orderCap =>
        ContinuousLinearMap.positivePowerJetOperatorFamily
          (fun sigma : G.BelowHalfMassShift =>
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf sigma.property)
          (p.1.1, p.2.1)) :=
  R.toPositivePowerJetFiniteSpectralWitnessData
    T hP hInnerSymmetric hSelf |>.linearIndependent

/-- Finite closed-Hamiltonian spectral witnesses supply the exact continuum
support-local independence condition used by coefficient semantic uniqueness. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositivePowerJetCoefficientMapsIndependent_of_finiteSpectralWitness
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.ContinuumResolventFiniteSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes orderCap)
    (left right : ContinuousLinearMap.PositivePowerJetCoefficientMap
      G.BelowHalfMassShift)
    (hFit : G.PositivePowerJetCoefficientMapsFitWindow
      nodes orderCap left right) :
    G.ContinuumResolventPositivePowerJetCoefficientMapsIndependent
      T hP hInnerSymmetric hSelf left right := by
  rcases hFit with ⟨hNodes, hOrders⟩
  simpa [
    VacuumSemigroupGapSlope.ContinuumResolventPositivePowerJetCoefficientMapsIndependent] using
    (ContinuousLinearMap.PositivePowerJetCoefficientMap.areOperatorIndependentOnSupport_of_finiteSpectralWitness
      (fun sigma : G.BelowHalfMassShift =>
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property)
      nodes orderCap
      (R.toPositivePowerJetFiniteSpectralWitnessData
        T hP hInnerSymmetric hSelf)
      left right hNodes hOrders)

/-- Finite continuum Hamiltonian spectral witnesses upgrade operator-level
profile permutation invariance to equality of the recursively aggregated
coefficient Finsupps. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_continuumFiniteSpectralWitness
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.ContinuumResolventFiniteSpectralWitnessData
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
      G.resolventPositiveMultiplicityProfileCoefficientMap first₂ tail₂ := by
  apply
    G.resolventPositiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_continuumSupportIndependent
      T hP hInnerSymmetric hSelf first₁ first₂ tail₁ tail₂ hPerm hPairwise₁
  exact
    G.continuumResolventPositivePowerJetCoefficientMapsIndependent_of_finiteSpectralWitness
      T hP hInnerSymmetric hSelf nodes orderCap R _ _ hFit

/-- Finite continuum Hamiltonian spectral witnesses identify the
permutation-canonical coefficient map with the recursively aggregated map. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_continuumFiniteSpectralWitness
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.ContinuumResolventFiniteSpectralWitnessData
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
      G.resolventPositiveMultiplicityProfileCoefficientMap first tail := by
  apply
    G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_continuumSupportIndependent
      T hP hInnerSymmetric hSelf first tail hPairwise
  exact
    G.continuumResolventPositivePowerJetCoefficientMapsIndependent_of_finiteSpectralWitness
      T hP hInnerSymmetric hSelf nodes orderCap R _ _ hFit

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
