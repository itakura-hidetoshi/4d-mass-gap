import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PhysicalTransferModePositiveTimeBoundaryPairClosure
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonCarrierOneStepEigenmodeLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

private theorem su2BoundaryPairCommonCarrierTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance su2BoundaryPairCommonCarrierSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance su2BoundaryPairCommonCarrierTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2BoundaryPairCommonCarrierCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2BoundaryPairCommonCarrierSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2BoundaryPairCommonCarrierMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2BoundaryPairCommonCarrierBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

section SU2BoundaryPairCommonCarrier

variable
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 su2BoundaryPairCommonCarrierTwoRankPositive beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent 2 su2BoundaryPairCommonCarrierTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant}
    {G : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent 2 su2BoundaryPairCommonCarrierTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant C}

/-- The finite eigenvector produced by the positive-time boundary-pair closure
criterion is forced to be the canonical common-carrier approximant as soon as
the two states have the same concrete completed Wilson boundary realization.

The proof uses only injectivity of the already-canonical boundary linear
isometry.  It introduces neither a finite-Hilbert identification nor a new
choice of approximating state. -/
theorem finiteOperator_one_apply_approximate_of_normalizedPhysicalTransferModePositiveTimeBoundaryPairClosure
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2BoundaryPairCommonCarrierTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (psi : P.PhysicalHilbert)
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) 2)
    (mu : ℝ)
    (hf : periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) 2 su2BoundaryPairCommonCarrierTwoRankPositive
        (beta n) (hbeta n) f = mu • f)
    (hBoundary :
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (A.approximate n psi) =
        periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
          (halfExtent n) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
            (halfExtent n) 2 f)
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
            (halfExtent n) 2 su2BoundaryPairCommonCarrierTwoRankPositive
              (beta n) (hbeta n)))
    (W : Q.PhysicalTransferModePositiveTimeSubmoduleBoundaryPairClosureAt
      hInvariant C n f) :
    C.finiteOperator n 1 (A.approximate n psi) =
      mu • A.approximate n psi := by
  obtain ⟨phi, hphiBoundary, hphiEigen⟩ :=
    Q.exists_finiteOperator_one_eigen_of_normalizedPhysicalTransferModePositiveTimeBoundaryPairClosure
      hInvariant C n f mu hf W
  have hphi : phi = A.approximate n psi := by
    apply (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n).injective
    exact hphiBoundary.trans hBoundary.symm
  simpa [hphi] using hphiEigen

/-- Cutoff-dependent normalized physical SU(2) transfer modes pass all the way
through the Wilson common carrier once their concrete one-sided boundary
realizations agree with the canonical finite approximants.

The finite eigen-equations are not assumed: each is generated by the
post-synthesis positive-time boundary-pair closure theorem above.  The only
limit input is convergence of the scalar one-step eigenvalues. -/
theorem physicalOperator_one_apply_of_normalizedPhysicalTransferModePositiveTimeBoundaryPairClosure
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2BoundaryPairCommonCarrierTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (psi : P.PhysicalHilbert)
    (f : (n : ℕ) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) 2)
    (mu : ℕ → ℝ)
    (muLimit : ℝ)
    (hmu : Tendsto mu atTop (𝓝 muLimit))
    (hf : ∀ n,
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        (halfExtent n) 2 su2BoundaryPairCommonCarrierTwoRankPositive
          (beta n) (hbeta n) (f n) = mu n • f n)
    (hBoundary : ∀ n,
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (A.approximate n psi) =
        periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
          (halfExtent n) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
            (halfExtent n) 2 (f n))
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
            (halfExtent n) 2 su2BoundaryPairCommonCarrierTwoRankPositive
              (beta n) (hbeta n)))
    (hClosure : ∀ n,
      Q.PhysicalTransferModePositiveTimeSubmoduleBoundaryPairClosureAt
        hInvariant C n (f n)) :
    T.toPhysicalSemigroup.operator 1 psi = muLimit • psi := by
  apply physicalOperator_one_apply_of_approximating_eigen
    A psi mu muLimit hmu
  intro n
  exact
    finiteOperator_one_apply_approximate_of_normalizedPhysicalTransferModePositiveTimeBoundaryPairClosure
      A psi n (f n) (mu n) (hf n) (hBoundary n) (hClosure n)

/-- Fixed-eigenvalue specialization of the SU(2) boundary-pair common-carrier
transport. -/
theorem physicalOperator_one_apply_of_fixed_normalizedPhysicalTransferModePositiveTimeBoundaryPairClosure
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent 2 su2BoundaryPairCommonCarrierTwoRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant P T C G)
    (psi : P.PhysicalHilbert)
    (f : (n : ℕ) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        (halfExtent n) 2)
    (mu : ℝ)
    (hf : ∀ n,
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        (halfExtent n) 2 su2BoundaryPairCommonCarrierTwoRankPositive
          (beta n) (hbeta n) (f n) = mu • f n)
    (hBoundary : ∀ n,
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (A.approximate n psi) =
        periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
          (halfExtent n) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
            (halfExtent n) 2 (f n))
          (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
            (halfExtent n) 2 su2BoundaryPairCommonCarrierTwoRankPositive
              (beta n) (hbeta n)))
    (hClosure : ∀ n,
      Q.PhysicalTransferModePositiveTimeSubmoduleBoundaryPairClosureAt
        hInvariant C n (f n)) :
    T.toPhysicalSemigroup.operator 1 psi = mu • psi := by
  exact
    physicalOperator_one_apply_of_normalizedPhysicalTransferModePositiveTimeBoundaryPairClosure
      A psi f (fun _ => mu) mu tendsto_const_nhds hf hBoundary hClosure

/-- Positive cutoff SU(2) physical transfer eigenvalues converging to a positive
continuum value generate an actual graph-closed vacuum-orthogonal OS
Hamiltonian mode.

All finite operator eigen-equations are theorem-generated from the physical
one-slice transfer equations, common-carrier boundary identification, and the
post-synthesis boundary-pair closure condition.  The unbounded Hamiltonian
domain/action is then generated by the already-canonical one-step mode theorem. -/
theorem exists_vacuumOrthogonalClosedRightHamiltonian_mode_of_normalizedPhysicalTransferModePositiveTimeBoundaryPairClosure
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer S D halfExtent 2 su2BoundaryPairCommonCarrierTwoRankPositive beta hbeta Q.toWeakStarBridge hInvariant P T C G)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hHamiltonianSymmetric : T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian)
    (psi : P.VacuumOrthogonalHilbert)
    (f : (n : ℕ) → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (halfExtent n) 2)
    (mu : ℕ → ℝ) (muLimit : ℝ) (hmuLimit : 0 < muLimit)
    (hmu : Tendsto mu atTop (𝓝 muLimit))
    (hf : ∀ n, periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator (halfExtent n) 2 su2BoundaryPairCommonCarrierTwoRankPositive (beta n) (hbeta n) (f n) = mu n • f n)
    (hBoundary : ∀ n, Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n (A.approximate n (psi : P.PhysicalHilbert)) = periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2 (halfExtent n) 2 (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp (halfExtent n) 2 (f n)) (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp (halfExtent n) 2 su2BoundaryPairCommonCarrierTwoRankPositive (beta n) (hbeta n)))
    (hClosure : ∀ n, Q.PhysicalTransferModePositiveTimeSubmoduleBoundaryPairClosureAt hInvariant C n (f n)) :
    ∃ z : (T.vacuumOrthogonalClosedRightHamiltonian hHamiltonianSymmetric).domain,
      (z : P.VacuumOrthogonalHilbert) = psi ∧ T.vacuumOrthogonalClosedRightHamiltonian hHamiltonianSymmetric z = (-Real.log muLimit) • psi := by
  apply exists_vacuumOrthogonalClosedRightHamiltonian_mode_of_approximating_eigen
    A hInnerSymmetric hHamiltonianSymmetric psi mu muLimit hmuLimit hmu
  intro n
  exact
    finiteOperator_one_apply_approximate_of_normalizedPhysicalTransferModePositiveTimeBoundaryPairClosure
      A (psi : P.PhysicalHilbert) n (f n) (mu n)
        (hf n) (hBoundary n) (hClosure n)

end SU2BoundaryPairCommonCarrier

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
