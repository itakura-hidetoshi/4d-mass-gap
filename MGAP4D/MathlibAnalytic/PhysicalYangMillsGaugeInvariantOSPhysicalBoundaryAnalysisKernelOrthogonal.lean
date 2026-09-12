import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalBoundarySynthesisRangeClosure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance physicalBoundaryAnalysisKernelOrthogonalSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance physicalBoundaryAnalysisKernelOrthogonalSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalBoundaryAnalysisKernelOrthogonalSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalBoundaryAnalysisKernelOrthogonalSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalBoundaryAnalysisKernelOrthogonalSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalBoundaryAnalysisKernelOrthogonalSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- The actual Wilson open-half analysis restricted to the completed physical
OS Hilbert space through the canonical boundary isometry `J_n`. -/
noncomputable def actualBoundaryAnalysisOnPhysicalHilbert
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n →L[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N) :=
  (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
      (halfExtent n) N hN (beta n) (hbeta n)).comp
    (L.completedLinearIsometry n).toContinuousLinearMap

/-- The completed physical boundary image lies in the orthogonal complement of
the kernel of the actual Wilson analysis operator.

This is the Hilbert-space form of the synthesis-range closure theorem: for any
bounded operator `A`, `ker(A)⊥ = closure(range(A†))`.  Thus no physical OS
boundary vector is lost in a direction invisible to `A` except the zero
vector. -/
theorem completedLinearIsometry_mem_actualBoundaryAnalysis_orthogonal_ker
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n) :
    L.completedLinearIsometry n psi ∈
      (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        (halfExtent n) N hN (beta n) (hbeta n)).kerᗮ := by
  let A :=
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
      (halfExtent n) N hN (beta n) (hbeta n)
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  change UniformSpace.Completion Pn.Separated at psi
  refine UniformSpace.Completion.induction_on psi
    (A.ker.isClosed_orthogonal.preimage (L.completedLinearMap n).continuous) ?_
  intro x
  rcases SeparationQuotient.surjective_mk x with ⟨F, rfl⟩
  change L.completedLinearMap n
      ((SeparationQuotient.mk F : Pn.Separated) :
        UniformSpace.Completion Pn.Separated) ∈ A.kerᗮ
  rw [L.completedLinearMap_coe, L.separatedLinearIsometry_mk]
  rw [ContinuousLinearMap.orthogonal_ker A]
  apply (A†).range.le_topologicalClosure
  refine ⟨physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
    S D halfExtent N hN beta hbeta B hInvariant n F, ?_⟩
  simpa [A, physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator,
    periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator] using
    (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis
      S D halfExtent N hN beta hbeta B hInvariant n F).symm

/-- The actual Wilson analysis, restricted through the canonical physical
boundary isometry, is injective.

This removes only the null-space obstruction.  It does not imply closed range,
a bounded inverse, or any uniform coercive lower bound for the static analysis
operator. -/
theorem actualBoundaryAnalysisOnPhysicalHilbert_injective
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    Function.Injective (L.actualBoundaryAnalysisOnPhysicalHilbert n) := by
  intro psi phi hEq
  let A :=
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
      (halfExtent n) N hN (beta n) (hbeta n)
  have hzero :
      A (L.completedLinearIsometry n (psi - phi)) = 0 := by
    change L.actualBoundaryAnalysisOnPhysicalHilbert n (psi - phi) = 0
    rw [map_sub, hEq, sub_self]
  have hker : L.completedLinearIsometry n (psi - phi) ∈ A.ker := by
    exact hzero
  have horth : L.completedLinearIsometry n (psi - phi) ∈ A.kerᗮ := by
    exact L.completedLinearIsometry_mem_actualBoundaryAnalysis_orthogonal_ker
      n (psi - phi)
  have hinner :
      inner ℝ
        (L.completedLinearIsometry n (psi - phi))
        (L.completedLinearIsometry n (psi - phi)) = 0 :=
    Submodule.inner_left_of_mem_orthogonal hker horth
  have hJzero : L.completedLinearIsometry n (psi - phi) = 0 :=
    inner_self_eq_zero.mp hinner
  have hsubzero : psi - phi = 0 := by
    apply (L.completedLinearIsometry n).injective
    simpa using hJzero
  exact sub_eq_zero.mp hsubzero

/-- Every nonzero physical OS vector has strictly positive actual Wilson
open-half analysis norm.  This is qualitative nondegeneracy only; no Poincare
or scale-uniform coercive constant is inferred. -/
theorem actualBoundaryAnalysisOnPhysicalHilbert_norm_pos
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    {psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n}
    (hpsi : psi ≠ 0) :
    0 < ‖L.actualBoundaryAnalysisOnPhysicalHilbert n psi‖ := by
  apply norm_pos_iff.mpr
  intro hzero
  apply hpsi
  apply L.actualBoundaryAnalysisOnPhysicalHilbert_injective n
  simpa using hzero

/-- Consequently the static actual Wilson Gram factor `A† A` has strictly
positive quadratic form on every nonzero vector in the physical boundary
image.

This remains qualitative.  In particular it does not promote the static
Hilbert--Schmidt analysis operator to a global bounded-below map.  The physical
mass-gap frontier remains the model-derived time-transfer/reflected Wilson
quadratic decay estimate on the vacuum-orthogonal sector. -/
theorem actualBoundaryGramFactorizedOperator_inner_physical_pos
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    {psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n}
    (hpsi : psi ≠ 0) :
    0 < inner ℝ
      (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
        (halfExtent n) N hN (beta n) (hbeta n)
        (L.completedLinearIsometry n psi))
      (L.completedLinearIsometry n psi) := by
  rw [periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner_self]
  have hnorm := L.actualBoundaryAnalysisOnPhysicalHilbert_norm_pos n hpsi
  change 0 < ‖L.actualBoundaryAnalysisOnPhysicalHilbert n psi‖ ^ 2
  exact pow_pos hnorm 2

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

end MathlibAnalytic
end MGAP4D

end
