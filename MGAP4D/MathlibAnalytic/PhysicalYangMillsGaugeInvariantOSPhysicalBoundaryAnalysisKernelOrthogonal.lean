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
  apply Submodule.subset_topologicalClosure
  refine ⟨physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
    S D halfExtent N hN beta hbeta B hInvariant n F, ?_⟩
  simpa [A, physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator,
    periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator] using
    (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis
      S D halfExtent N hN beta hbeta B hInvariant n F).symm

/-- The actual Wilson analysis, restricted through the canonical physical
boundary isometry, is injective.

No quantitative lower bound is asserted: this theorem removes only the null
space obstruction.  The remaining model-facing estimate is a positive lower
bound for this injective map on the relevant normalized physical sector. -/
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
    Submodule.inner_left_of_mem_orthogonal horth hker
  have hJzero : L.completedLinearIsometry n (psi - phi) = 0 :=
    inner_self_eq_zero.mp hinner
  have hsubzero : psi - phi = 0 :=
    (L.completedLinearIsometry n).injective hJzero
  exact sub_eq_zero.mp hsubzero

/-- Every nonzero physical OS vector has strictly positive actual Wilson
open-half analysis norm.  This is qualitative nondegeneracy, not yet a
Poincare/coercive lower bound uniform over unit vectors or lattice scales. -/
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
  exact hpsi (L.actualBoundaryAnalysisOnPhysicalHilbert_injective n hzero)

/-- Consequently the static actual Wilson Gram factor `A† A` has strictly
positive quadratic form on every nonzero vector in the physical boundary
image.

This isolates the remaining analytic frontier exactly: turn this qualitative
strict positivity into a quantitative lower bound `c_n ‖psi‖²`, and then
control `c_n` along the continuum scaling sequence. -/
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
