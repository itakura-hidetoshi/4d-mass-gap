import MGAP4D.MathlibAnalytic.PhysicalYangMillsR4IntrinsicOptimalComponentBudget
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- A genuine nonzero vacuum-orthogonal physical excitation bounds every
admissible lower coefficient from above by the component Rayleigh quotient of
that one state.  Hence no additional numerical upper bound is needed. -/
theorem physicalYangMillsComponentLowerBoundSet_bddAbove
    (T : P.StronglyContinuousPhysicalSemigroup)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (q : T.closedRightHamiltonian.domain → ℝ) :
    BddAbove (T.physicalYangMillsComponentLowerBoundSet q) := by
  have hnorm_pos : 0 < ‖(W.state : P.PhysicalHilbert)‖ :=
    norm_pos_iff.mpr W.state_ne_zero
  have hnorm_sq_pos : 0 < ‖(W.state : P.PhysicalHilbert)‖ ^ 2 := by
    positivity
  refine ⟨q W.state / ‖(W.state : P.PhysicalHilbert)‖ ^ 2, ?_⟩
  intro c hc
  apply (le_div_iff₀ hnorm_sq_pos).2
  exact hc W.state W.state_ne_zero W.state_orthogonal

/-- The same genuine excitation bounds every admissible upper coefficient from
below by its component Rayleigh quotient. -/
theorem physicalYangMillsComponentUpperBoundSet_bddBelow
    (T : P.StronglyContinuousPhysicalSemigroup)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (q : T.closedRightHamiltonian.domain → ℝ) :
    BddBelow (T.physicalYangMillsComponentUpperBoundSet q) := by
  have hnorm_pos : 0 < ‖(W.state : P.PhysicalHilbert)‖ :=
    norm_pos_iff.mpr W.state_ne_zero
  have hnorm_sq_pos : 0 < ‖(W.state : P.PhysicalHilbert)‖ ^ 2 := by
    positivity
  refine ⟨q W.state / ‖(W.state : P.PhysicalHilbert)‖ ^ 2, ?_⟩
  intro c hc
  apply (div_le_iff₀ hnorm_sq_pos).2
  exact hc W.state W.state_ne_zero W.state_orthogonal

/-- Canonical optimal lower coefficient of one actual quadratic-form component:
the supremum of all valid uniform lower coefficients. -/
noncomputable def physicalYangMillsComponentCanonicalLowerCoefficient
    (T : P.StronglyContinuousPhysicalSemigroup)
    (q : T.closedRightHamiltonian.domain → ℝ) : ℝ :=
  sSup (T.physicalYangMillsComponentLowerBoundSet q)

/-- Canonical optimal upper coefficient of one actual quadratic-form component:
the infimum of all valid uniform upper coefficients. -/
noncomputable def physicalYangMillsComponentCanonicalUpperCoefficient
    (T : P.StronglyContinuousPhysicalSemigroup)
    (q : T.closedRightHamiltonian.domain → ℝ) : ℝ :=
  sInf (T.physicalYangMillsComponentUpperBoundSet q)

/-- If the lower-coefficient set is nonempty, its canonical `sSup` is not only a
supremum but is itself a valid lower coefficient, hence is the greatest member
of the set.  Closedness is obtained directly from the pointwise inequalities. -/
theorem physicalYangMillsComponentCanonicalLower_isGreatest
    (T : P.StronglyContinuousPhysicalSemigroup)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (q : T.closedRightHamiltonian.domain → ℝ)
    (hNonempty : (T.physicalYangMillsComponentLowerBoundSet q).Nonempty) :
    IsGreatest
      (T.physicalYangMillsComponentLowerBoundSet q)
      (T.physicalYangMillsComponentCanonicalLowerCoefficient q) := by
  refine ⟨?_, ?_⟩
  · intro psi hpsi horthogonal
    have hnorm_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ :=
      norm_pos_iff.mpr hpsi
    have hnorm_sq_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
      positivity
    have hs :
        T.physicalYangMillsComponentCanonicalLowerCoefficient q ≤
          q psi / ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
      unfold physicalYangMillsComponentCanonicalLowerCoefficient
      apply csSup_le hNonempty
      intro c hc
      apply (le_div_iff₀ hnorm_sq_pos).2
      exact hc psi hpsi horthogonal
    exact (le_div_iff₀ hnorm_sq_pos).1 hs
  · intro c hc
    unfold physicalYangMillsComponentCanonicalLowerCoefficient
    exact le_csSup (T.physicalYangMillsComponentLowerBoundSet_bddAbove W q) hc

/-- Dually, a nonempty upper-coefficient set has its canonical `sInf` as an
actual least valid upper coefficient. -/
theorem physicalYangMillsComponentCanonicalUpper_isLeast
    (T : P.StronglyContinuousPhysicalSemigroup)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (q : T.closedRightHamiltonian.domain → ℝ)
    (hNonempty : (T.physicalYangMillsComponentUpperBoundSet q).Nonempty) :
    IsLeast
      (T.physicalYangMillsComponentUpperBoundSet q)
      (T.physicalYangMillsComponentCanonicalUpperCoefficient q) := by
  refine ⟨?_, ?_⟩
  · intro psi hpsi horthogonal
    have hnorm_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ :=
      norm_pos_iff.mpr hpsi
    have hnorm_sq_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
      positivity
    have hs :
        q psi / ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
          T.physicalYangMillsComponentCanonicalUpperCoefficient q := by
      unfold physicalYangMillsComponentCanonicalUpperCoefficient
      apply le_csInf hNonempty
      intro c hc
      apply (div_le_iff₀ hnorm_sq_pos).2
      exact hc psi hpsi horthogonal
    exact (div_le_iff₀ hnorm_sq_pos).1 hs
  · intro c hc
    unfold physicalYangMillsComponentCanonicalUpperCoefficient
    exact csInf_le (T.physicalYangMillsComponentUpperBoundSet_bddBelow W q) hc

/-- The only extra analytic input needed to construct all six canonical R4
component optima is nonemptiness of the appropriate coefficient sets.

These are form-boundedness obligations; this structure contains no coefficient
values and no exact target number. -/
structure PhysicalYangMillsR4ComponentBoundednessData
    {T : P.StronglyContinuousPhysicalSemigroup}
    (A : T.PhysicalYangMillsR4NormalizedFormDecomposition) where
  baseLower_nonempty :
    (T.physicalYangMillsComponentLowerBoundSet A.qBase).Nonempty
  curvatureLower_nonempty :
    (T.physicalYangMillsComponentLowerBoundSet A.qCurvature).Nonempty
  interactionPositiveLower_nonempty :
    (T.physicalYangMillsComponentLowerBoundSet A.qInteractionPositive).Nonempty
  interactionLeakUpper_nonempty :
    (T.physicalYangMillsComponentUpperBoundSet A.qInteractionLeak).Nonempty
  boundaryErrorUpper_nonempty :
    (T.physicalYangMillsComponentUpperBoundSet A.qBoundaryError).Nonempty
  regularizationErrorUpper_nonempty :
    (T.physicalYangMillsComponentUpperBoundSet A.qRegularizationError).Nonempty

namespace PhysicalYangMillsR4ComponentBoundednessData

variable {T : P.StronglyContinuousPhysicalSemigroup}
variable {A : T.PhysicalYangMillsR4NormalizedFormDecomposition}

/-- Canonically reconstruct the six intrinsic optimal coefficients from the
actual component forms by `sSup`/`sInf`.  No coefficient is selected by a
certificate. -/
noncomputable def toCanonicalOptimalComponentData
    (K : PhysicalYangMillsR4ComponentBoundednessData A)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    T.PhysicalYangMillsR4IntrinsicOptimalComponentData A where
  baseCoefficient :=
    T.physicalYangMillsComponentCanonicalLowerCoefficient A.qBase
  curvatureCoefficient :=
    T.physicalYangMillsComponentCanonicalLowerCoefficient A.qCurvature
  interactionPositiveCoefficient :=
    T.physicalYangMillsComponentCanonicalLowerCoefficient A.qInteractionPositive
  interactionLeakCoefficient :=
    T.physicalYangMillsComponentCanonicalUpperCoefficient A.qInteractionLeak
  boundaryErrorCoefficient :=
    T.physicalYangMillsComponentCanonicalUpperCoefficient A.qBoundaryError
  regularizationErrorCoefficient :=
    T.physicalYangMillsComponentCanonicalUpperCoefficient A.qRegularizationError
  base_isGreatest :=
    T.physicalYangMillsComponentCanonicalLower_isGreatest
      W A.qBase K.baseLower_nonempty
  curvature_isGreatest :=
    T.physicalYangMillsComponentCanonicalLower_isGreatest
      W A.qCurvature K.curvatureLower_nonempty
  interactionPositive_isGreatest :=
    T.physicalYangMillsComponentCanonicalLower_isGreatest
      W A.qInteractionPositive K.interactionPositiveLower_nonempty
  interactionLeak_isLeast :=
    T.physicalYangMillsComponentCanonicalUpper_isLeast
      W A.qInteractionLeak K.interactionLeakUpper_nonempty
  boundaryError_isLeast :=
    T.physicalYangMillsComponentCanonicalUpper_isLeast
      W A.qBoundaryError K.boundaryErrorUpper_nonempty
  regularizationError_isLeast :=
    T.physicalYangMillsComponentCanonicalUpper_isLeast
      W A.qRegularizationError K.regularizationErrorUpper_nonempty

/-- The fully canonical component budget is automatically a lower bound for the
normalized variational Yang--Mills mass. -/
theorem canonicalBudget_le_normalized_physicalYangMillsMass
    (K : PhysicalYangMillsR4ComponentBoundednessData A)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    (K.toCanonicalOptimalComponentData W).budget ≤
      A.referenceTime * T.physicalYangMillsMass := by
  exact (K.toCanonicalOptimalComponentData W).budget_le_normalized_physicalYangMillsMass W

/-- Exact-value endpoint with canonical coefficients: after the actual
Yang--Mills analysis evaluates the six `sSup`/`sInf` coefficients and provides
one state attaining their combined budget, `33/20` is a theorem output. -/
theorem normalized_physicalYangMillsMass_eq_33_over_20_of_canonical_coefficients_and_attainment
    (K : PhysicalYangMillsR4ComponentBoundednessData A)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0)
    (hattain :
      A.referenceTime *
          inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) =
        (K.toCanonicalOptimalComponentData W).budget *
          ‖(psi : P.PhysicalHilbert)‖ ^ 2)
    (hbase :
      T.physicalYangMillsComponentCanonicalLowerCoefficient A.qBase =
        (9 : ℝ) / 5)
    (hcurv :
      T.physicalYangMillsComponentCanonicalLowerCoefficient A.qCurvature =
        (1 : ℝ) / 10)
    (hintpos :
      T.physicalYangMillsComponentCanonicalLowerCoefficient A.qInteractionPositive = 0)
    (hleak :
      T.physicalYangMillsComponentCanonicalUpperCoefficient A.qInteractionLeak =
        (1 : ℝ) / 10)
    (hboundary :
      T.physicalYangMillsComponentCanonicalUpperCoefficient A.qBoundaryError =
        (1 : ℝ) / 20)
    (hreg :
      T.physicalYangMillsComponentCanonicalUpperCoefficient A.qRegularizationError =
        (1 : ℝ) / 10) :
    A.referenceTime * T.physicalYangMillsMass = (33 : ℝ) / 20 := by
  exact
    (K.toCanonicalOptimalComponentData W).
      normalized_physicalYangMillsMass_eq_33_over_20_of_intrinsic_coefficients_and_attainment
        psi hpsi horthogonal hattain hbase hcurv hintpos hleak hboundary hreg

end PhysicalYangMillsR4ComponentBoundednessData

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D