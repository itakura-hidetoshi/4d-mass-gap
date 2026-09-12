import MGAP4D.MathlibAnalytic.PhysicalYangMillsR4CanonicalComponentOptima
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

/-- Actual component Rayleigh values on nonzero vacuum-orthogonal vectors of
the graph-closed physical Yang--Mills Hamiltonian domain. -/
def physicalYangMillsComponentRayleighSet
    (T : P.StronglyContinuousPhysicalSemigroup)
    (q : T.closedRightHamiltonian.domain → ℝ) : Set ℝ :=
  {r | ∃ psi : T.closedRightHamiltonian.domain,
    (psi : P.PhysicalHilbert) ≠ 0 ∧
    inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0 ∧
    r = q psi / ‖(psi : P.PhysicalHilbert)‖ ^ 2}

/-- Any genuine physical excitation produces one actual component Rayleigh
value. -/
theorem physicalYangMillsComponentRayleighSet_nonempty
    (T : P.StronglyContinuousPhysicalSemigroup)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (q : T.closedRightHamiltonian.domain → ℝ) :
    (T.physicalYangMillsComponentRayleighSet q).Nonempty := by
  refine ⟨q W.state / ‖(W.state : P.PhysicalHilbert)‖ ^ 2, ?_⟩
  exact ⟨W.state, W.state_ne_zero, W.state_orthogonal, rfl⟩

/-- Nonemptiness of the uniform lower-coefficient set is exactly enough to
supply a lower bound for the actual component Rayleigh values. -/
theorem physicalYangMillsComponentRayleighSet_bddBelow_of_lowerBoundSet_nonempty
    (T : P.StronglyContinuousPhysicalSemigroup)
    (q : T.closedRightHamiltonian.domain → ℝ)
    (hLower : (T.physicalYangMillsComponentLowerBoundSet q).Nonempty) :
    BddBelow (T.physicalYangMillsComponentRayleighSet q) := by
  rcases hLower with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro r hr
  rcases hr with ⟨psi, hpsi, horthogonal, rfl⟩
  have hnorm_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ :=
    norm_pos_iff.mpr hpsi
  have hnorm_sq_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
    positivity
  apply (le_div_iff₀ hnorm_sq_pos).2
  exact hc psi hpsi horthogonal

/-- Dually, nonemptiness of the uniform upper-coefficient set bounds the
component Rayleigh values from above. -/
theorem physicalYangMillsComponentRayleighSet_bddAbove_of_upperBoundSet_nonempty
    (T : P.StronglyContinuousPhysicalSemigroup)
    (q : T.closedRightHamiltonian.domain → ℝ)
    (hUpper : (T.physicalYangMillsComponentUpperBoundSet q).Nonempty) :
    BddAbove (T.physicalYangMillsComponentRayleighSet q) := by
  rcases hUpper with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro r hr
  rcases hr with ⟨psi, hpsi, horthogonal, rfl⟩
  have hnorm_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ :=
    norm_pos_iff.mpr hpsi
  have hnorm_sq_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
    positivity
  apply (div_le_iff₀ hnorm_sq_pos).2
  exact hc psi hpsi horthogonal

/-- The canonical greatest uniform lower coefficient is exactly the infimum of
the actual component Rayleigh quotient set.

This identifies the order-theoretic coefficient constructed in #1557 with the
usual variational quantity that must be evaluated by the Yang--Mills model. -/
theorem physicalYangMillsComponentCanonicalLowerCoefficient_eq_sInf_rayleighSet
    (T : P.StronglyContinuousPhysicalSemigroup)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (q : T.closedRightHamiltonian.domain → ℝ)
    (hLower : (T.physicalYangMillsComponentLowerBoundSet q).Nonempty) :
    T.physicalYangMillsComponentCanonicalLowerCoefficient q =
      sInf (T.physicalYangMillsComponentRayleighSet q) := by
  have hGreatest :=
    T.physicalYangMillsComponentCanonicalLower_isGreatest W q hLower
  have hRayNonempty := T.physicalYangMillsComponentRayleighSet_nonempty W q
  have hRayBddBelow :=
    T.physicalYangMillsComponentRayleighSet_bddBelow_of_lowerBoundSet_nonempty
      q hLower
  apply le_antisymm
  · apply le_csInf hRayNonempty
    intro r hr
    rcases hr with ⟨psi, hpsi, horthogonal, rfl⟩
    have hnorm_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ :=
      norm_pos_iff.mpr hpsi
    have hnorm_sq_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
      positivity
    apply (le_div_iff₀ hnorm_sq_pos).2
    exact hGreatest.1 psi hpsi horthogonal
  · apply hGreatest.2
    intro psi hpsi horthogonal
    have hnorm_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ :=
      norm_pos_iff.mpr hpsi
    have hnorm_sq_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
      positivity
    have hr :
        q psi / ‖(psi : P.PhysicalHilbert)‖ ^ 2 ∈
          T.physicalYangMillsComponentRayleighSet q := by
      exact ⟨psi, hpsi, horthogonal, rfl⟩
    exact (le_div_iff₀ hnorm_sq_pos).1 (csInf_le hRayBddBelow hr)

/-- The canonical least uniform upper coefficient is exactly the supremum of
the actual component Rayleigh quotient set. -/
theorem physicalYangMillsComponentCanonicalUpperCoefficient_eq_sSup_rayleighSet
    (T : P.StronglyContinuousPhysicalSemigroup)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (q : T.closedRightHamiltonian.domain → ℝ)
    (hUpper : (T.physicalYangMillsComponentUpperBoundSet q).Nonempty) :
    T.physicalYangMillsComponentCanonicalUpperCoefficient q =
      sSup (T.physicalYangMillsComponentRayleighSet q) := by
  have hLeast :=
    T.physicalYangMillsComponentCanonicalUpper_isLeast W q hUpper
  have hRayNonempty := T.physicalYangMillsComponentRayleighSet_nonempty W q
  have hRayBddAbove :=
    T.physicalYangMillsComponentRayleighSet_bddAbove_of_upperBoundSet_nonempty
      q hUpper
  apply le_antisymm
  · apply hLeast.2
    intro psi hpsi horthogonal
    have hnorm_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ :=
      norm_pos_iff.mpr hpsi
    have hnorm_sq_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
      positivity
    have hr :
        q psi / ‖(psi : P.PhysicalHilbert)‖ ^ 2 ∈
          T.physicalYangMillsComponentRayleighSet q := by
      exact ⟨psi, hpsi, horthogonal, rfl⟩
    exact (div_le_iff₀ hnorm_sq_pos).1 (le_csSup hRayBddAbove hr)
  · apply csSup_le hRayNonempty
    intro r hr
    rcases hr with ⟨psi, hpsi, horthogonal, rfl⟩
    have hnorm_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ :=
      norm_pos_iff.mpr hpsi
    have hnorm_sq_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
      positivity
    apply (div_le_iff₀ hnorm_sq_pos).2
    exact hLeast.1 psi hpsi horthogonal

namespace PhysicalYangMillsR4NormalizedFormDecomposition

variable {T : P.StronglyContinuousPhysicalSemigroup}

/-- The R4 normalized budget written directly in terms of extrema of actual
component Rayleigh quotients.  No coefficient certificate occurs in this
definition. -/
noncomputable def rayleighExtremaBudget
    (A : T.PhysicalYangMillsR4NormalizedFormDecomposition) : ℝ :=
  sInf (T.physicalYangMillsComponentRayleighSet A.qBase) +
    sInf (T.physicalYangMillsComponentRayleighSet A.qCurvature) +
    sInf (T.physicalYangMillsComponentRayleighSet A.qInteractionPositive) -
    sSup (T.physicalYangMillsComponentRayleighSet A.qInteractionLeak) -
    sSup (T.physicalYangMillsComponentRayleighSet A.qBoundaryError) -
    sSup (T.physicalYangMillsComponentRayleighSet A.qRegularizationError)

end PhysicalYangMillsR4NormalizedFormDecomposition

namespace PhysicalYangMillsR4ComponentBoundednessData

variable {T : P.StronglyContinuousPhysicalSemigroup}
variable {A : T.PhysicalYangMillsR4NormalizedFormDecomposition}

/-- The canonical budget reconstructed in #1557 is definitionally independent
of coefficients and equals the direct variational budget of component Rayleigh
extrema. -/
theorem canonicalBudget_eq_rayleighExtremaBudget
    (K : PhysicalYangMillsR4ComponentBoundednessData A)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    (K.toCanonicalOptimalComponentData W).budget = A.rayleighExtremaBudget := by
  unfold PhysicalYangMillsR4IntrinsicOptimalComponentData.budget
  unfold PhysicalYangMillsR4NormalizedFormDecomposition.rayleighExtremaBudget
  change
    T.physicalYangMillsComponentCanonicalLowerCoefficient A.qBase +
      T.physicalYangMillsComponentCanonicalLowerCoefficient A.qCurvature +
      T.physicalYangMillsComponentCanonicalLowerCoefficient A.qInteractionPositive -
      T.physicalYangMillsComponentCanonicalUpperCoefficient A.qInteractionLeak -
      T.physicalYangMillsComponentCanonicalUpperCoefficient A.qBoundaryError -
      T.physicalYangMillsComponentCanonicalUpperCoefficient A.qRegularizationError = _
  rw [T.physicalYangMillsComponentCanonicalLowerCoefficient_eq_sInf_rayleighSet
        W A.qBase K.baseLower_nonempty,
      T.physicalYangMillsComponentCanonicalLowerCoefficient_eq_sInf_rayleighSet
        W A.qCurvature K.curvatureLower_nonempty,
      T.physicalYangMillsComponentCanonicalLowerCoefficient_eq_sInf_rayleighSet
        W A.qInteractionPositive K.interactionPositiveLower_nonempty,
      T.physicalYangMillsComponentCanonicalUpperCoefficient_eq_sSup_rayleighSet
        W A.qInteractionLeak K.interactionLeakUpper_nonempty,
      T.physicalYangMillsComponentCanonicalUpperCoefficient_eq_sSup_rayleighSet
        W A.qBoundaryError K.boundaryErrorUpper_nonempty,
      T.physicalYangMillsComponentCanonicalUpperCoefficient_eq_sSup_rayleighSet
        W A.qRegularizationError K.regularizationErrorUpper_nonempty]

/-- Exact normalized mass theorem whose numerical hypotheses are now stated
only as extrema of actual component Rayleigh quotients.

Thus the remaining `9/5`, `1/10`, `1/20` obligations are genuine variational
calculations on the constructed Yang--Mills Hamiltonian components, not stored
component coefficients. -/
theorem normalized_physicalYangMillsMass_eq_33_over_20_of_component_rayleigh_extrema_and_attainment
    (K : PhysicalYangMillsR4ComponentBoundednessData A)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0)
    (hattain :
      A.referenceTime *
          inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) =
        A.rayleighExtremaBudget * ‖(psi : P.PhysicalHilbert)‖ ^ 2)
    (hbase :
      sInf (T.physicalYangMillsComponentRayleighSet A.qBase) = (9 : ℝ) / 5)
    (hcurv :
      sInf (T.physicalYangMillsComponentRayleighSet A.qCurvature) = (1 : ℝ) / 10)
    (hintpos :
      sInf (T.physicalYangMillsComponentRayleighSet A.qInteractionPositive) = 0)
    (hleak :
      sSup (T.physicalYangMillsComponentRayleighSet A.qInteractionLeak) = (1 : ℝ) / 10)
    (hboundary :
      sSup (T.physicalYangMillsComponentRayleighSet A.qBoundaryError) = (1 : ℝ) / 20)
    (hreg :
      sSup (T.physicalYangMillsComponentRayleighSet A.qRegularizationError) = (1 : ℝ) / 10) :
    A.referenceTime * T.physicalYangMillsMass = (33 : ℝ) / 20 := by
  have hbudget := K.canonicalBudget_eq_rayleighExtremaBudget W
  have hattainCanonical :
      A.referenceTime *
          inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) =
        (K.toCanonicalOptimalComponentData W).budget *
          ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
    rw [hbudget]
    exact hattain
  have hbaseCanonical :
      T.physicalYangMillsComponentCanonicalLowerCoefficient A.qBase = (9 : ℝ) / 5 := by
    rw [T.physicalYangMillsComponentCanonicalLowerCoefficient_eq_sInf_rayleighSet
      W A.qBase K.baseLower_nonempty]
    exact hbase
  have hcurvCanonical :
      T.physicalYangMillsComponentCanonicalLowerCoefficient A.qCurvature = (1 : ℝ) / 10 := by
    rw [T.physicalYangMillsComponentCanonicalLowerCoefficient_eq_sInf_rayleighSet
      W A.qCurvature K.curvatureLower_nonempty]
    exact hcurv
  have hintposCanonical :
      T.physicalYangMillsComponentCanonicalLowerCoefficient A.qInteractionPositive = 0 := by
    rw [T.physicalYangMillsComponentCanonicalLowerCoefficient_eq_sInf_rayleighSet
      W A.qInteractionPositive K.interactionPositiveLower_nonempty]
    exact hintpos
  have hleakCanonical :
      T.physicalYangMillsComponentCanonicalUpperCoefficient A.qInteractionLeak = (1 : ℝ) / 10 := by
    rw [T.physicalYangMillsComponentCanonicalUpperCoefficient_eq_sSup_rayleighSet
      W A.qInteractionLeak K.interactionLeakUpper_nonempty]
    exact hleak
  have hboundaryCanonical :
      T.physicalYangMillsComponentCanonicalUpperCoefficient A.qBoundaryError = (1 : ℝ) / 20 := by
    rw [T.physicalYangMillsComponentCanonicalUpperCoefficient_eq_sSup_rayleighSet
      W A.qBoundaryError K.boundaryErrorUpper_nonempty]
    exact hboundary
  have hregCanonical :
      T.physicalYangMillsComponentCanonicalUpperCoefficient A.qRegularizationError = (1 : ℝ) / 10 := by
    rw [T.physicalYangMillsComponentCanonicalUpperCoefficient_eq_sSup_rayleighSet
      W A.qRegularizationError K.regularizationErrorUpper_nonempty]
    exact hreg
  exact K.normalized_physicalYangMillsMass_eq_33_over_20_of_canonical_coefficients_and_attainment
    W psi hpsi horthogonal hattainCanonical hbaseCanonical hcurvCanonical
      hintposCanonical hleakCanonical hboundaryCanonical hregCanonical

end PhysicalYangMillsR4ComponentBoundednessData

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D