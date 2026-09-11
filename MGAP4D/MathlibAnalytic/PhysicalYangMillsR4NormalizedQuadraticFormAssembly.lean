import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSOptimalRayleighCoercivity
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

/-- Proof-relevant normalized quadratic-form decomposition on the **actual
 graph-closed OS Yang--Mills Hamiltonian**.

The reference time makes every coefficient dimensionless.  The structure does
not contain the target `33/20`.  Instead it carries the six component forms and
the old R4 component estimates individually:

* base coercivity: `9/5`;
* curvature contribution: `1/10`;
* positive interaction: nonnegative;
* interaction leakage: at most `1/10`;
* boundary error: at most `1/20`;
* regularization error: at most `1/10`.

Only an actual Yang--Mills construction of these fields can instantiate this
package.  The exact final coefficient is theorem-generated below by rational
assembly. -/
structure PhysicalYangMillsR4NormalizedQuadraticFormData
    (T : P.StronglyContinuousPhysicalSemigroup) where
  referenceTime : ℝ
  referenceTime_pos : 0 < referenceTime
  qBase : T.closedRightHamiltonian.domain → ℝ
  qCurvature : T.closedRightHamiltonian.domain → ℝ
  qInteractionPositive : T.closedRightHamiltonian.domain → ℝ
  qInteractionLeak : T.closedRightHamiltonian.domain → ℝ
  qBoundaryError : T.closedRightHamiltonian.domain → ℝ
  qRegularizationError : T.closedRightHamiltonian.domain → ℝ
  decomposition : ∀ psi : T.closedRightHamiltonian.domain,
    referenceTime *
        inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) =
      qBase psi + qCurvature psi + qInteractionPositive psi -
        qInteractionLeak psi - qBoundaryError psi - qRegularizationError psi
  base_lower : ∀ psi : T.closedRightHamiltonian.domain,
    inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0 →
      ((9 : ℝ) / 5) * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤ qBase psi
  curvature_lower : ∀ psi : T.closedRightHamiltonian.domain,
    inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0 →
      ((1 : ℝ) / 10) * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤ qCurvature psi
  interactionPositive_nonneg : ∀ psi : T.closedRightHamiltonian.domain,
    inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0 →
      0 ≤ qInteractionPositive psi
  interactionLeak_upper : ∀ psi : T.closedRightHamiltonian.domain,
    inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0 →
      qInteractionLeak psi ≤ ((1 : ℝ) / 10) * ‖(psi : P.PhysicalHilbert)‖ ^ 2
  boundaryError_upper : ∀ psi : T.closedRightHamiltonian.domain,
    inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0 →
      qBoundaryError psi ≤ ((1 : ℝ) / 20) * ‖(psi : P.PhysicalHilbert)‖ ^ 2
  regularizationError_upper : ∀ psi : T.closedRightHamiltonian.domain,
    inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0 →
      qRegularizationError psi ≤ ((1 : ℝ) / 10) * ‖(psi : P.PhysicalHilbert)‖ ^ 2

namespace PhysicalYangMillsR4NormalizedQuadraticFormData

variable {T : P.StronglyContinuousPhysicalSemigroup}

/-- The exact R4 rational budget is generated from its component estimates:

`9/5 + 1/10 - 1/10 - 1/20 - 1/10 = 33/20`.

The target coefficient is not a field of the data structure. -/
theorem normalized_inner_ge_33_over_20_mul_norm_sq
    (A : T.PhysicalYangMillsR4NormalizedQuadraticFormData)
    (psi : T.closedRightHamiltonian.domain)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    ((33 : ℝ) / 20) * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      A.referenceTime *
        inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  have hbase := A.base_lower psi horthogonal
  have hcurv := A.curvature_lower psi horthogonal
  have hintpos := A.interactionPositive_nonneg psi horthogonal
  have hleak := A.interactionLeak_upper psi horthogonal
  have hboundary := A.boundaryError_upper psi horthogonal
  have hreg := A.regularizationError_upper psi horthogonal
  rw [A.decomposition psi]
  linarith

/-- Dividing by the positive model-derived reference time turns the assembled
normalized R4 coefficient into an actual Rayleigh lower bound for the graph-
closed physical Hamiltonian. -/
theorem divided_33_over_20_mem_physicalYangMillsRayleighLowerBoundSet
    (A : T.PhysicalYangMillsR4NormalizedQuadraticFormData) :
    (((33 : ℝ) / 20) / A.referenceTime) ∈
      T.physicalYangMillsRayleighLowerBoundSet := by
  intro psi _hpsi horthogonal
  have h := A.normalized_inner_ge_33_over_20_mul_norm_sq psi horthogonal
  have hdiv :
      (((33 : ℝ) / 20) * ‖(psi : P.PhysicalHilbert)‖ ^ 2) /
          A.referenceTime ≤
        inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) := by
    apply (div_le_iff₀ A.referenceTime_pos).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  calc
    (((33 : ℝ) / 20) / A.referenceTime) *
          ‖(psi : P.PhysicalHilbert)‖ ^ 2 =
        (((33 : ℝ) / 20) * ‖(psi : P.PhysicalHilbert)‖ ^ 2) /
          A.referenceTime := by ring
    _ ≤ inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) := hdiv

/-- With a genuine nonzero physical excitation-domain witness, the actual
variational mass obeys the normalized lower bound

`33/20 <= referenceTime * physicalYangMillsMass`.

Thus `33/20` is a consequence of the component form budget rather than an input
mass value. -/
theorem thirtyThree_over_twenty_le_normalized_physicalYangMillsMass
    (A : T.PhysicalYangMillsR4NormalizedQuadraticFormData)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    ((33 : ℝ) / 20) ≤ A.referenceTime * T.physicalYangMillsMass := by
  have hlower :
      ((33 : ℝ) / 20) / A.referenceTime ≤ T.physicalYangMillsMass :=
    T.rayleighLowerBound_le_physicalYangMillsMass W
      A.divided_33_over_20_mem_physicalYangMillsRayleighLowerBoundSet
  have hmul := mul_le_mul_of_nonneg_left hlower A.referenceTime_pos.le
  calc
    ((33 : ℝ) / 20) =
        A.referenceTime * (((33 : ℝ) / 20) / A.referenceTime) := by
      field_simp [ne_of_gt A.referenceTime_pos]
    _ ≤ A.referenceTime * T.physicalYangMillsMass := hmul

/-- A state saturating every component of the R4 budget theorem-generates the
normalized quadratic-form value `33/20`; the final rational number is not
assumed in the saturation hypotheses. -/
theorem normalized_inner_eq_33_over_20_mul_norm_sq_of_component_saturation
    (A : T.PhysicalYangMillsR4NormalizedQuadraticFormData)
    (psi : T.closedRightHamiltonian.domain)
    (hbase : A.qBase psi = ((9 : ℝ) / 5) * ‖(psi : P.PhysicalHilbert)‖ ^ 2)
    (hcurv : A.qCurvature psi = ((1 : ℝ) / 10) * ‖(psi : P.PhysicalHilbert)‖ ^ 2)
    (hintpos : A.qInteractionPositive psi = 0)
    (hleak : A.qInteractionLeak psi = ((1 : ℝ) / 10) * ‖(psi : P.PhysicalHilbert)‖ ^ 2)
    (hboundary : A.qBoundaryError psi = ((1 : ℝ) / 20) * ‖(psi : P.PhysicalHilbert)‖ ^ 2)
    (hreg : A.qRegularizationError psi = ((1 : ℝ) / 10) * ‖(psi : P.PhysicalHilbert)‖ ^ 2) :
    A.referenceTime *
        inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) =
      ((33 : ℝ) / 20) * ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
  rw [A.decomposition psi, hbase, hcurv, hintpos, hleak, hboundary, hreg]
  ring

/-- If an actual nonzero vacuum-orthogonal physical excitation saturates all six
component estimates, then the normalized variational Yang--Mills mass is
exactly `33/20`.

All occurrences of the final number are theorem outputs from the component
budget.  The hypotheses name only the independent component constants and an
actual state of the graph-closed Hamiltonian. -/
theorem normalized_physicalYangMillsMass_eq_33_over_20_of_component_saturation
    (A : T.PhysicalYangMillsR4NormalizedQuadraticFormData)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0)
    (hbase : A.qBase psi = ((9 : ℝ) / 5) * ‖(psi : P.PhysicalHilbert)‖ ^ 2)
    (hcurv : A.qCurvature psi = ((1 : ℝ) / 10) * ‖(psi : P.PhysicalHilbert)‖ ^ 2)
    (hintpos : A.qInteractionPositive psi = 0)
    (hleak : A.qInteractionLeak psi = ((1 : ℝ) / 10) * ‖(psi : P.PhysicalHilbert)‖ ^ 2)
    (hboundary : A.qBoundaryError psi = ((1 : ℝ) / 20) * ‖(psi : P.PhysicalHilbert)‖ ^ 2)
    (hreg : A.qRegularizationError psi = ((1 : ℝ) / 10) * ‖(psi : P.PhysicalHilbert)‖ ^ 2) :
    A.referenceTime * T.physicalYangMillsMass = (33 : ℝ) / 20 := by
  let lambda : ℝ := ((33 : ℝ) / 20) / A.referenceTime
  have hnorm_sq_ne : ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≠ 0 := by
    have hnorm : 0 < ‖(psi : P.PhysicalHilbert)‖ := norm_pos_iff.mpr hpsi
    positivity
  have hnormalized :=
    A.normalized_inner_eq_33_over_20_mul_norm_sq_of_component_saturation
      psi hbase hcurv hintpos hleak hboundary hreg
  have hinner :
      inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) =
        lambda * ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
    dsimp [lambda]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (ne_of_gt A.referenceTime_pos)).2
    simpa [mul_comm] using hnormalized
  have hattained : T.physicalYangMillsClosedRayleighQuotient psi = lambda := by
    unfold PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.StronglyContinuousPhysicalSemigroup.physicalYangMillsClosedRayleighQuotient
    rw [hinner]
    field_simp [hnorm_sq_ne]
  have hlower :
      ∀ phi : T.closedRightHamiltonian.domain,
        (phi : P.PhysicalHilbert) ≠ 0 →
        inner ℝ (phi : P.PhysicalHilbert) P.vacuum = 0 →
        lambda * ‖(phi : P.PhysicalHilbert)‖ ^ 2 ≤
          inner ℝ (T.closedRightHamiltonian phi) (phi : P.PhysicalHilbert) := by
    intro phi _hphi hphiOrth
    exact A.divided_33_over_20_mem_physicalYangMillsRayleighLowerBoundSet
      _ _hphi hphiOrth
  have hmass : T.physicalYangMillsMass = lambda :=
    T.physicalYangMillsMass_eq_of_uniformRayleighLowerBound_of_attained
      psi hpsi horthogonal hattained hlower
  rw [hmass]
  dsimp [lambda]
  field_simp [ne_of_gt A.referenceTime_pos]

end PhysicalYangMillsR4NormalizedQuadraticFormData

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D