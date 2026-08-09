import MGAP4D.MathlibAnalytic.PhysicalYangMillsR4NormalizedQuadraticFormAssembly
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

/-- Admissible lower coefficients for one real quadratic-form component on the
actual nonzero vacuum-orthogonal graph-closed Hamiltonian domain. -/
def physicalYangMillsComponentLowerBoundSet
    (T : P.StronglyContinuousPhysicalSemigroup)
    (q : T.closedRightHamiltonian.domain → ℝ) : Set ℝ :=
  {c | ∀ psi : T.closedRightHamiltonian.domain,
    (psi : P.PhysicalHilbert) ≠ 0 →
    inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0 →
      c * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤ q psi}

/-- Admissible upper coefficients for one real quadratic-form component on the
actual nonzero vacuum-orthogonal graph-closed Hamiltonian domain. -/
def physicalYangMillsComponentUpperBoundSet
    (T : P.StronglyContinuousPhysicalSemigroup)
    (q : T.closedRightHamiltonian.domain → ℝ) : Set ℝ :=
  {c | ∀ psi : T.closedRightHamiltonian.domain,
    (psi : P.PhysicalHilbert) ≠ 0 →
    inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0 →
      q psi ≤ c * ‖(psi : P.PhysicalHilbert)‖ ^ 2}

/-- A normalized decomposition of the actual graph-closed physical Hamiltonian
into the six R4 component forms, without any numerical component bound.

All quantitative coefficients are moved to the intrinsic optimality package
below, so neither `33/20` nor `9/5`, `1/10`, `1/20` is part of this model data. -/
structure PhysicalYangMillsR4NormalizedFormDecomposition
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

/-- Intrinsic optimal coefficients of the six actual R4 component forms.

Positive components carry the **greatest** valid lower coefficient; subtractive
error components carry the **least** valid upper coefficient.  Hence the six
numbers are uniquely determined by the component forms rather than freely
selected certificate parameters. -/
structure PhysicalYangMillsR4IntrinsicOptimalComponentData
    {T : P.StronglyContinuousPhysicalSemigroup}
    (A : T.PhysicalYangMillsR4NormalizedFormDecomposition) where
  baseCoefficient : ℝ
  curvatureCoefficient : ℝ
  interactionPositiveCoefficient : ℝ
  interactionLeakCoefficient : ℝ
  boundaryErrorCoefficient : ℝ
  regularizationErrorCoefficient : ℝ
  base_isGreatest :
    IsGreatest (T.physicalYangMillsComponentLowerBoundSet A.qBase) baseCoefficient
  curvature_isGreatest :
    IsGreatest
      (T.physicalYangMillsComponentLowerBoundSet A.qCurvature)
      curvatureCoefficient
  interactionPositive_isGreatest :
    IsGreatest
      (T.physicalYangMillsComponentLowerBoundSet A.qInteractionPositive)
      interactionPositiveCoefficient
  interactionLeak_isLeast :
    IsLeast
      (T.physicalYangMillsComponentUpperBoundSet A.qInteractionLeak)
      interactionLeakCoefficient
  boundaryError_isLeast :
    IsLeast
      (T.physicalYangMillsComponentUpperBoundSet A.qBoundaryError)
      boundaryErrorCoefficient
  regularizationError_isLeast :
    IsLeast
      (T.physicalYangMillsComponentUpperBoundSet A.qRegularizationError)
      regularizationErrorCoefficient

namespace PhysicalYangMillsR4IntrinsicOptimalComponentData

variable {T : P.StronglyContinuousPhysicalSemigroup}
variable {A : T.PhysicalYangMillsR4NormalizedFormDecomposition}

/-- The intrinsic normalized R4 coercivity budget assembled from the optimal
component coefficients.  This definition contains no target rational value. -/
def budget (B : PhysicalYangMillsR4IntrinsicOptimalComponentData A) : ℝ :=
  B.baseCoefficient + B.curvatureCoefficient +
    B.interactionPositiveCoefficient - B.interactionLeakCoefficient -
      B.boundaryErrorCoefficient - B.regularizationErrorCoefficient

/-- The intrinsic optimal component budget lower-bounds the normalized actual
physical Hamiltonian quadratic form. -/
theorem normalized_inner_ge_budget_mul_norm_sq
    (B : PhysicalYangMillsR4IntrinsicOptimalComponentData A)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    B.budget * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      A.referenceTime *
        inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  have hbase := B.base_isGreatest.1 psi hpsi horthogonal
  have hcurv := B.curvature_isGreatest.1 psi hpsi horthogonal
  have hintpos := B.interactionPositive_isGreatest.1 psi hpsi horthogonal
  have hleak := B.interactionLeak_isLeast.1 psi hpsi horthogonal
  have hboundary := B.boundaryError_isLeast.1 psi hpsi horthogonal
  have hreg := B.regularizationError_isLeast.1 psi hpsi horthogonal
  rw [A.decomposition psi]
  unfold budget
  nlinarith

/-- Dividing by the positive model-derived reference time makes the intrinsic
component budget an actual graph-closed Hamiltonian Rayleigh lower bound. -/
theorem budget_div_referenceTime_mem_physicalYangMillsRayleighLowerBoundSet
    (B : PhysicalYangMillsR4IntrinsicOptimalComponentData A) :
    (B.budget / A.referenceTime) ∈ T.physicalYangMillsRayleighLowerBoundSet := by
  intro psi hpsi horthogonal
  have h := B.normalized_inner_ge_budget_mul_norm_sq psi hpsi horthogonal
  have hdiv :
      (B.budget * ‖(psi : P.PhysicalHilbert)‖ ^ 2) / A.referenceTime ≤
        inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) := by
    apply (div_le_iff₀ A.referenceTime_pos).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  calc
    (B.budget / A.referenceTime) * ‖(psi : P.PhysicalHilbert)‖ ^ 2 =
        (B.budget * ‖(psi : P.PhysicalHilbert)‖ ^ 2) / A.referenceTime := by ring
    _ ≤ inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) := hdiv

/-- With a genuine excitation-domain witness, the model-derived intrinsic R4
budget lies below the normalized variational Yang--Mills mass. -/
theorem budget_le_normalized_physicalYangMillsMass
    (B : PhysicalYangMillsR4IntrinsicOptimalComponentData A)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    B.budget ≤ A.referenceTime * T.physicalYangMillsMass := by
  have hlower : B.budget / A.referenceTime ≤ T.physicalYangMillsMass :=
    T.rayleighLowerBound_le_physicalYangMillsMass W
      B.budget_div_referenceTime_mem_physicalYangMillsRayleighLowerBoundSet
  have hmul := mul_le_mul_of_nonneg_left hlower A.referenceTime_pos.le
  calc
    B.budget = A.referenceTime * (B.budget / A.referenceTime) := by
      field_simp [ne_of_gt A.referenceTime_pos]
    _ ≤ A.referenceTime * T.physicalYangMillsMass := hmul

/-- If an actual nonzero vacuum-orthogonal state attains the complete intrinsic
budget, then the normalized physical Yang--Mills mass equals that budget. -/
theorem normalized_physicalYangMillsMass_eq_budget_of_attained
    (B : PhysicalYangMillsR4IntrinsicOptimalComponentData A)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0)
    (hattain :
      A.referenceTime *
          inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) =
        B.budget * ‖(psi : P.PhysicalHilbert)‖ ^ 2) :
    A.referenceTime * T.physicalYangMillsMass = B.budget := by
  let lambda : ℝ := B.budget / A.referenceTime
  have hnorm_sq_ne : ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≠ 0 := by
    have hnorm : 0 < ‖(psi : P.PhysicalHilbert)‖ := norm_pos_iff.mpr hpsi
    positivity
  have hinner :
      inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) =
        lambda * ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
    dsimp [lambda]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (ne_of_gt A.referenceTime_pos)).2
    simpa [mul_comm] using hattain
  have hRayleigh : T.physicalYangMillsClosedRayleighQuotient psi = lambda := by
    unfold PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.StronglyContinuousPhysicalSemigroup.physicalYangMillsClosedRayleighQuotient
    rw [hinner]
    field_simp [hnorm_sq_ne]
  have hlower :
      ∀ phi : T.closedRightHamiltonian.domain,
        (phi : P.PhysicalHilbert) ≠ 0 →
        inner ℝ (phi : P.PhysicalHilbert) P.vacuum = 0 →
        lambda * ‖(phi : P.PhysicalHilbert)‖ ^ 2 ≤
          inner ℝ (T.closedRightHamiltonian phi) (phi : P.PhysicalHilbert) := by
    intro phi hphi hphiOrth
    exact B.budget_div_referenceTime_mem_physicalYangMillsRayleighLowerBoundSet
      phi hphi hphiOrth
  have hmass : T.physicalYangMillsMass = lambda :=
    T.physicalYangMillsMass_eq_of_uniformRayleighLowerBound_of_attained
      psi hpsi horthogonal hRayleigh hlower
  rw [hmass]
  dsimp [lambda]
  field_simp [ne_of_gt A.referenceTime_pos]

/-- Exact arithmetic evaluation of the intrinsic component budget.  The final
`33/20` is generated only after the six **intrinsic optimal coefficients** have
been independently identified with the R4 rational values. -/
theorem budget_eq_33_over_20_of_intrinsic_coefficients
    (B : PhysicalYangMillsR4IntrinsicOptimalComponentData A)
    (hbase : B.baseCoefficient = (9 : ℝ) / 5)
    (hcurv : B.curvatureCoefficient = (1 : ℝ) / 10)
    (hintpos : B.interactionPositiveCoefficient = 0)
    (hleak : B.interactionLeakCoefficient = (1 : ℝ) / 10)
    (hboundary : B.boundaryErrorCoefficient = (1 : ℝ) / 20)
    (hreg : B.regularizationErrorCoefficient = (1 : ℝ) / 10) :
    B.budget = (33 : ℝ) / 20 := by
  unfold budget
  rw [hbase, hcurv, hintpos, hleak, hboundary, hreg]
  norm_num

/-- Natural exact-value endpoint: if the actual Yang--Mills component forms
have the six stated intrinsic optimal coefficients and one genuine excitation
attains their combined intrinsic budget, then the dimensionless normalized
physical mass is theorem-equal to `33/20`.

Neither `33/20` nor any freely chosen component coefficient is present in the
underlying decomposition or optimality data. -/
theorem normalized_physicalYangMillsMass_eq_33_over_20_of_intrinsic_coefficients_and_attainment
    (B : PhysicalYangMillsR4IntrinsicOptimalComponentData A)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0)
    (hattain :
      A.referenceTime *
          inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) =
        B.budget * ‖(psi : P.PhysicalHilbert)‖ ^ 2)
    (hbase : B.baseCoefficient = (9 : ℝ) / 5)
    (hcurv : B.curvatureCoefficient = (1 : ℝ) / 10)
    (hintpos : B.interactionPositiveCoefficient = 0)
    (hleak : B.interactionLeakCoefficient = (1 : ℝ) / 10)
    (hboundary : B.boundaryErrorCoefficient = (1 : ℝ) / 20)
    (hreg : B.regularizationErrorCoefficient = (1 : ℝ) / 10) :
    A.referenceTime * T.physicalYangMillsMass = (33 : ℝ) / 20 := by
  calc
    A.referenceTime * T.physicalYangMillsMass = B.budget :=
      B.normalized_physicalYangMillsMass_eq_budget_of_attained
        psi hpsi horthogonal hattain
    _ = (33 : ℝ) / 20 :=
      B.budget_eq_33_over_20_of_intrinsic_coefficients
        hbase hcurv hintpos hleak hboundary hreg

end PhysicalYangMillsR4IntrinsicOptimalComponentData

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D