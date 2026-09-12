import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicOffLinkUniformSeparationBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

/-- A fixed heat-bath coercivity constant on the entire Gibbs-vacuum orthogonal
subspace.  Unlike the unit-sphere formulation, this is homogeneous in the
vector norm and is the standard sectorwise quadratic lower bound. -/
def ContinuousCompactOrientedGaugeWilsonSystem.periodicVacuumOrthogonalHeatBathCoerciveAtL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (κ : ℝ) : Prop :=
  ∀ f : Lp ℝ 2 C.gibbsMeasure,
    f ∈ C.VacuumOrthogonalL2 →
      κ * ‖f‖ ^ 2 ≤ inner ℝ (C.heatBathHamiltonianL2 f) f

/-- Existence of a strictly positive homogeneous heat-bath coercivity constant
on the full Gibbs-vacuum orthogonal subspace. -/
def ContinuousCompactOrientedGaugeWilsonSystem.periodicVacuumOrthogonalHomogeneousHeatBathCoerciveL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) : Prop :=
  ∃ κ : ℝ,
    0 < κ ∧
      C.periodicVacuumOrthogonalHeatBathCoerciveAtL2 κ

/-- A homogeneous sectorwise coercivity bound with constant `κ` is exactly the
existing heat-bath Poincare inequality with the same constant.  The forward
direction applies sectorwise coercivity to the vacuum-centered vector; the
reverse direction uses that vacuum centering fixes every vacuum-orthogonal
vector. -/
theorem continuous_compact_oriented_periodicVacuumOrthogonalHeatBathCoerciveAt_iff_poincare
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (κ : ℝ) :
    C.periodicVacuumOrthogonalHeatBathCoerciveAtL2 κ ↔
      C.HeatBathPoincareL2 κ := by
  constructor
  · intro hCoercive
    intro f
    have hCenteredOrth :
        C.vacuumCenteredL2 f ∈ C.VacuumOrthogonalL2 :=
      continuous_compact_oriented_periodicRayleighInfimumPoincare_vacuumCentered_mem_orthogonal
        C f
    have hCenteredLower :=
      hCoercive (C.vacuumCenteredL2 f) hCenteredOrth
    calc
      κ * ‖C.vacuumCenteredL2 f‖ ^ 2 ≤
          inner ℝ
            (C.heatBathHamiltonianL2 (C.vacuumCenteredL2 f))
            (C.vacuumCenteredL2 f) := hCenteredLower
      _ = inner ℝ (C.heatBathHamiltonianL2 f) f :=
        continuous_compact_oriented_periodicRayleighInfimumPoincare_vacuumCentered_quadratic_eq
          C f
  · intro hPoincare f hfOrth
    have hfInner : inner ℝ C.gibbsVacuumL2 f = 0 :=
      (continuous_compact_oriented_mem_vacuumOrthogonalL2_iff C f).1 hfOrth
    have hCentered : C.vacuumCenteredL2 f = f :=
      continuous_compact_oriented_vacuumCenteredL2_eq_self C f hfInner
    simpa [hCentered] using hPoincare f

/-- Positive homogeneous vacuum-orthogonal coercivity is exactly existence of a
strictly positive heat-bath Poincare constant.  The witness constant is
preserved in both directions. -/
theorem continuous_compact_oriented_periodicVacuumOrthogonalHomogeneousHeatBathCoercive_iff_exists_positive_poincare
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.periodicVacuumOrthogonalHomogeneousHeatBathCoerciveL2 ↔
      ∃ gap : ℝ, 0 < gap ∧ C.HeatBathPoincareL2 gap := by
  constructor
  · rintro ⟨κ, hκPos, hCoercive⟩
    exact ⟨κ, hκPos,
      (continuous_compact_oriented_periodicVacuumOrthogonalHeatBathCoerciveAt_iff_poincare
        C κ).1 hCoercive⟩
  · rintro ⟨κ, hκPos, hPoincare⟩
    exact ⟨κ, hκPos,
      (continuous_compact_oriented_periodicVacuumOrthogonalHeatBathCoerciveAt_iff_poincare
        C κ).2 hPoincare⟩

/-- Positive coercivity on the full vacuum-orthogonal subspace is equivalent to
positive coercivity on its unit sphere.  The reverse direction normalizes each
nonzero vector and recovers the original vector by quadratic homogeneity. -/
theorem continuous_compact_oriented_periodicVacuumOrthogonalHomogeneousHeatBathCoercive_iff_unitHeatBathCoercive
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.periodicVacuumOrthogonalHomogeneousHeatBathCoerciveL2 ↔
      C.periodicVacuumOrthogonalUnitHeatBathCoerciveL2 := by
  constructor
  · rintro ⟨κ, hκPos, hCoercive⟩
    refine ⟨κ, hκPos, ?_⟩
    intro f hfOrth hfNorm
    have hLower := hCoercive f hfOrth
    simpa [hfNorm] using hLower
  · rintro ⟨κ, hκPos, hUnitCoercive⟩
    refine ⟨κ, hκPos, ?_⟩
    intro f hfOrth
    by_cases hfZero : f = 0
    · subst f
      simp
    · let normalized : Lp ℝ 2 C.gibbsMeasure := ‖f‖⁻¹ • f
      have hNormPos : 0 < ‖f‖ := norm_pos_iff.mpr hfZero
      have hNormNe : ‖f‖ ≠ 0 := ne_of_gt hNormPos
      have hNormalizedOrth : normalized ∈ C.VacuumOrthogonalL2 := by
        exact C.VacuumOrthogonalL2.smul_mem _ hfOrth
      have hNormalizedNorm : ‖normalized‖ = 1 := by
        simpa [normalized] using
          (continuous_compact_oriented_periodicRayleighInfimumPoincare_normalize_norm_eq_one
            C f hfZero)
      have hNormalizedLower :=
        hUnitCoercive normalized hNormalizedOrth hNormalizedNorm
      have hRecover : ‖f‖ • normalized = f := by
        dsimp [normalized]
        rw [smul_smul, mul_inv_cancel₀ hNormNe, one_smul]
      have hScale :=
        continuous_compact_oriented_periodicRayleighInfimumPoincare_quadratic_smul
          C ‖f‖ normalized
      rw [hRecover] at hScale
      calc
        κ * ‖f‖ ^ 2 = ‖f‖ ^ 2 * κ := by ring
        _ ≤ ‖f‖ ^ 2 *
            inner ℝ (C.heatBathHamiltonianL2 normalized) normalized :=
          mul_le_mul_of_nonneg_left hNormalizedLower (sq_nonneg ‖f‖)
        _ = inner ℝ (C.heatBathHamiltonianL2 f) f := hScale.symm

/-- Uniform separation by at least one local off-link projection defect is
exactly positive homogeneous coercivity on the full vacuum-orthogonal sector. -/
theorem continuous_compact_oriented_periodicOffLinkUniformSeparation_iff_homogeneousHeatBathCoercive
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.periodicVacuumOrthogonalUnitOffLinkUniformSeparationL2 ↔
      C.periodicVacuumOrthogonalHomogeneousHeatBathCoerciveL2 := by
  exact
    (continuous_compact_oriented_periodicOffLinkUniformSeparation_iff_heatBathCoercive C).trans
      (continuous_compact_oriented_periodicVacuumOrthogonalHomogeneousHeatBathCoercive_iff_unitHeatBathCoercive
        C).symm

/-- When the unit vacuum-orthogonal Rayleigh set is inhabited, strict positivity
of its variational lower edge is exactly positive homogeneous coercivity. -/
theorem continuous_compact_oriented_periodicRayleighInfimum_pos_iff_homogeneousHeatBathCoercive
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hNonempty : C.periodicVacuumOrthogonalUnitRayleighEnergySet.Nonempty) :
    0 < C.periodicVacuumOrthogonalUnitRayleighInfimum ↔
      C.periodicVacuumOrthogonalHomogeneousHeatBathCoerciveL2 := by
  exact
    (continuous_compact_oriented_periodicOffLinkUniformSeparation_rayleighInfimum_pos_iff_heatBathCoercive
      C hNonempty).trans
      (continuous_compact_oriented_periodicVacuumOrthogonalHomogeneousHeatBathCoercive_iff_unitHeatBathCoercive
        C).symm

/-- For the actual side-three periodic `SU(2)` endpoint system, homogeneous
coercivity at a fixed constant is exactly the standard heat-bath Poincare
inequality at that same constant. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_homogeneousHeatBathCoerciveAt_iff_poincare
    (κ : ℝ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalHeatBathCoerciveAtL2 κ ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.HeatBathPoincareL2 κ := by
  exact
    continuous_compact_oriented_periodicVacuumOrthogonalHeatBathCoerciveAt_iff_poincare
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem κ

/-- Actual positive homogeneous heat-bath coercivity is exactly existence of a
strictly positive actual finite-volume Poincare constant. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_homogeneousHeatBathCoercive_iff_exists_positive_poincare :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalHomogeneousHeatBathCoerciveL2 ↔
      ∃ gap : ℝ,
        0 < gap ∧
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.HeatBathPoincareL2 gap := by
  exact
    continuous_compact_oriented_periodicVacuumOrthogonalHomogeneousHeatBathCoercive_iff_exists_positive_poincare
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem

/-- Actual uniform local-defect separation is exactly actual homogeneous
heat-bath coercivity on every vacuum-orthogonal vector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_offLinkUniformSeparation_iff_homogeneousHeatBathCoercive :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitOffLinkUniformSeparationL2 ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalHomogeneousHeatBathCoerciveL2 := by
  exact
    continuous_compact_oriented_periodicOffLinkUniformSeparation_iff_homogeneousHeatBathCoercive
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem

/-- Actual strict positivity of the finite-volume Rayleigh lower edge is exactly
actual homogeneous heat-bath coercivity. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_pos_iff_homogeneousHeatBathCoercive :
    0 <
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalHomogeneousHeatBathCoerciveL2 := by
  exact
    continuous_compact_oriented_periodicRayleighInfimum_pos_iff_homogeneousHeatBathCoercive
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighEnergySet_nonempty

/-- Compact proof-facing package identifying all standard finite-volume
positive-coercivity formulations for the actual side-three periodic `SU(2)`
endpoint system. -/
def periodicHypercubicThreeSpecialUnitaryTwoHomogeneousPoincareCoercivityReceipt : Prop :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalHomogeneousHeatBathCoerciveL2 ↔
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitHeatBathCoerciveL2) ∧
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalHomogeneousHeatBathCoerciveL2 ↔
    ∃ gap : ℝ,
      0 < gap ∧
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.HeatBathPoincareL2 gap) ∧
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitOffLinkUniformSeparationL2 ↔
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalHomogeneousHeatBathCoerciveL2) ∧
  (0 <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ↔
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalHomogeneousHeatBathCoerciveL2)

/-- The actual positive finite-volume frontier is equivalently expressed as a
unit-sphere lower bound, a homogeneous sectorwise lower bound, a standard
Poincare inequality, or uniform off-link separation.  This theorem does not
prove that any positive witness exists. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoHomogeneousPoincareCoercivityReceipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoHomogeneousPoincareCoercivityReceipt := by
  exact ⟨
    continuous_compact_oriented_periodicVacuumOrthogonalHomogeneousHeatBathCoercive_iff_unitHeatBathCoercive
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_homogeneousHeatBathCoercive_iff_exists_positive_poincare,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_offLinkUniformSeparation_iff_homogeneousHeatBathCoercive,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_pos_iff_homogeneousHeatBathCoercive⟩

end

end MathlibAnalytic
end MGAP4D
