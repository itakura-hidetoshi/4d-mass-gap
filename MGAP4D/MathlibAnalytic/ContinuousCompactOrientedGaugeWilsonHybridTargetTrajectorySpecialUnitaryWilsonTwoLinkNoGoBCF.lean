import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryTwoLinkCylinderObservableBCF
import MGAP4D.MathlibAnalytic.SpecialUnitaryCompactOrientedGaugeWilsonSystem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- Right multiplication is surjective, so precomposition by a fixed right
translate does not change the range of a function on a group. -/
private theorem range_right_mul_eq
    {G R : Type*}
    [Group G]
    (f : G → R)
    (s : G) :
    Set.range (fun g : G => f (g * s)) = Set.range f := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g * s, rfl⟩
  · rintro ⟨g, rfl⟩
    refine ⟨g * s⁻¹, ?_⟩
    simp

/-- Oscillation of a bounded continuous real function on the compact Gauge
group. -/
def ContinuousCompactOrientedGaugeWilsonSystem.gaugeFunctionOscillationBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : BoundedContinuousFunction C.base.Gauge ℝ) : ℝ :=
  sSup (Set.range f) - sInf (Set.range f)

/-- A two-variable kernel obtained by applying a bounded continuous Gauge
function after right multiplication.  A single Wilson plaquette with a frozen
staple has exactly this form. -/
def ContinuousCompactOrientedGaugeWilsonSystem.rightTranslateKernelBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : BoundedContinuousFunction C.base.Gauge ℝ) :
    BoundedContinuousFunction (C.base.Gauge × C.base.Gauge) ℝ := by
  let F : C.base.Gauge × C.base.Gauge → ℝ :=
    fun z => f (z.1 * z.2)
  have hF : Continuous F := by
    exact f.continuous.comp (continuous_fst.mul continuous_snd)
  exact BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩

@[simp]
theorem continuous_compact_oriented_rightTranslateKernelBCF_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : BoundedContinuousFunction C.base.Gauge ℝ)
    (g s : C.base.Gauge) :
    C.rightTranslateKernelBCF f (g, s) = f (g * s) := by
  rfl

/-- Every frozen target section of a right-translate kernel has exactly the
same range as the underlying one-variable function. -/
theorem continuous_compact_oriented_rightTranslateKernelBCF_targetSection_range_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : BoundedContinuousFunction C.base.Gauge ℝ)
    (s : C.base.Gauge) :
    Set.range (fun g : C.base.Gauge => C.rightTranslateKernelBCF f (g, s)) =
      Set.range f := by
  change Set.range (fun g : C.base.Gauge => f (g * s)) = Set.range f
  exact range_right_mul_eq (fun g : C.base.Gauge => f g) s

/-- The target-section oscillation of a right-translate kernel is the
oscillation of the underlying function and is therefore independent of the
frozen source value. -/
theorem continuous_compact_oriented_rightTranslateKernelBCF_targetSectionOscillation_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : BoundedContinuousFunction C.base.Gauge ℝ)
    (s : C.base.Gauge) :
    C.twoLinkCylinderTargetSectionOscillationBCF
        (C.rightTranslateKernelBCF f) s =
      C.gaugeFunctionOscillationBCF f := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.twoLinkCylinderTargetSectionOscillationBCF
    ContinuousCompactOrientedGaugeWilsonSystem.gaugeFunctionOscillationBCF
  rw [continuous_compact_oriented_rightTranslateKernelBCF_targetSection_range_eq
    C f s]

/-- Any two frozen target sections of a right-translate kernel have equal
oscillation. -/
theorem continuous_compact_oriented_rightTranslateKernelBCF_targetSectionOscillation_eq_targetSectionOscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : BoundedContinuousFunction C.base.Gauge ℝ)
    (s₀ s₁ : C.base.Gauge) :
    C.twoLinkCylinderTargetSectionOscillationBCF
        (C.rightTranslateKernelBCF f) s₀ =
      C.twoLinkCylinderTargetSectionOscillationBCF
        (C.rightTranslateKernelBCF f) s₁ := by
  rw [continuous_compact_oriented_rightTranslateKernelBCF_targetSectionOscillation_eq
      C f s₀,
    continuous_compact_oriented_rightTranslateKernelBCF_targetSectionOscillation_eq
      C f s₁]

/-- For a concrete two-link cylinder built from a pure right-translate kernel,
the endpoint insertion-profile oscillation margin is identically zero. -/
theorem continuous_compact_oriented_rightTranslateTwoLinkCylinderObservableBCF_oscillationMargin_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (hSource : source ≠ target)
    (f : BoundedContinuousFunction C.base.Gauge ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
        target
        (C.twoLinkCylinderObservableBCF target source
          (C.rightTranslateKernelBCF f)) z = 0 := by
  rw [continuous_compact_oriented_twoLinkCylinderObservableBCF_oscillationMargin_eq_sectionOscillationMismatch
    C target source hSource (C.rightTranslateKernelBCF f) z]
  have hSections :=
    continuous_compact_oriented_rightTranslateKernelBCF_targetSectionOscillation_eq_targetSectionOscillation
      C f
      ((C.independentPairHybridConfiguration z.1 z.2 0) source)
      ((C.independentPairHybridConfiguration z.1 z.2
        (Fintype.card C.base.geometry.Edge)) source)
  rw [hSections, sub_self, abs_zero]

/-- Consequently the PR #922 coordinate-update criterion can never hold for a
single pure right-translate kernel.  This is a no-go for obtaining the margin
from one Wilson plaquette with a frozen staple. -/
theorem continuous_compact_oriented_rightTranslateTwoLinkCylinderObservableBCF_not_coordinateUpdateWitness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (hSource : source ≠ target)
    (f : BoundedContinuousFunction C.base.Gauge ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    ¬ C.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
        target
        (C.twoLinkCylinderObservableBCF target source
          (C.rightTranslateKernelBCF f)) z := by
  rw [continuous_compact_oriented_twoLinkCylinderObservableBCF_coordinateUpdateWitness_iff_sectionOscillation_ne
    C target source hSource (C.rightTranslateKernelBCF f) z]
  intro hNe
  exact hNe
    (continuous_compact_oriented_rightTranslateKernelBCF_targetSectionOscillation_eq_targetSectionOscillation
      C f
      ((C.independentPairHybridConfiguration z.1 z.2 0) source)
      ((C.independentPairHybridConfiguration z.1 z.2
        (Fintype.card C.base.geometry.Edge)) source))

/-- There is no non-null Gibbs-pair family carrying the PR #922 section
mismatch for a pure right-translate kernel. -/
theorem continuous_compact_oriented_rightTranslateTwoLinkCylinderObservableBCF_not_sectionOscillationMismatch
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (f : BoundedContinuousFunction C.base.Gauge ℝ) :
    ¬ C.independentPairHybridTargetTrajectoryTwoLinkCylinderSectionOscillationMismatchBCF
        target source (C.rightTranslateKernelBCF f) := by
  intro hMismatch
  exact hMismatch (Filter.Eventually.of_forall fun z => by
    intro hNe
    exact hNe
      (continuous_compact_oriented_rightTranslateKernelBCF_targetSectionOscillation_eq_targetSectionOscillation
        C f
        ((C.independentPairHybridConfiguration z.1 z.2 0) source)
        ((C.independentPairHybridConfiguration z.1 z.2
          (Fintype.card C.base.geometry.Edge)) source)))

/-- The conventional `SU(N)` Wilson plaquette energy as an actual bounded
continuous function on the compact special-unitary group. -/
def specialUnitaryWilsonPlaquetteEnergyBCF
    (N : ℕ) :
    BoundedContinuousFunction (SpecialUnitaryMatrixGroup N) ℝ := by
  letI : CompactSpace (SpecialUnitaryMatrixGroup N) :=
    specialUnitaryGroupCompactSpace N
  exact BoundedContinuousFunction.mkOfCompact
    ⟨specialUnitaryWilsonPlaquetteEnergy N,
      continuous_specialUnitaryWilsonPlaquetteEnergy N⟩

@[simp]
theorem specialUnitaryWilsonPlaquetteEnergyBCF_apply
    (N : ℕ)
    (g : SpecialUnitaryMatrixGroup N) :
    specialUnitaryWilsonPlaquetteEnergyBCF N g =
      specialUnitaryWilsonPlaquetteEnergy N g := by
  rfl

/-- The actual two-variable `SU(N)` Wilson kernel obtained from a target link
and one frozen right staple. -/
def specialUnitaryWilsonRightTranslateKernelBCF
    (N : ℕ) :
    BoundedContinuousFunction
      (SpecialUnitaryMatrixGroup N × SpecialUnitaryMatrixGroup N) ℝ := by
  letI : IsTopologicalGroup (SpecialUnitaryMatrixGroup N) :=
    specialUnitaryGroupIsTopologicalGroup N
  letI : CompactSpace (SpecialUnitaryMatrixGroup N) :=
    specialUnitaryGroupCompactSpace N
  let F : SpecialUnitaryMatrixGroup N × SpecialUnitaryMatrixGroup N → ℝ :=
    fun z => specialUnitaryWilsonPlaquetteEnergy N (z.1 * z.2)
  have hF : Continuous F := by
    exact (continuous_specialUnitaryWilsonPlaquetteEnergy N).comp
      (continuous_fst.mul continuous_snd)
  exact BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩

@[simp]
theorem specialUnitaryWilsonRightTranslateKernelBCF_apply
    (N : ℕ)
    (g s : SpecialUnitaryMatrixGroup N) :
    specialUnitaryWilsonRightTranslateKernelBCF N (g, s) =
      specialUnitaryWilsonPlaquetteEnergy N (g * s) := by
  rfl

/-- Every frozen target section of the actual `SU(N)` Wilson right-translate
kernel has the full range of the Wilson plaquette energy. -/
theorem specialUnitaryWilsonRightTranslateKernelBCF_targetSection_range_eq
    (N : ℕ)
    (s : SpecialUnitaryMatrixGroup N) :
    Set.range (fun g : SpecialUnitaryMatrixGroup N =>
        specialUnitaryWilsonRightTranslateKernelBCF N (g, s)) =
      Set.range (specialUnitaryWilsonPlaquetteEnergy N) := by
  change Set.range (fun g : SpecialUnitaryMatrixGroup N =>
      specialUnitaryWilsonPlaquetteEnergy N (g * s)) =
    Set.range (specialUnitaryWilsonPlaquetteEnergy N)
  exact range_right_mul_eq (specialUnitaryWilsonPlaquetteEnergy N) s

/-- Target-section oscillation of the actual `SU(N)` Wilson right-translate
kernel. -/
def specialUnitaryWilsonRightTranslateTargetSectionOscillationBCF
    (N : ℕ)
    (s : SpecialUnitaryMatrixGroup N) : ℝ :=
  sSup (Set.range (fun g : SpecialUnitaryMatrixGroup N =>
      specialUnitaryWilsonRightTranslateKernelBCF N (g, s))) -
    sInf (Set.range (fun g : SpecialUnitaryMatrixGroup N =>
      specialUnitaryWilsonRightTranslateKernelBCF N (g, s)))

/-- The actual `SU(N)` Wilson section oscillation equals the global Wilson
energy oscillation, independently of the frozen staple. -/
theorem specialUnitaryWilsonRightTranslateTargetSectionOscillationBCF_eq
    (N : ℕ)
    (s : SpecialUnitaryMatrixGroup N) :
    specialUnitaryWilsonRightTranslateTargetSectionOscillationBCF N s =
      sSup (Set.range (specialUnitaryWilsonPlaquetteEnergy N)) -
        sInf (Set.range (specialUnitaryWilsonPlaquetteEnergy N)) := by
  unfold specialUnitaryWilsonRightTranslateTargetSectionOscillationBCF
  rw [specialUnitaryWilsonRightTranslateKernelBCF_targetSection_range_eq N s]

/-- No two frozen staples can produce unequal target-section oscillations for
a single `SU(N)` Wilson plaquette kernel. -/
theorem specialUnitaryWilsonRightTranslateTargetSectionOscillationBCF_independent
    (N : ℕ)
    (s₀ s₁ : SpecialUnitaryMatrixGroup N) :
    specialUnitaryWilsonRightTranslateTargetSectionOscillationBCF N s₀ =
      specialUnitaryWilsonRightTranslateTargetSectionOscillationBCF N s₁ := by
  rw [specialUnitaryWilsonRightTranslateTargetSectionOscillationBCF_eq N s₀,
    specialUnitaryWilsonRightTranslateTargetSectionOscillationBCF_eq N s₁]

end

end MathlibAnalytic
end MGAP4D
