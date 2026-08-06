import MGAP4D.MathlibAnalytic.ProjectiveLimitFiniteMarginalL2IsometricSystem
import Mathlib.MeasureTheory.Measure.SeparableMeasure

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable
    {ι : Type*}
    {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)]

/-- Measurable finite-coordinate cylinders form an algebra of sets on the full
product configuration space. -/
theorem measurableCylinders_isSetAlgebra :
    IsSetAlgebra (measurableCylinders α) where
  empty_mem := empty_mem_measurableCylinders α
  compl_mem := compl_mem_measurableCylinders
  union_mem := by
    intro s t hs ht
    exact union_mem_measurableCylinders (α := α) hs ht

/-- For every finite measure on a product measurable space, measurable
finite-coordinate cylinders are dense for symmetric-difference measure. -/
theorem measureDense_measurableCylinders_finite
    (μ : Measure (∀ i, α i))
    [IsFiniteMeasure μ] :
    μ.MeasureDense (measurableCylinders α) := by
  exact Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite μ
    measurableCylinders_isSetAlgebra
    (by simpa using (generateFrom_measurableCylinders (α := α)).symm)

/-- Every measurable finite marginal event has finite measure whenever the
projective-limit measure is finite. -/
theorem projectiveLimitFiniteMarginal_measure_ne_top
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    [IsFiniteMeasure μ]
    (J : Finset ι)
    {s : Set (∀ i : J, α i)}
    (hs : MeasurableSet s) :
    Q J s ≠ ∞ := by
  rw [← (projectiveLimitRestrictionMeasurePreserving μ Q hLimit J).measure_preimage
    hs.nullMeasurableSet]
  exact measure_ne_top μ _

/-- Pullback sends a finite-marginal constant indicator exactly to the
corresponding continuum cylinder indicator. -/
theorem projectiveLimitFiniteMarginalL2Pullback_indicatorConstLp
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    [IsFiniteMeasure μ]
    (J : Finset ι)
    {s : Set (∀ i : J, α i)}
    (hs : MeasurableSet s)
    (c : ℝ) :
    projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J
        (indicatorConstLp 2 hs
          (projectiveLimitFiniteMarginal_measure_ne_top μ Q hLimit J hs) c) =
      indicatorConstLp 2 (hs.cylinder J) (measure_ne_top μ _) c := by
  simpa [projectiveLimitFiniteMarginalL2Pullback, cylinder] using
    (Lp.indicatorConstLp_compMeasurePreserving
      (p := (2 : ℝ≥0∞)) (E := ℝ) hs
      (projectiveLimitFiniteMarginal_measure_ne_top μ Q hLimit J hs) c
      (projectiveLimitRestrictionMeasurePreserving μ Q hLimit J))

/-- Every measurable constant indicator depending on a fixed finite coordinate
set belongs to that finite-coordinate cylinder subspace. -/
theorem projectiveLimitFiniteMarginalL2CylinderSubspace_indicatorConstLp_mem
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    [IsFiniteMeasure μ]
    (J : Finset ι)
    {s : Set (∀ i : J, α i)}
    (hs : MeasurableSet s)
    (c : ℝ) :
    indicatorConstLp 2 (hs.cylinder J) (measure_ne_top μ _) c ∈
      projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J := by
  refine ⟨indicatorConstLp 2 hs
    (projectiveLimitFiniteMarginal_measure_ne_top μ Q hLimit J hs) c, ?_⟩
  exact projectiveLimitFiniteMarginalL2Pullback_indicatorConstLp
    μ Q hLimit J hs c

/-- Algebraic directed union of all finite-coordinate cylinder subspaces inside
one projective-limit `L²` carrier.  Its closure, rather than this algebraic
subspace itself, is the full continuum `L²` space. -/
noncomputable def projectiveLimitFiniteMarginalL2CylinderTotalSubspace
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q) :
    Submodule ℝ (Lp ℝ 2 μ) :=
  ⨆ J, projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J

/-- Every fixed finite-coordinate cylinder subspace lies in the total
finite-coordinate cylinder subspace. -/
theorem projectiveLimitFiniteMarginalL2CylinderSubspace_le_total
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    (J : Finset ι) :
    projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J ≤
      projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit := by
  exact le_iSup (fun K =>
    projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit K) J

/-- Every measurable finite-coordinate cylinder indicator belongs to the total
finite-coordinate cylinder subspace. -/
theorem projectiveLimitFiniteMarginalL2CylinderTotalSubspace_indicatorConstLp_mem
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    [IsFiniteMeasure μ]
    (J : Finset ι)
    {s : Set (∀ i : J, α i)}
    (hs : MeasurableSet s)
    (c : ℝ) :
    indicatorConstLp 2 (hs.cylinder J) (measure_ne_top μ _) c ∈
      projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit := by
  exact projectiveLimitFiniteMarginalL2CylinderSubspace_le_total μ Q hLimit J
    (projectiveLimitFiniteMarginalL2CylinderSubspace_indicatorConstLp_mem
      μ Q hLimit J hs c)

/-- Every measurable constant indicator lies in the topological closure of the
finite-coordinate cylinder subspace. -/
theorem projectiveLimitFiniteMarginalL2CylinderTotalSubspace_indicatorConstLp_mem_topologicalClosure
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    [IsFiniteMeasure μ]
    {s : Set (∀ i, α i)}
    (hs : MeasurableSet s)
    (c : ℝ) :
    indicatorConstLp 2 hs (measure_ne_top μ s) c ∈
      (projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit).topologicalClosure := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let hCyl : μ.MeasureDense (measurableCylinders α) :=
    measureDense_measurableCylinders_finite μ
  have hIndicators :=
    hCyl.indicatorConstLp_subset_closure (p := (2 : ℝ≥0∞)) c
  have hSource :
      indicatorConstLp 2 hs (measure_ne_top μ s) c ∈
        {indicatorConstLp 2 hs' hμs' c |
          (s' : Set (∀ i, α i)) (hs' : MeasurableSet s')
          (hμs' : μ s' ≠ ∞)} := by
    exact ⟨s, hs, measure_ne_top μ s, rfl⟩
  have hClosure := hIndicators hSource
  change indicatorConstLp 2 hs (measure_ne_top μ s) c ∈
    closure
      (projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit :
        Set (Lp ℝ 2 μ))
  refine closure_mono ?_ hClosure
  rintro f ⟨t, ht, hμt, rfl⟩
  rcases (mem_measurableCylinders (α := α) t).1 ht with ⟨J, u, hu, rfl⟩
  simpa using
    (projectiveLimitFiniteMarginalL2CylinderTotalSubspace_indicatorConstLp_mem
      μ Q hLimit J hu c)

/-- The topological closure of the algebraic finite-coordinate cylinder
subspace is the entire projective-limit `L²` space. -/
theorem projectiveLimitFiniteMarginalL2CylinderTotalSubspace_topologicalClosure_eq_top
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    [IsFiniteMeasure μ] :
    (projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit).topologicalClosure =
      ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro f _
    refine Lp.induction (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℝ)
      (by norm_num)
      (fun g => g ∈
        (projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit).topologicalClosure)
      ?_ ?_
      (Submodule.isClosed_topologicalClosure
        (projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit)) f
    · intro c s hs hμs
      simpa using
        (projectiveLimitFiniteMarginalL2CylinderTotalSubspace_indicatorConstLp_mem_topologicalClosure
          μ Q hLimit hs c)
    · intro g k hg hk hdisjoint hgc hkc
      exact
        (projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit).topologicalClosure.add_mem
          hgc hkc

/-- Finite-coordinate cylinder functions are dense in the projective-limit
`L²` carrier. -/
theorem projectiveLimitFiniteMarginalL2CylinderTotalSubspace_dense
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    [IsFiniteMeasure μ] :
    Dense
      (projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit :
        Set (Lp ℝ 2 μ)) := by
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (projectiveLimitFiniteMarginalL2CylinderTotalSubspace_topologicalClosure_eq_top
      μ Q hLimit)

/-- Audit-visible generic receipt for finite-coordinate cylinder exhaustion of a
finite projective-limit `L²` carrier. -/
structure ProjectiveLimitFiniteMarginalL2CylinderDensityPackage
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    [IsFiniteMeasure μ] : Prop where
  finiteSubspace_le_total :
    ∀ J : Finset ι,
      projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J ≤
        projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit
  indicator_mem_topologicalClosure :
    ∀ {s : Set (∀ i, α i)} (hs : MeasurableSet s) (c : ℝ),
      indicatorConstLp 2 hs (measure_ne_top μ s) c ∈
        (projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit).topologicalClosure
  topologicalClosure_eq_top :
    (projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit).topologicalClosure = ⊤
  dense :
    Dense
      (projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit :
        Set (Lp ℝ 2 μ))

/-- Construct the complete generic cylinder-density receipt. -/
noncomputable def projectiveLimitFiniteMarginalL2CylinderDensityPackage
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    [IsFiniteMeasure μ] :
    ProjectiveLimitFiniteMarginalL2CylinderDensityPackage μ Q hLimit where
  finiteSubspace_le_total :=
    projectiveLimitFiniteMarginalL2CylinderSubspace_le_total μ Q hLimit
  indicator_mem_topologicalClosure := fun hs c =>
    projectiveLimitFiniteMarginalL2CylinderTotalSubspace_indicatorConstLp_mem_topologicalClosure
      μ Q hLimit hs c
  topologicalClosure_eq_top :=
    projectiveLimitFiniteMarginalL2CylinderTotalSubspace_topologicalClosure_eq_top
      μ Q hLimit
  dense :=
    projectiveLimitFiniteMarginalL2CylinderTotalSubspace_dense μ Q hLimit

end

end MathlibAnalytic
end MGAP4D
