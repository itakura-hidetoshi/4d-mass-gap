import MGAP4D.MathlibAnalytic.ProjectiveLimitFiniteMarginalL2CylinderDensity
import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitL2CylinderIsometricSystem

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Every typed Euclidean Yang--Mills projective-limit measure is locally
available as a probability measure throughout this specialization file. -/
local instance projectiveLimitContinuumProbability
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    IsProbabilityMeasure L.continuumMeasure :=
  euclidean_yang_mills_projective_limit_probability L

namespace EuclideanYangMillsProjectiveLimitMeasure

variable
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (L : EuclideanYangMillsProjectiveLimitMeasure F)

/-- Algebraic directed union of all finite Euclidean Yang--Mills marginal `L²`
cylinder subspaces inside the projective-limit continuum carrier. -/
noncomputable def finiteMarginalL2CylinderTotalSubspace :
    Submodule ℝ (Lp ℝ 2 L.continuumMeasure) :=
  ⨆ J : Finset EuclideanFourSpace, L.finiteMarginalL2CylinderSubspace J

/-- Every fixed finite-marginal cylinder subspace lies in the total algebraic
cylinder subspace. -/
theorem finiteMarginalL2CylinderSubspace_le_total
    (J : Finset EuclideanFourSpace) :
    L.finiteMarginalL2CylinderSubspace J ≤
      L.finiteMarginalL2CylinderTotalSubspace := by
  exact le_iSup (fun K : Finset EuclideanFourSpace =>
    L.finiteMarginalL2CylinderSubspace K) J

/-- Every measurable continuum event indicator lies in the topological closure
of finite-coordinate Euclidean Yang--Mills cylinder functions. -/
theorem finiteMarginalL2CylinderTotalSubspace_indicatorConstLp_mem_topologicalClosure
    {s : Set F.Configuration}
    (hs : MeasurableSet s)
    (c : ℝ) :
    indicatorConstLp 2 hs (measure_ne_top L.continuumMeasure s) c ∈
      L.finiteMarginalL2CylinderTotalSubspace.topologicalClosure := by
  simpa [finiteMarginalL2CylinderTotalSubspace,
    finiteMarginalL2CylinderSubspace,
    projectiveLimitFiniteMarginalL2CylinderTotalSubspace] using
    (projectiveLimitFiniteMarginalL2CylinderTotalSubspace_indicatorConstLp_mem_topologicalClosure
      L.continuumMeasure F.finiteMarginal L.projectiveLimit hs c)

/-- The closure of all finite-marginal Euclidean Yang--Mills cylinder subspaces
is the full continuum projective-limit `L²` carrier. -/
theorem finiteMarginalL2CylinderTotalSubspace_topologicalClosure_eq_top :
    L.finiteMarginalL2CylinderTotalSubspace.topologicalClosure = ⊤ := by
  simpa [finiteMarginalL2CylinderTotalSubspace,
    finiteMarginalL2CylinderSubspace,
    projectiveLimitFiniteMarginalL2CylinderTotalSubspace] using
    (projectiveLimitFiniteMarginalL2CylinderTotalSubspace_topologicalClosure_eq_top
      L.continuumMeasure F.finiteMarginal L.projectiveLimit)

/-- Finite-marginal Euclidean Yang--Mills cylinder functions are dense in the
continuum projective-limit `L²` carrier. -/
theorem finiteMarginalL2CylinderTotalSubspace_dense :
    Dense
      (L.finiteMarginalL2CylinderTotalSubspace :
        Set (Lp ℝ 2 L.continuumMeasure)) := by
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    L.finiteMarginalL2CylinderTotalSubspace_topologicalClosure_eq_top

end EuclideanYangMillsProjectiveLimitMeasure

/-- Audit-visible Euclidean Yang--Mills specialization of projective-limit
finite-coordinate cylinder exhaustion. -/
structure EuclideanYangMillsProjectiveLimitL2CylinderDensityPackage
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) : Prop where
  finiteSubspace_le_total :
    ∀ J : Finset EuclideanFourSpace,
      L.finiteMarginalL2CylinderSubspace J ≤
        L.finiteMarginalL2CylinderTotalSubspace
  indicator_mem_topologicalClosure :
    ∀ {s : Set F.Configuration} (hs : MeasurableSet s) (c : ℝ),
      indicatorConstLp 2 hs (measure_ne_top L.continuumMeasure s) c ∈
        L.finiteMarginalL2CylinderTotalSubspace.topologicalClosure
  topologicalClosure_eq_top :
    L.finiteMarginalL2CylinderTotalSubspace.topologicalClosure = ⊤
  dense :
    Dense
      (L.finiteMarginalL2CylinderTotalSubspace :
        Set (Lp ℝ 2 L.continuumMeasure))

/-- Construct the complete Euclidean Yang--Mills cylinder-density receipt from
one typed projective-limit measure. -/
noncomputable def euclideanYangMillsProjectiveLimitL2CylinderDensityPackage
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    EuclideanYangMillsProjectiveLimitL2CylinderDensityPackage F L where
  finiteSubspace_le_total := L.finiteMarginalL2CylinderSubspace_le_total
  indicator_mem_topologicalClosure := fun hs c =>
    L.finiteMarginalL2CylinderTotalSubspace_indicatorConstLp_mem_topologicalClosure hs c
  topologicalClosure_eq_top :=
    L.finiteMarginalL2CylinderTotalSubspace_topologicalClosure_eq_top
  dense := L.finiteMarginalL2CylinderTotalSubspace_dense

end

end MathlibAnalytic
end MGAP4D
