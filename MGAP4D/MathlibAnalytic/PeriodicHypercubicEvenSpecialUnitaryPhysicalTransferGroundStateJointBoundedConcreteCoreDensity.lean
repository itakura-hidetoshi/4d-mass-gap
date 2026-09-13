import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkBoundedCoreCondExpResidualCoercivity
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter Set
open scoped ENNReal BigOperators

noncomputable section

local instance groundStateJointBoundedConcreteCoreDensitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointBoundedConcreteCoreDensitySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointBoundedConcreteCoreDensitySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointBoundedConcreteCoreDensitySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointBoundedConcreteCoreDensitySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointBoundedConcreteCoreDensitySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The bounded strongly measurable concrete vectors used by the sharp
one-link theorem form a distinguished core inside the genuine ground-state
joint `L²` carrier.  The definition records existence of a bounded concrete
representative; it does not choose pointwise sections of an arbitrary `L²`
quotient representative. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Set (PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :=
  {f | ∃
      (F :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : StronglyMeasurable F)
      (bound : ℝ)
      (hbound : ∀ z, ‖F z‖ ≤ bound),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound = f}

/-- Every `L²` simple function belongs to the bounded concrete core.  Its finite
range supplies a literal global bound, so the existing bounded-concrete
constructor applies without truncating or evaluating an arbitrary quotient
representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSimpleFunc_mem_boundedConcreteCore
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (g : Lp.simpleFunc ℝ 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)) :
    (g : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta := by
  let F := Lp.simpleFunc.toSimpleFunc g
  let bound : ℝ := F.range.sum (fun y => ‖y‖)
  have hF : StronglyMeasurable (fun z => F z) := F.stronglyMeasurable
  have hbound : ∀ z, ‖F z‖ ≤ bound := by
    intro z
    dsimp [bound]
    exact Finset.single_le_sum (fun y hy => norm_nonneg y) (F.mem_range_self z)
  refine ⟨(fun z => F z), hF, bound, hbound, ?_⟩
  apply Lp.ext
  have hConcrete :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
      H N hN beta hbeta (fun z => F z) hF bound hbound
  have hSimple :
      (fun z =>
        (g : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta) z) =ᵐ[
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta] (fun z => F z) := by
    simpa [F] using (Lp.simpleFunc.toSimpleFunc_eq_toFun g).symm
  exact hConcrete.trans hSimple.symm

/-- The bounded concrete core is dense in the genuine ground-state joint `L²`
carrier.  The proof is purely Hilbert/measure theoretic: Mathlib's dense simple
functions are already bounded concrete representatives. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore_dense
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Dense
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta) := by
  let μJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  apply
    (Lp.simpleFunc.dense (E := ℝ) (p := (2 : ℝ≥0∞)) (μ := μJ)
      ENNReal.ofNat_ne_top).mono
  intro f hf
  let g : Lp.simpleFunc ℝ 2 μJ := ⟨f, hf⟩
  simpa [μJ, g] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSimpleFunc_mem_boundedConcreteCore
      H N hN beta hbeta g)

end

end MathlibAnalytic
end MGAP4D
