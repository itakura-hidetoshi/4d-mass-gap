import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointBoundedConcreteCoreDensity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkConditionalExpectation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance groundStateJointBoundedConcreteCoreAllOneLinkSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointBoundedConcreteCoreAllOneLinkSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointBoundedConcreteCoreAllOneLinkSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointBoundedConcreteCoreAllOneLinkSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointBoundedConcreteCoreAllOneLinkSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointBoundedConcreteCoreAllOneLinkSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- A vector in the bounded concrete core admits one and the same bounded
strongly measurable representative for which the sharp one-link coercivity
estimate holds simultaneously at every spatial target.

This is a quantifier-packaging theorem: no summation over links and no
same-color Doob factorization is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore_exists_all_oneLink_sharpHaarVariance_le_residual
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf : f ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta) :
    ∃
      (F :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : StronglyMeasurable F)
      (bound : ℝ)
      (hbound : ∀ z, ‖F z‖ ≤ bound),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound = f ∧
        ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreSharpHaarVarianceFunctional
              H N hN beta hbeta target F ≤
            ENNReal.ofReal
              (‖f -
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                    H N hN beta hbeta target f‖ ^ 2) := by
  rcases hf with ⟨F, hF, bound, hbound, hEq⟩
  refine ⟨F, hF, bound, hbound, hEq, ?_⟩
  intro target
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreSharpHaarVarianceFunctional_le_condExpL2_residual_norm_sq
      H N hN beta hbeta target F hF bound hbound
  rw [hEq] at h
  exact h

/-- The same common bounded representative also controls every sharp one-link
functional by the genuine conditional-expectation defect of the six-spatial
color containing that link.

Only monotonicity under sigma-algebra inclusion is used to pass from the
one-link defect to the color defect.  In particular, this theorem does not
assert same-color Doob commutation, factorization, independence, or any sum
bound over the links in a color. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore_exists_all_oneLink_sharpHaarVariance_le_color_residual
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf : f ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
        H N hN beta hbeta) :
    ∃
      (F :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : StronglyMeasurable F)
      (bound : ℝ)
      (hbound : ∀ z, ‖F z‖ ≤ bound),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound = f ∧
        ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreSharpHaarVarianceFunctional
              H N hN beta hbeta target F ≤
            ENNReal.ofReal
              (‖f -
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
                    H N hN beta hbeta
                    (periodicHypercubicEvenSpatialSliceLinkColor H target) f‖ ^ 2) := by
  obtain ⟨F, hF, bound, hbound, hEq, hAll⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore_exists_all_oneLink_sharpHaarVariance_le_residual
      H N hN beta hbeta f hf
  refine ⟨F, hF, bound, hbound, hEq, ?_⟩
  intro target
  have hLink := hAll target
  have hNorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_residual_norm_le_color
      H N hN beta hbeta target f
  have hSq :
      ‖f -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta target f‖ ^ 2 ≤
        ‖f -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
            H N hN beta hbeta
            (periodicHypercubicEvenSpatialSliceLinkColor H target) f‖ ^ 2 := by
    exact
      (sq_le_sq₀
        (norm_nonneg _)
        (norm_nonneg _)).2 hNorm
  exact hLink.trans (ENNReal.ofReal_le_ofReal hSq)

end

end MathlibAnalytic
end MGAP4D
