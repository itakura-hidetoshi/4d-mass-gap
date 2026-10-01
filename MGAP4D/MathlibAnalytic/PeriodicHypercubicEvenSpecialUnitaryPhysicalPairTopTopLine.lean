import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceSimplicity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2TopEigenspaceBlockClosureOrthogonality
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-!
# One-dimensionality of the completed physical top-top pair block

Once the full one-slice normalized-transfer top eigenspace is the line generated
by the chosen unit top mode, every decomposable top-top pair is a scalar
multiple of the single vector Ω ⊠ Ω.

This file propagates the one-slice simplicity theorem through the algebraic
top-top generator span and then through Hilbert closure.  Consequently the
completed top-top block is exactly one real line.

This is the pair-side form needed to reduce full top-top orthogonality to one
scalar inner-product condition.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance physicalPairTopTopLineTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairTopTopLineCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairTopTopLineSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairTopTopLineMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairTopTopLineBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairTopTopLineSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairTopTopLineSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section PhysicalPairTopTopLine

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N

local notation "F" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
    H N hN beta hbeta

local notation "PairE" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N

local notation "omega" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
    H N hN beta hbeta

/-- The chosen one-slice top vector, now bundled as an element of the full
top eigenspace. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvectorInTopEigenspace :
    F :=
  ⟨omega,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
      H N hN beta hbeta⟩

/-- Canonical generator of the completed top-top pair line. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopLineGenerator :
    PairE :=
  periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopDecomposableL2
    H N hN beta hbeta
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvectorInTopEigenspace
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvectorInTopEigenspace
      H N hN beta hbeta)

/-- Every bundled full-top vector is a scalar multiple of the bundled chosen
top eigenvector. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspace_exists_smul_topEigenvector
    (u : F) :
    ∃ c : ℝ,
      u =
        c •
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvectorInTopEigenspace
            H N hN beta hbeta := by
  have hTopLine :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_topEigenvector
      H N hN beta hbeta
  have hu :
      (u : G) ∈ ℝ ∙ omega := by
    rw [← hTopLine]
    exact u.property
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu
  refine ⟨c, ?_⟩
  apply Subtype.ext
  exact hc.symm

/-- Every decomposable top-top generator is a scalar multiple of the canonical
Ω ⊠ Ω generator. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopDecomposableL2_mem_span_generator
    (u v : F) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopDecomposableL2
        H N hN beta hbeta u v ∈
      ℝ ∙ periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopLineGenerator
        H N hN beta hbeta := by
  obtain ⟨cu, hu⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspace_exists_smul_topEigenvector
      H N hN beta hbeta u
  obtain ⟨cv, hv⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspace_exists_smul_topEigenvector
      H N hN beta hbeta v
  rw [hu, hv]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopLineGenerator]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopDecomposableL2
  rw [map_smul, map_smul]
  rw [realL2ExternalTensor_smul_left, realL2ExternalTensor_smul_right, smul_smul]
  exact Submodule.smul_mem _
    (cu * cv)
    (Submodule.mem_span_singleton_self _)

/-- The algebraic full top-top block is already the single line generated by
Ω ⊠ Ω. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan_eq_span_generator :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan
        H N hN beta hbeta =
      ℝ ∙ periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopLineGenerator
        H N hN beta hbeta := by
  apply le_antisymm
  · rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan]
    apply Submodule.span_le.2
    intro z hz
    rcases hz with ⟨⟨u, v⟩, rfl⟩
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopDecomposableL2_mem_span_generator
        H N hN beta hbeta u v
  · rw [Submodule.span_singleton_le_iff_mem]
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan]
    apply Submodule.subset_span
    refine ⟨
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvectorInTopEigenspace
        H N hN beta hbeta,
       periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvectorInTopEigenspace
        H N hN beta hbeta), ?_⟩
    rfl

/-- The completed full top-top block is the same one-dimensional line. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_eq_span_generator :
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
        H N hN beta hbeta =
      ℝ ∙ periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopLineGenerator
        H N hN beta hbeta := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure,
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan_eq_span_generator]
  exact
    (ℝ ∙ periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopLineGenerator
      H N hN beta hbeta).closed_of_finiteDimensional.submodule_topologicalClosure_eq

/-- Orthogonality to the completed top-top block is now exactly one scalar
matrix-coefficient condition. -/
theorem periodicHypercubicEvenSpecialUnitary_mem_topTopBlockClosure_orthogonal_iff_inner_generator_eq_zero
    (x : PairE) :
    x ∈
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
          H N hN beta hbeta)ᗮ ↔
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopLineGenerator
          H N hN beta hbeta)
        x = 0 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_eq_span_generator
      H N hN beta hbeta,
    Submodule.mem_orthogonal]
  constructor
  · intro hx
    exact hx
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopLineGenerator
        H N hN beta hbeta)
      (Submodule.mem_span_singleton_self _)
  · intro hx y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [real_inner_smul_left, hx, mul_zero]

end PhysicalPairTopTopLine

end

end MathlibAnalytic
end MGAP4D
