import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCarrierFourBlockDecomposition
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance physicalPairCompletedTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairCompletedCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairCompletedSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairCompletedMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairCompletedBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairCompletedSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairCompletedSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section CompletedPhysicalPairDecomposition

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "PairE" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "PairT" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure H N hN beta hbeta
local notation "PairN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure H N hN beta hbeta
local notation "PairP" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N

local instance physicalPairCompletedTopTopCompleteSpace : CompleteSpace PairT := by
  have hclosed : IsClosed (PairT : Set PairE) := by
    simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure] using
      Submodule.isClosed_topologicalClosure
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan
          H N hN beta hbeta)
  exact hclosed.completeSpace_coe

private theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalProjection_span_mem_nonTop
    {x : PairE}
    (hx : x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N) :
    ((PairT)ᗮ).starProjection x ∈ PairN := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan_eq_topTop_sup_nonTop
    H N hN beta hbeta] at hx
  rcases Submodule.mem_sup.1 hx with ⟨t, ht, n, hn, rfl⟩
  have htT : t ∈ PairT := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure]
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan
        H N hN beta hbeta).le_topologicalClosure ht
  have hnN : n ∈ PairN := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure]
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockSpan
        H N hN beta hbeta).le_topologicalClosure hn
  have hOrtho : PairT ⟂ PairN :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_isOrtho_nonTopBlockClosure
      H N hN beta hbeta
  have hnOrth : n ∈ (PairT)ᗮ := hOrtho.symm hnN
  have hQt : ((PairT)ᗮ).starProjection t = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero (K := PairT) htT
  have hQn : ((PairT)ᗮ).starProjection n = n :=
    (Submodule.starProjection_eq_self_iff (K := (PairT)ᗮ)).2 hnOrth
  rw [map_add, hQt, hQn, zero_add]
  exact hnN

private theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalProjection_nonTopPreimage_isClosed :
    IsClosed
      ((((PairN).comap (((PairT)ᗮ).starProjection.toLinearMap)) : Submodule ℝ PairE) : Set PairE) := by
  have hNclosed : IsClosed (PairN : Set PairE) := by
    simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure] using
      Submodule.isClosed_topologicalClosure
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockSpan
          H N hN beta hbeta)
  change IsClosed (((PairT)ᗮ).starProjection ⁻¹' (PairN : Set PairE))
  exact hNclosed.preimage ((PairT)ᗮ).starProjection.continuous

/-- The orthogonal projection away from the completed top-top block maps the entire
completed physical pair carrier into the completed non-top block.  This is the
continuity step that upgrades the algebraic four-block decomposition to Hilbert
completion. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalProjection_mem_nonTop
    (x : PairE) (hx : x ∈ PairP) : ((PairT)ᗮ).starProjection x ∈ PairN := by
  have hSpan :
      periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N ≤
        (PairN).comap (((PairT)ᗮ).starProjection.toLinearMap) := by
    intro y hy
    change ((PairT)ᗮ).starProjection y ∈ PairN
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalProjection_span_mem_nonTop
        H N hN beta hbeta hy
  have hPreClosed :
      IsClosed
        (((PairN).comap (((PairT)ᗮ).starProjection.toLinearMap) : Submodule ℝ PairE) : Set PairE) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalProjection_nonTopPreimage_isClosed
      H N hN beta hbeta
  have hCarrier :
      PairP ≤ (PairN).comap (((PairT)ᗮ).starProjection.toLinearMap) := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier]
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N).topologicalClosure_minimal
        hSpan hPreClosed
  exact hCarrier hx

/-- The completed physical pair carrier is exactly the orthogonal sum of the completed
top-top block and the completed non-top block. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_eq_topTopClosure_sup_nonTopClosure :
    PairP = PairT ⊔ PairN := by
  apply le_antisymm
  · intro x hx
    have hNproj : ((PairT)ᗮ).starProjection x ∈ PairN :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalProjection_mem_nonTop
        H N hN beta hbeta x hx
    have hTproj : (PairT).starProjection x ∈ PairT :=
      Submodule.starProjection_apply_mem (PairT) x
    have hsum : (PairT).starProjection x + ((PairT)ᗮ).starProjection x = x := by
      calc
        (PairT).starProjection x + ((PairT)ᗮ).starProjection x =
            (PairT).starProjection x + (x - (PairT).starProjection x) := by
          rw [Submodule.starProjection_orthogonal_val (K := PairT)]
        _ = x := by abel
    exact Submodule.mem_sup.2
      ⟨(PairT).starProjection x, hTproj,
        ((PairT)ᗮ).starProjection x, hNproj, hsum⟩
  · exact sup_le
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_le_physicalPairCarrier
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_le_physicalPairCarrier
        H N hN beta hbeta)

/-- Inside the physical pair carrier, the completed non-top block is exactly the
orthogonal complement of the completed top-top block.  The ambient orthogonal
complement may be larger; the intersection with the physical pair carrier is essential. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopClosure_eq_carrier_inf_topTopOrthogonal :
    PairN = PairP ⊓ (PairT)ᗮ := by
  apply le_antisymm
  · intro x hx
    have hP : x ∈ PairP :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_le_physicalPairCarrier
        H N hN beta hbeta hx
    have hOrtho : PairT ⟂ PairN :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_isOrtho_nonTopBlockClosure
        H N hN beta hbeta
    exact ⟨hP, hOrtho.symm hx⟩
  · intro x hx
    rcases hx with ⟨hxP, hxOrth⟩
    have hQx : ((PairT)ᗮ).starProjection x ∈ PairN :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalProjection_mem_nonTop
        H N hN beta hbeta x hxP
    have hfix : ((PairT)ᗮ).starProjection x = x :=
      (Submodule.starProjection_eq_self_iff (K := (PairT)ᗮ)).2 hxOrth
    rw [hfix] at hQx
    exact hQx

/-- Every vector in the completed physical pair carrier has an actual completed
orthogonal decomposition into top-top and non-top components. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_exists_topTop_add_nonTop
    (x : PairE) (hx : x ∈ PairP) :
    ∃ t : PairE, t ∈ PairT ∧ ∃ n : PairE, n ∈ PairN ∧ t + n = x := by
  have hx' : x ∈ PairT ⊔ PairN := by
    rw [← periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_eq_topTopClosure_sup_nonTopClosure
      H N hN beta hbeta]
    exact hx
  rwa [Submodule.mem_sup] at hx'

/-- Audit-visible completed physical-pair Hilbert decomposition package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCarrierCompletedOrthogonalDecompositionPackage :
    Prop where
  completedDecomposition : PairP = PairT ⊔ PairN
  orthogonal : PairT ⟂ PairN
  relativeOrthogonalComplement : PairN = PairP ⊓ (PairT)ᗮ
  decomposes :
    ∀ x : PairE, x ∈ PairP →
      ∃ t : PairE, t ∈ PairT ∧ ∃ n : PairE, n ∈ PairN ∧ t + n = x

/-- Construct the completed physical-pair Hilbert decomposition package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrierCompletedOrthogonalDecompositionPackage :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCarrierCompletedOrthogonalDecompositionPackage
      H N hN beta hbeta :=
  { completedDecomposition :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_eq_topTopClosure_sup_nonTopClosure
        H N hN beta hbeta
    orthogonal :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_isOrtho_nonTopBlockClosure
        H N hN beta hbeta
    relativeOrthogonalComplement :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopClosure_eq_carrier_inf_topTopOrthogonal
        H N hN beta hbeta
    decomposes :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_exists_topTop_add_nonTop
        H N hN beta hbeta }

end CompletedPhysicalPairDecomposition

end

end MathlibAnalytic
end MGAP4D
