import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2CanonicalSelectedMarginalCofinalTransferExtension
import MGAP4D.MathlibAnalytic.RealLinearIsometryProjectedCompression
import Mathlib.Tactic

/-!
# Directed selected-cylinder closure dynamics for canonical SU(2) pair transfer

PR #5087 showed that a cofinal sequence of selected projective marginals is
enough to build one bounded continuum operator.  Cofinality is stronger than
what the actual SU(2) three-mode continuum excitation needs.

The exact finite images and their continuum limit all live in the closure of
the union of the selected Wilson cylinder ranges.  On that closed Hilbert
subspace it is enough that the selected marginals form a directed family.

This file proves that general directed-closure extension and then specializes
it to the canonical selected SU(2) pair-transfer operators of #5086.

The selected family is theorem-generated to be directed from the coherent
readout's existing eventual-support property.  Thus no independent cofinality
assumption remains.

The only model-facing inputs left for the selected operator family are:

* one common norm bound;
* exact cross-scale transition compatibility of the canonical selected
  operators.

The operator is first extended to the selected-cylinder closure and then
extended to the ambient projective-limit L2 space by orthogonal projection to
that closed range.  Therefore the exact selected-marginal intertwining is
preserved while no assertion is made about unrelated continuum directions.

No H1-D5 compatibility, vacuum/top alignment, or rank-one forcing is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Function Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance directedProjectiveContinuumProbability
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    IsProbabilityMeasure L.continuumMeasure :=
  euclidean_yang_mills_projective_limit_probability L

/-- A uniformly bounded compatible operator family on a directed sequence of
selected Euclidean Yang--Mills finite marginals. -/
structure EuclideanYangMillsProjectiveLimitL2DirectedOperatorSystem
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) where
  marginalIndex : ℕ → Finset EuclideanFourSpace
  directed :
    ∀ n m : ℕ,
      ∃ k : ℕ,
        marginalIndex n ⊆ marginalIndex k ∧
        marginalIndex m ⊆ marginalIndex k
  localOperator :
    ∀ n : ℕ,
      Lp ℝ 2 (F.finiteMarginal (marginalIndex n)) →L[ℝ]
        Lp ℝ 2 (F.finiteMarginal (marginalIndex n))
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  local_norm_le :
    ∀ (n : ℕ)
      (f : Lp ℝ 2 (F.finiteMarginal (marginalIndex n))),
      ‖localOperator n f‖ ≤ bound * ‖f‖
  transition_intertwines :
    ∀ {n m : ℕ}
      (h : marginalIndex n ⊆ marginalIndex m)
      (f : Lp ℝ 2 (F.finiteMarginal (marginalIndex n))),
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) h (localOperator n f) =
        localOperator m
          (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
            (F := F) h f)

namespace EuclideanYangMillsProjectiveLimitL2DirectedOperatorSystem

variable
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (C : EuclideanYangMillsProjectiveLimitL2DirectedOperatorSystem F L)

noncomputable def cylinderSubspace
    (n : ℕ) :
    Submodule ℝ (Lp ℝ 2 L.continuumMeasure) :=
  L.finiteMarginalL2CylinderSubspace (C.marginalIndex n)

theorem cylinderSubspace_directed :
    Directed (· ≤ ·) C.cylinderSubspace := by
  intro n m
  obtain ⟨k, hnk, hmk⟩ := C.directed n m
  exact
    ⟨k,
      L.finiteMarginalL2CylinderSubspace_mono hnk,
      L.finiteMarginalL2CylinderSubspace_mono hmk⟩

noncomputable def finiteCylinderOperator
    (n : ℕ) :
    C.cylinderSubspace n →L[ℝ]
      Lp ℝ 2 L.continuumMeasure := by
  let e := L.finiteMarginalL2Pullback (C.marginalIndex n)
  let eInv :
      C.cylinderSubspace n →L[ℝ]
        Lp ℝ 2 (F.finiteMarginal (C.marginalIndex n)) :=
    (e.equivRange.symm.toContinuousLinearEquiv).toContinuousLinearMap
  exact
    e.toContinuousLinearMap.comp
      ((C.localOperator n).comp eInv)

@[simp]
theorem finiteCylinderOperator_apply
    (n : ℕ)
    (f : Lp ℝ 2 (F.finiteMarginal (C.marginalIndex n))) :
    C.finiteCylinderOperator n
        ((L.finiteMarginalL2Pullback
          (C.marginalIndex n)).equivRange f) =
      L.finiteMarginalL2Pullback
        (C.marginalIndex n) (C.localOperator n f) := by
  let e := L.finiteMarginalL2Pullback (C.marginalIndex n)
  have hinv :
      (e.equivRange.symm.toContinuousLinearEquiv)
          (e.equivRange f) = f :=
    e.equivRange.symm_apply_apply f
  change e
      (C.localOperator n
        ((e.equivRange.symm.toContinuousLinearEquiv) (e.equivRange f))) =
    e (C.localOperator n f)
  rw [hinv]

theorem finiteCylinderOperator_mem
    (n : ℕ)
    (x : C.cylinderSubspace n) :
    C.finiteCylinderOperator n x ∈ C.cylinderSubspace n := by
  rcases
      (L.finiteMarginalL2Pullback
        (C.marginalIndex n)).equivRange.surjective x
    with ⟨f, rfl⟩
  rw [C.finiteCylinderOperator_apply]
  exact
    (L.finiteMarginalL2Pullback
      (C.marginalIndex n)).equivRange (C.localOperator n f) |>.property

theorem finiteCylinderOperator_norm_le
    (n : ℕ)
    (x : C.cylinderSubspace n) :
    ‖C.finiteCylinderOperator n x‖ ≤ C.bound * ‖x‖ := by
  rcases
      (L.finiteMarginalL2Pullback
        (C.marginalIndex n)).equivRange.surjective x
    with ⟨f, rfl⟩
  rw [C.finiteCylinderOperator_apply]
  calc
    ‖L.finiteMarginalL2Pullback
        (C.marginalIndex n) (C.localOperator n f)‖ =
      ‖C.localOperator n f‖ :=
        L.finiteMarginalL2Pullback_norm _ _
    _ ≤ C.bound * ‖f‖ := C.local_norm_le n f
    _ = C.bound *
        ‖(L.finiteMarginalL2Pullback
          (C.marginalIndex n)).equivRange f‖ := by
      rw [(L.finiteMarginalL2Pullback
        (C.marginalIndex n)).equivRange.norm_map]

theorem finiteCylinderOperator_eq_comp_inclusion
    {n m : ℕ}
    (h : C.marginalIndex n ⊆ C.marginalIndex m) :
    (C.finiteCylinderOperator n).toLinearMap =
      (C.finiteCylinderOperator m).toLinearMap.comp
        (Submodule.inclusion
          (L.finiteMarginalL2CylinderSubspace_mono h)) := by
  apply LinearMap.ext
  intro x
  rcases
      (L.finiteMarginalL2Pullback
        (C.marginalIndex n)).equivRange.surjective x
    with ⟨f, rfl⟩
  have hInclusion :
      Submodule.inclusion
          (L.finiteMarginalL2CylinderSubspace_mono h)
          ((L.finiteMarginalL2Pullback
            (C.marginalIndex n)).equivRange f) =
        (L.finiteMarginalL2Pullback
          (C.marginalIndex m)).equivRange
          (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
            (F := F) h f) := by
    apply Subtype.ext
    exact L.finiteMarginalL2Pullback_compatible h f
  change
    C.finiteCylinderOperator n
        ((L.finiteMarginalL2Pullback
          (C.marginalIndex n)).equivRange f) =
      C.finiteCylinderOperator m
        (Submodule.inclusion
          (L.finiteMarginalL2CylinderSubspace_mono h)
          ((L.finiteMarginalL2Pullback
            (C.marginalIndex n)).equivRange f))
  rw [hInclusion,
    C.finiteCylinderOperator_apply,
    C.finiteCylinderOperator_apply]
  rw [← C.transition_intertwines h f]
  exact
    L.finiteMarginalL2Pullback_compatible
      h (C.localOperator n f)

theorem finiteCylinderOperator_agree_on_overlap
    (n m : ℕ)
    (x : Lp ℝ 2 L.continuumMeasure)
    (hxn : x ∈ C.cylinderSubspace n)
    (hxm : x ∈ C.cylinderSubspace m) :
    C.finiteCylinderOperator n ⟨x, hxn⟩ =
      C.finiteCylinderOperator m ⟨x, hxm⟩ := by
  obtain ⟨k, hnk, hmk⟩ := C.directed n m
  let hSubN := L.finiteMarginalL2CylinderSubspace_mono hnk
  let hSubM := L.finiteMarginalL2CylinderSubspace_mono hmk
  have hEqN := congrArg
    (fun T :
      C.cylinderSubspace n →ₗ[ℝ]
        Lp ℝ 2 L.continuumMeasure =>
      T ⟨x, hxn⟩)
    (C.finiteCylinderOperator_eq_comp_inclusion hnk)
  have hEqM := congrArg
    (fun T :
      C.cylinderSubspace m →ₗ[ℝ]
        Lp ℝ 2 L.continuumMeasure =>
      T ⟨x, hxm⟩)
    (C.finiteCylinderOperator_eq_comp_inclusion hmk)
  calc
    C.finiteCylinderOperator n ⟨x, hxn⟩ =
        C.finiteCylinderOperator k
          (Submodule.inclusion hSubN ⟨x, hxn⟩) := hEqN
    _ = C.finiteCylinderOperator k
          (Submodule.inclusion hSubM ⟨x, hxm⟩) :=
      congrArg (C.finiteCylinderOperator k) (Subtype.ext (by rfl))
    _ = C.finiteCylinderOperator m ⟨x, hxm⟩ := hEqM.symm

noncomputable def cylinderTotalSubspace :
    Submodule ℝ (Lp ℝ 2 L.continuumMeasure) :=
  ⨆ n : ℕ, C.cylinderSubspace n

theorem cylinderSubspace_le_total
    (n : ℕ) :
    C.cylinderSubspace n ≤ C.cylinderTotalSubspace :=
  le_iSup (fun m : ℕ => C.cylinderSubspace m) n

noncomputable def cylinderCoreOperator :
    C.cylinderTotalSubspace →ₗ[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  directedSubmoduleISupLift
    C.cylinderSubspace
    C.cylinderSubspace_directed
    (fun n => (C.finiteCylinderOperator n).toLinearMap)
    (fun n m x hxn hxm =>
      C.finiteCylinderOperator_agree_on_overlap n m x hxn hxm)

@[simp]
theorem cylinderCoreOperator_apply_selected
    (n : ℕ)
    (f : Lp ℝ 2 (F.finiteMarginal (C.marginalIndex n))) :
    C.cylinderCoreOperator
        (Submodule.inclusion
          (C.cylinderSubspace_le_total n)
          ((L.finiteMarginalL2Pullback
            (C.marginalIndex n)).equivRange f)) =
      L.finiteMarginalL2Pullback
        (C.marginalIndex n) (C.localOperator n f) := by
  change
    directedSubmoduleISupLift
        C.cylinderSubspace
        C.cylinderSubspace_directed
        (fun m => (C.finiteCylinderOperator m).toLinearMap)
        (fun i j x hxi hxj =>
          C.finiteCylinderOperator_agree_on_overlap i j x hxi hxj)
        (Submodule.inclusion
          (C.cylinderSubspace_le_total n)
          ((L.finiteMarginalL2Pullback
            (C.marginalIndex n)).equivRange f)) = _
  calc
    _ = C.finiteCylinderOperator n
          ((L.finiteMarginalL2Pullback
            (C.marginalIndex n)).equivRange f) :=
      directedSubmoduleISupLift_inclusion
        (K := C.cylinderSubspace)
        (dir := C.cylinderSubspace_directed)
        (f := fun m => (C.finiteCylinderOperator m).toLinearMap)
        (hf := fun i j x hxi hxj =>
          C.finiteCylinderOperator_agree_on_overlap i j x hxi hxj)
        ((L.finiteMarginalL2Pullback
          (C.marginalIndex n)).equivRange f)
        (C.cylinderSubspace_le_total n)
    _ = _ := C.finiteCylinderOperator_apply n f

theorem cylinderCoreOperator_of_mem
    (x : C.cylinderTotalSubspace)
    (n : ℕ)
    (hx : (x : Lp ℝ 2 L.continuumMeasure) ∈
      C.cylinderSubspace n) :
    C.cylinderCoreOperator x =
      C.finiteCylinderOperator n ⟨x, hx⟩ := by
  change
    directedSubmoduleISupLift
        C.cylinderSubspace
        C.cylinderSubspace_directed
        (fun m => (C.finiteCylinderOperator m).toLinearMap)
        (fun i j y hyi hyj =>
          C.finiteCylinderOperator_agree_on_overlap i j y hyi hyj)
        x = _
  exact directedSubmoduleISupLift_of_mem x hx

theorem cylinderCoreOperator_norm_le
    (x : C.cylinderTotalSubspace) :
    ‖C.cylinderCoreOperator x‖ ≤ C.bound * ‖x‖ := by
  have hxSup :
      (x : Lp ℝ 2 L.continuumMeasure) ∈
        ⨆ n : ℕ, C.cylinderSubspace n := by
    simpa [cylinderTotalSubspace] using x.property
  rcases
      (Submodule.mem_iSup_of_directed
        C.cylinderSubspace
        C.cylinderSubspace_directed).1 hxSup
    with ⟨n, hxn⟩
  rw [C.cylinderCoreOperator_of_mem x n hxn]
  simpa using
    C.finiteCylinderOperator_norm_le n ⟨x, hxn⟩

theorem cylinderCoreOperator_mem_total
    (x : C.cylinderTotalSubspace) :
    C.cylinderCoreOperator x ∈ C.cylinderTotalSubspace := by
  have hxSup :
      (x : Lp ℝ 2 L.continuumMeasure) ∈
        ⨆ n : ℕ, C.cylinderSubspace n := by
    simpa [cylinderTotalSubspace] using x.property
  rcases
      (Submodule.mem_iSup_of_directed
        C.cylinderSubspace
        C.cylinderSubspace_directed).1 hxSup
    with ⟨n, hxn⟩
  rw [C.cylinderCoreOperator_of_mem x n hxn]
  exact
    C.cylinderSubspace_le_total n
      (C.finiteCylinderOperator_mem n ⟨x, hxn⟩)

noncomputable def selectedClosure :
    Submodule ℝ (Lp ℝ 2 L.continuumMeasure) :=
  C.cylinderTotalSubspace.topologicalClosure

local instance selectedClosureCompleteSpace :
    CompleteSpace C.selectedClosure := by
  have hclosed :
      IsClosed
        (C.selectedClosure :
          Set (Lp ℝ 2 L.continuumMeasure)) := by
    exact Submodule.isClosed_topologicalClosure _
  exact hclosed.completeSpace_coe

noncomputable def cylinderCoreInclusion :
    C.cylinderTotalSubspace →ₗ[ℝ] C.selectedClosure :=
  Submodule.inclusion
    (Submodule.le_topologicalClosure C.cylinderTotalSubspace)

theorem cylinderCoreInclusion_denseRange :
    DenseRange C.cylinderCoreInclusion := by
  rw [DenseRange, Subtype.dense_iff]
  intro y hy
  change
    y ∈ closure
      (((↑) :
          C.selectedClosure →
            Lp ℝ 2 L.continuumMeasure) ''
        Set.range C.cylinderCoreInclusion)
  have hRange :
      (((↑) :
          C.selectedClosure →
            Lp ℝ 2 L.continuumMeasure) ''
        Set.range C.cylinderCoreInclusion) =
      (C.cylinderTotalSubspace :
        Set (Lp ℝ 2 L.continuumMeasure)) := by
    ext z
    constructor
    · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
      exact x.property
    · intro hz
      let x : C.cylinderTotalSubspace := ⟨z, hz⟩
      refine
        ⟨C.cylinderCoreInclusion x, ⟨x, rfl⟩, ?_⟩
      rfl
  rw [hRange]
  simpa only [
    selectedClosure,
    Submodule.topologicalClosure_coe
  ] using hy

noncomputable def cylinderCoreOperatorToClosure :
    C.cylinderTotalSubspace →ₗ[ℝ] C.selectedClosure :=
  C.cylinderCoreOperator.codRestrict
    C.selectedClosure
    (fun x =>
      Submodule.le_topologicalClosure C.cylinderTotalSubspace
        (C.cylinderCoreOperator_mem_total x))

theorem cylinderCoreOperatorToClosure_norm_le
    (x : C.cylinderTotalSubspace) :
    ‖C.cylinderCoreOperatorToClosure x‖ ≤
      C.bound * ‖x‖ := by
  change ‖C.cylinderCoreOperator x‖ ≤ C.bound * ‖x‖
  exact C.cylinderCoreOperator_norm_le x

noncomputable def closureOperator :
    C.selectedClosure →L[ℝ] C.selectedClosure :=
  C.cylinderCoreOperatorToClosure.extendOfNorm
    C.cylinderCoreInclusion

theorem closureOperator_apply_core
    (x : C.cylinderTotalSubspace) :
    C.closureOperator (C.cylinderCoreInclusion x) =
      C.cylinderCoreOperatorToClosure x := by
  simpa [closureOperator] using
    (LinearMap.extendOfNorm_eq
      (f := C.cylinderCoreOperatorToClosure)
      (e := C.cylinderCoreInclusion)
      C.cylinderCoreInclusion_denseRange
      ⟨C.bound, C.cylinderCoreOperatorToClosure_norm_le⟩ x)

theorem closureOperator_opNorm_le :
    ‖C.closureOperator‖ ≤ C.bound := by
  simpa [closureOperator] using
    (LinearMap.opNorm_extendOfNorm_le
      (f := C.cylinderCoreOperatorToClosure)
      (e := C.cylinderCoreInclusion)
      C.cylinderCoreInclusion_denseRange
      C.bound_nonneg
      C.cylinderCoreOperatorToClosure_norm_le)

noncomputable def selectedEmbedClosure
    (n : ℕ)
    (f : Lp ℝ 2 (F.finiteMarginal (C.marginalIndex n))) :
    C.selectedClosure :=
  C.cylinderCoreInclusion
    (Submodule.inclusion
      (C.cylinderSubspace_le_total n)
      ((L.finiteMarginalL2Pullback
        (C.marginalIndex n)).equivRange f))

@[simp]
theorem selectedEmbedClosure_coe
    (n : ℕ)
    (f : Lp ℝ 2 (F.finiteMarginal (C.marginalIndex n))) :
    ((C.selectedEmbedClosure n f : C.selectedClosure) :
      Lp ℝ 2 L.continuumMeasure) =
      L.finiteMarginalL2Pullback (C.marginalIndex n) f := by
  rfl

theorem closureOperator_intertwines_selected
    (n : ℕ)
    (f : Lp ℝ 2 (F.finiteMarginal (C.marginalIndex n))) :
    C.closureOperator (C.selectedEmbedClosure n f) =
      C.selectedEmbedClosure n (C.localOperator n f) := by
  unfold selectedEmbedClosure
  rw [C.closureOperator_apply_core]
  apply Subtype.ext
  exact C.cylinderCoreOperator_apply_selected n f

/-- Extend the closure operator to all continuum L2 by orthogonal projection to
the closed selected-cylinder carrier. -/
noncomputable def ambientContinuumOperator :
    Lp ℝ 2 L.continuumMeasure →L[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  realLinearIsometryProjectedCompression
    C.selectedClosure.subtypeₗᵢ
    C.closureOperator

theorem ambientContinuumOperator_opNorm_le :
    ‖C.ambientContinuumOperator‖ ≤ C.bound := by
  calc
    ‖C.ambientContinuumOperator‖ ≤ ‖C.closureOperator‖ :=
      realLinearIsometryProjectedCompression_opNorm_le
        C.selectedClosure.subtypeₗᵢ C.closureOperator
    _ ≤ C.bound := C.closureOperator_opNorm_le

theorem ambientContinuumOperator_intertwines_selected
    (n : ℕ)
    (f : Lp ℝ 2 (F.finiteMarginal (C.marginalIndex n))) :
    C.ambientContinuumOperator
        (L.finiteMarginalL2Pullback (C.marginalIndex n) f) =
      L.finiteMarginalL2Pullback
        (C.marginalIndex n) (C.localOperator n f) := by
  let z := C.selectedEmbedClosure n f
  have hz :
      C.closureOperator z =
        C.selectedEmbedClosure n (C.localOperator n f) :=
    C.closureOperator_intertwines_selected n f
  calc
    C.ambientContinuumOperator
        (L.finiteMarginalL2Pullback (C.marginalIndex n) f) =
      C.ambientContinuumOperator
        (C.selectedClosure.subtypeₗᵢ z) := by
          rw [selectedEmbedClosure_coe]
    _ = C.selectedClosure.subtypeₗᵢ (C.closureOperator z) := by
      exact
        realLinearIsometryProjectedCompression_apply_map
          C.selectedClosure.subtypeₗᵢ C.closureOperator z
    _ = C.selectedClosure.subtypeₗᵢ
        (C.selectedEmbedClosure n (C.localOperator n f)) := by
      rw [hz]
    _ = L.finiteMarginalL2Pullback
        (C.marginalIndex n) (C.localOperator n f) := by
      rw [selectedEmbedClosure_coe]

end EuclideanYangMillsProjectiveLimitL2DirectedOperatorSystem

local instance su2DirectedSelectedTransferTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2DirectedSelectedTransferCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2DirectedSelectedTransferSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2DirectedSelectedTransferMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2DirectedSelectedTransferBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2DirectedSelectedTransferSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2DirectedSelectedTransferSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance su2DirectedSelectedTransferNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section SU2DirectedSelectedTransfer

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)

structure PhysicalYangMillsSU2CanonicalSelectedMarginalPairTransferDirectedInput where
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  canonical_norm_le :
    ∀ (n : ℕ)
      (f : Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n))),
      ‖physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator
          Q R n f‖ ≤
        bound * ‖f‖
  transition_intertwines :
    ∀ {n m : ℕ}
      (h : R.marginalIndex n ⊆ R.marginalIndex m)
      (f : Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n))),
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) h
          (physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator
            Q R n f) =
        physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator
          Q R m
          (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
            (F := F) h f)

namespace PhysicalYangMillsSU2CanonicalSelectedMarginalPairTransferDirectedInput

variable
    (C :
      PhysicalYangMillsSU2CanonicalSelectedMarginalPairTransferDirectedInput
        Q R)

/-- The coherent readout already makes the selected marginal family directed. -/
theorem selectedMarginal_directed
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (n m : ℕ) :
    ∃ k : ℕ,
      R.marginalIndex n ⊆ R.marginalIndex k ∧
      R.marginalIndex m ⊆ R.marginalIndex k := by
  have hn := G.marginalSupportEventually n
  have hm := G.marginalSupportEventually m
  have hBoth :
      ∀ᶠ k in atTop,
        R.marginalIndex n ⊆ R.marginalIndex k ∧
        R.marginalIndex m ⊆ R.marginalIndex k := by
    filter_upwards [hn, hm] with k hnk hmk
    exact ⟨hnk, hmk⟩
  exact hBoth.exists

noncomputable def toDirectedOperatorSystem
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
    EuclideanYangMillsProjectiveLimitL2DirectedOperatorSystem F L where
  marginalIndex := R.marginalIndex
  directed := selectedMarginal_directed Q R L C hInvariant G
  localOperator :=
    physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator Q R
  bound := C.bound
  bound_nonneg := C.bound_nonneg
  local_norm_le := C.canonical_norm_le
  transition_intertwines := C.transition_intertwines

noncomputable def continuumTransfer
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
    Lp ℝ 2 L.continuumMeasure →L[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  EuclideanYangMillsProjectiveLimitL2DirectedOperatorSystem.ambientContinuumOperator
    (toDirectedOperatorSystem Q R L C hInvariant G)

theorem continuumTransfer_intertwines_pairTransfer
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (n : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2) :
    continuumTransfer Q R L C hInvariant G
        (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
          Q R L n x) =
      physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
        Q R L n
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) x) := by
  rw [
    physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding_eq_finitePullback
      Q R L n x,
    physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding_eq_finitePullback
      Q R L n
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) x)]
  unfold continuumTransfer
  have hGeneric :=
    EuclideanYangMillsProjectiveLimitL2DirectedOperatorSystem.ambientContinuumOperator_intertwines_selected
      (toDirectedOperatorSystem Q R L C hInvariant G) n
      (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n x)
  calc
    _ =
        L.finiteMarginalL2Pullback (R.marginalIndex n)
          (physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator
            Q R n
            (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n x)) := by
      simpa only [toDirectedOperatorSystem] using hGeneric
    _ = _ := by
      rw [
        physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator_apply_embedding
          Q R n x]

theorem continuumTransfer_pow_intertwines_pairTransfer
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (n m : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2) :
    (continuumTransfer Q R L C hInvariant G ^ m)
        (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
          Q R L n x) =
      physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
        Q R L n
        ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) ^ m) x) := by
  let T := continuumTransfer Q R L C hInvariant G
  let Sn :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
  let J :=
    physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
      Q R L n
  change (T ^ m) (J x) = J ((Sn ^ m) x)
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      change (T ^ m) (T (J x)) = J ((Sn ^ m) (Sn x))
      have hstep : T (J x) = J (Sn x) := by
        simpa [T, Sn, J] using
          continuumTransfer_intertwines_pairTransfer Q R L C hInvariant G n x
      rw [hstep]
      exact ih (Sn x)

theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage_eq_continuumTransfer_pow
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (n m : ℕ) :
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
        Q R L hInvariant n m =
      (continuumTransfer Q R L C hInvariant G ^ m)
        (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
          Q R L n
          (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
            Q hInvariant n)) := by
  unfold
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
  exact
    (continuumTransfer_pow_intertwines_pairTransfer Q R L C
      hInvariant G n m
      (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
        Q hInvariant n)).symm

theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_sameSubsequence_evolved_strong_limits
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ y : Lp ℝ 2 L.continuumMeasure,
        ‖y‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
            (fun j =>
              physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                Q R L hInvariant (phi j) m)
            atTop
            (𝓝 ((continuumTransfer Q R L C hInvariant G ^ m) y)) := by
  obtain ⟨phi, hphi, cInf, hcInf, hInitial, hyNorm⟩ :=
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_projective_strong_limit
      Q R L hInvariant G
  let y :=
    physicalYangMillsSU2ThreeModeContinuumSynthesis
      Q R L hInvariant G cInf
  refine ⟨phi, hphi, y, by simpa [y] using hyNorm, ?_⟩
  intro m
  have hPow :
      Tendsto
        (fun j =>
          (continuumTransfer Q R L C hInvariant G ^ m)
            (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
              Q R L (phi j)
              (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
                Q hInvariant (phi j))))
        atTop
        (𝓝 ((continuumTransfer Q R L C hInvariant G ^ m) y)) := by
    have hMap :=
      (((continuumTransfer Q R L C hInvariant G ^ m).continuous.tendsto y).comp
        hInitial)
    simpa [y] using hMap
  apply hPow.congr'
  exact Filter.Eventually.of_forall fun j =>
    (physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage_eq_continuumTransfer_pow Q R L C
      hInvariant G (phi j) m).symm

theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_continuumDiscreteTime_q0
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ y : Lp ℝ 2 L.continuumMeasure,
        ‖y‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
              (fun j =>
                physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                  Q R L hInvariant (phi j) m)
              atTop
              (𝓝 ((continuumTransfer Q R L C hInvariant G ^ m) y)) ∧
            ‖(continuumTransfer Q R L C hInvariant G ^ m) y‖ ≤
              GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  obtain ⟨phi, hphi, y, hyNorm, hStrong⟩ :=
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_sameSubsequence_evolved_strong_limits Q R L C
      hInvariant G
  refine ⟨phi, hphi, y, hyNorm, ?_⟩
  intro m
  refine ⟨hStrong m, ?_⟩
  exact
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveStrongLimit_norm_le_uniform_q0
      Q R L hInvariant s hs hcut phi m
      ((continuumTransfer Q R L C hInvariant G ^ m) y)
      (hStrong m)

theorem continuumTransfer_pow_add_apply
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (G :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (m k : ℕ)
    (y : Lp ℝ 2 L.continuumMeasure) :
    (continuumTransfer Q R L C hInvariant G ^ (m + k)) y =
      (continuumTransfer Q R L C hInvariant G ^ m)
        ((continuumTransfer Q R L C hInvariant G ^ k) y) := by
  rw [pow_add]
  rfl

end PhysicalYangMillsSU2CanonicalSelectedMarginalPairTransferDirectedInput

end SU2DirectedSelectedTransfer

end

end MathlibAnalytic
end MGAP4D
