import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2CanonicalSelectedMarginalPairTransferCompression
import MGAP4D.MathlibAnalytic.ProjectiveLimitFiniteMarginalL2CompatibleOperatorExtension
import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitL2CylinderDensity
import Mathlib.Tactic

/-!
# Cofinal selected-marginal extension of the canonical SU(2) pair transfer

PR #5085 showed that a compatible operator system on every finite projective
marginal produces one bounded continuum operator whose powers describe the
same-subsequence evolved limits of the exact SU(2) three-mode excitation.

PR #5086 removed the selected-marginal realization assumption: at every scale
the actual normalized physical pair transfer has a canonical selected-marginal
realization by projected compression through the pair-Haar/projective
isometric embedding.

This file removes the unnecessarily strong requirement that operators be
specified on all finite marginals.

First, a generic theorem is proved for a cofinal sequence of finite Euclidean
Yang--Mills marginals. A uniformly bounded family of operators on those
selected marginals, compatible whenever one selected marginal is contained in
another, glues on the directed union of their continuum cylinder ranges.
Cofinality makes that union dense because it contains every finite-coordinate
cylinder subspace. Mathlib's LinearMap.extendOfNorm then gives one bounded
continuum operator with exact selected-marginal intertwining.

Second, this generic theorem is specialized to the canonical selected SU(2)
pair-transfer operators of #5086.

Thus H1-C3 no longer needs a full finite-marginal operator system. The
remaining data are only cofinality, one uniform bound, and cross-scale
transition compatibility of the canonical selected operators.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Function Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance cofinalProjectiveContinuumProbability
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    IsProbabilityMeasure L.continuumMeasure :=
  euclidean_yang_mills_projective_limit_probability L

structure EuclideanYangMillsProjectiveLimitL2CofinalOperatorSystem
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) where
  marginalIndex : ℕ → Finset EuclideanFourSpace
  cofinal :
    ∀ J : Finset EuclideanFourSpace,
      ∃ n : ℕ, J ⊆ marginalIndex n
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
          (F := F) h
          (localOperator n f) =
        localOperator m
          (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
            (F := F) h f)

namespace EuclideanYangMillsProjectiveLimitL2CofinalOperatorSystem

variable
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (C : EuclideanYangMillsProjectiveLimitL2CofinalOperatorSystem F L)

noncomputable def cylinderSubspace
    (n : ℕ) :
    Submodule ℝ (Lp ℝ 2 L.continuumMeasure) :=
  L.finiteMarginalL2CylinderSubspace (C.marginalIndex n)

noncomputable def finiteCylinderOperator
    (n : ℕ) :
    C.cylinderSubspace n →L[ℝ]
      Lp ℝ 2 L.continuumMeasure := by
  let e :=
    L.finiteMarginalL2Pullback (C.marginalIndex n)
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
      L.finiteMarginalL2Pullback (C.marginalIndex n)
        (C.localOperator n f) := by
  let e :=
    L.finiteMarginalL2Pullback (C.marginalIndex n)
  have hinv :
      (e.equivRange.symm.toContinuousLinearEquiv)
          (e.equivRange f) = f :=
    e.equivRange.symm_apply_apply f
  change e
      (C.localOperator n
        ((e.equivRange.symm.toContinuousLinearEquiv) (e.equivRange f))) =
    e (C.localOperator n f)
  rw [hinv]

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
    ‖L.finiteMarginalL2Pullback (C.marginalIndex n)
        (C.localOperator n f)‖ =
      ‖C.localOperator n f‖ :=
        L.finiteMarginalL2Pullback_norm _ _
    _ ≤ C.bound * ‖f‖ := C.local_norm_le n f
    _ = C.bound *
        ‖(L.finiteMarginalL2Pullback
          (C.marginalIndex n)).equivRange f‖ := by
      rw [(L.finiteMarginalL2Pullback
        (C.marginalIndex n)).equivRange.norm_map]

theorem cylinderSubspace_directed :
    Directed (· ≤ ·) C.cylinderSubspace := by
  intro n m
  obtain ⟨k, hk⟩ :=
    C.cofinal (C.marginalIndex n ∪ C.marginalIndex m)
  have hnk : C.marginalIndex n ⊆ C.marginalIndex k := by
    intro x hx
    exact hk (by simp [hx])
  have hmk : C.marginalIndex m ⊆ C.marginalIndex k := by
    intro x hx
    exact hk (by simp [hx])
  exact
    ⟨k,
      L.finiteMarginalL2CylinderSubspace_mono hnk,
      L.finiteMarginalL2CylinderSubspace_mono hmk⟩

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
    exact
      L.finiteMarginalL2Pullback_compatible h f
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
  obtain ⟨k, hk⟩ :=
    C.cofinal (C.marginalIndex n ∪ C.marginalIndex m)
  have hnk : C.marginalIndex n ⊆ C.marginalIndex k := by
    intro y hy
    exact hk (by simp [hy])
  have hmk : C.marginalIndex m ⊆ C.marginalIndex k := by
    intro y hy
    exact hk (by simp [hy])
  let hSubN :=
    L.finiteMarginalL2CylinderSubspace_mono hnk
  let hSubM :=
    L.finiteMarginalL2CylinderSubspace_mono hmk
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

theorem fullCylinderTotalSubspace_le_cylinderTotalSubspace :
    L.finiteMarginalL2CylinderTotalSubspace ≤
      C.cylinderTotalSubspace := by
  unfold
    EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2CylinderTotalSubspace
  refine iSup_le ?_
  intro J
  obtain ⟨n, hJn⟩ := C.cofinal J
  exact
    (L.finiteMarginalL2CylinderSubspace_mono hJn).trans
      (C.cylinderSubspace_le_total n)

theorem cylinderTotalSubspace_topologicalClosure_eq_top :
    C.cylinderTotalSubspace.topologicalClosure = ⊤ := by
  apply le_antisymm le_top
  rw [← L.finiteMarginalL2CylinderTotalSubspace_topologicalClosure_eq_top]
  exact
    Submodule.topologicalClosure_mono
      C.fullCylinderTotalSubspace_le_cylinderTotalSubspace

theorem cylinderTotalSubspace_dense :
    Dense
      (C.cylinderTotalSubspace :
        Set (Lp ℝ 2 L.continuumMeasure)) := by
  exact
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      C.cylinderTotalSubspace_topologicalClosure_eq_top

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
      L.finiteMarginalL2Pullback (C.marginalIndex n)
        (C.localOperator n f) := by
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
  exact
    directedSubmoduleISupLift_of_mem x hx

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

theorem cylinderCoreSubtype_denseRange :
    DenseRange C.cylinderTotalSubspace.subtype := by
  simpa [DenseRange] using C.cylinderTotalSubspace_dense

noncomputable def continuumOperator :
    Lp ℝ 2 L.continuumMeasure →L[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  C.cylinderCoreOperator.extendOfNorm
    C.cylinderTotalSubspace.subtype

theorem continuumOperator_apply_core
    (x : C.cylinderTotalSubspace) :
    continuumOperator C (x : Lp ℝ 2 L.continuumMeasure) =
      C.cylinderCoreOperator x := by
  simpa [continuumOperator] using
    (LinearMap.extendOfNorm_eq
      (f := C.cylinderCoreOperator)
      (e := C.cylinderTotalSubspace.subtype)
      C.cylinderCoreSubtype_denseRange
      ⟨C.bound, C.cylinderCoreOperator_norm_le⟩ x)

theorem continuumOperator_intertwines_selected
    (n : ℕ)
    (f : Lp ℝ 2 (F.finiteMarginal (C.marginalIndex n))) :
    continuumOperator C
        (L.finiteMarginalL2Pullback
          (C.marginalIndex n) f) =
      L.finiteMarginalL2Pullback
        (C.marginalIndex n)
        (C.localOperator n f) := by
  let x :=
    Submodule.inclusion
      (C.cylinderSubspace_le_total n)
      ((L.finiteMarginalL2Pullback
        (C.marginalIndex n)).equivRange f)
  have hxval :
      (x : Lp ℝ 2 L.continuumMeasure) =
        L.finiteMarginalL2Pullback
          (C.marginalIndex n) f := rfl
  rw [← hxval, continuumOperator_apply_core C x]
  exact C.cylinderCoreOperator_apply_selected n f

theorem continuumOperator_norm_le
    (x : Lp ℝ 2 L.continuumMeasure) :
    ‖continuumOperator C x‖ ≤ C.bound * ‖x‖ := by
  simpa [continuumOperator] using
    (LinearMap.norm_extendOfNorm_apply_le
      (f := C.cylinderCoreOperator)
      (e := C.cylinderTotalSubspace.subtype)
      C.cylinderCoreSubtype_denseRange
      C.bound C.cylinderCoreOperator_norm_le x)

theorem continuumOperator_opNorm_le :
    ‖continuumOperator C‖ ≤ C.bound := by
  simpa [continuumOperator] using
    (LinearMap.opNorm_extendOfNorm_le
      (f := C.cylinderCoreOperator)
      (e := C.cylinderTotalSubspace.subtype)
      C.cylinderCoreSubtype_denseRange
      C.bound_nonneg C.cylinderCoreOperator_norm_le)

end EuclideanYangMillsProjectiveLimitL2CofinalOperatorSystem

local instance su2CofinalSelectedTransferTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2CofinalSelectedTransferCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2CofinalSelectedTransferSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2CofinalSelectedTransferMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2CofinalSelectedTransferBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2CofinalSelectedTransferSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2CofinalSelectedTransferSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance su2CofinalSelectedTransferNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section SU2CofinalSelectedTransfer

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

structure PhysicalYangMillsSU2CanonicalSelectedMarginalPairTransferCofinalInput where
  cofinal :
    ∀ J : Finset EuclideanFourSpace,
      ∃ n : ℕ, J ⊆ R.marginalIndex n
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

namespace PhysicalYangMillsSU2CanonicalSelectedMarginalPairTransferCofinalInput

variable
    (C :
      PhysicalYangMillsSU2CanonicalSelectedMarginalPairTransferCofinalInput
        Q R)

noncomputable def toCofinalOperatorSystem :
    EuclideanYangMillsProjectiveLimitL2CofinalOperatorSystem F L where
  marginalIndex := R.marginalIndex
  cofinal := C.cofinal
  localOperator :=
    physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator Q R
  bound := C.bound
  bound_nonneg := C.bound_nonneg
  local_norm_le := C.canonical_norm_le
  transition_intertwines := C.transition_intertwines

noncomputable def continuumTransfer :
    Lp ℝ 2 L.continuumMeasure →L[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  EuclideanYangMillsProjectiveLimitL2CofinalOperatorSystem.continuumOperator
    (toCofinalOperatorSystem Q R L C)

theorem continuumTransfer_intertwines_pairTransfer
    (n : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2) :
    continuumTransfer Q R L C
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
  calc
    _ =
        L.finiteMarginalL2Pullback (R.marginalIndex n)
          (physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator
            Q R n
            (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n x)) := by
      simpa only [toCofinalOperatorSystem] using
        (EuclideanYangMillsProjectiveLimitL2CofinalOperatorSystem.continuumOperator_intertwines_selected
          (toCofinalOperatorSystem Q R L C) n
          (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n x))
    _ = _ := by
      rw [
        physicalYangMillsSU2CanonicalSelectedMarginalPairTransferOperator_apply_embedding
          Q R n x]

theorem continuumTransfer_pow_intertwines_pairTransfer
    (n m : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2) :
    (continuumTransfer Q R L C ^ m)
        (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
          Q R L n x) =
      physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
        Q R L n
        ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) ^ m) x) := by
  let T := continuumTransfer Q R L C
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
          continuumTransfer_intertwines_pairTransfer Q R L C n x
      rw [hstep]
      exact ih (Sn x)

theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage_eq_continuumTransfer_pow
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n m : ℕ) :
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
        Q R L hInvariant n m =
      (continuumTransfer Q R L C ^ m)
        (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
          Q R L n
          (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
            Q hInvariant n)) := by
  unfold
    physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
  exact
    (continuumTransfer_pow_intertwines_pairTransfer Q R L C
      n m
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
            (𝓝 ((continuumTransfer Q R L C ^ m) y)) := by
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
          (continuumTransfer Q R L C ^ m)
            (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
              Q R L (phi j)
              (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
                Q hInvariant (phi j))))
        atTop
        (𝓝 ((continuumTransfer Q R L C ^ m) y)) := by
    have hMap :=
      (((continuumTransfer Q R L C ^ m).continuous.tendsto y).comp hInitial)
    simpa [y] using hMap
  apply hPow.congr'
  exact Filter.Eventually.of_forall fun j =>
    (physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage_eq_continuumTransfer_pow Q R L C
      hInvariant (phi j) m).symm

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
              (𝓝 ((continuumTransfer Q R L C ^ m) y)) ∧
            ‖(continuumTransfer Q R L C ^ m) y‖ ≤
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
      ((continuumTransfer Q R L C ^ m) y)
      (hStrong m)

theorem continuumTransfer_pow_add_apply
    (m k : ℕ)
    (y : Lp ℝ 2 L.continuumMeasure) :
    (continuumTransfer Q R L C ^ (m + k)) y =
      (continuumTransfer Q R L C ^ m)
        ((continuumTransfer Q R L C ^ k) y) := by
  rw [pow_add]
  rfl

end PhysicalYangMillsSU2CanonicalSelectedMarginalPairTransferCofinalInput

end SU2CofinalSelectedTransfer

end

end MathlibAnalytic
end MGAP4D
