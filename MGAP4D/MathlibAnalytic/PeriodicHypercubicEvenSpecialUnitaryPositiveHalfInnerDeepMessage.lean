import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepFubiniIntegral
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfInnerDeepMessageIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfInnerDeepMessageCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfInnerDeepMessageSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfInnerDeepMessageMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfInnerDeepMessageBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfInnerDeepMessageSpatialLinkFintype (M : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink (M + 2)) :=
  Fintype.ofFinite _

/-- Every strict-interior coordinate produced by the outer-boundary split is
literally the corresponding complete-path slice at time `k+1`. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_interior_apply
    (H N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N)
    (k : Fin H) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
      H N path).2 k =
      path ⟨k.1 + 1, by
        simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩ := by
  let X : Fin 2 ⊕ Fin H → Type :=
    fun _ => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv H
  let reindex := MeasurableEquiv.piCongrLeft X e
  let j : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) :=
    ⟨k.1 + 1, by simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
  change reindex path (Sum.inr k) = path j
  have hEval : reindex path (e j) = path j := by
    simpa [reindex] using
      (MeasurableEquiv.piCongrLeft_apply_apply (β := X) e path j)
  have hj : e j = Sum.inr k := by
    simpa [e, j] using
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathTimeBoundaryInteriorEquiv_interior
        H k)
  rw [hj] at hEval
  exact hEval

/-- The erased first/last-slab Wilson product depends only on the strict
interior spatial path.  In particular, changing either outer reflection-fixed
boundary while keeping all times `1,...,H` fixed leaves the interior product
unchanged. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel_congr_of_interior_eq
    (H N : ℕ)
    (beta : ℝ)
    (path₁ path₂ : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N)
    (hInterior :
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
        H N path₁).2 =
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
        H N path₂).2) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel
        H N beta path₁ =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel
        H N beta path₂ := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel
  apply Finset.prod_congr rfl
  intro i hi
  have hiLast :
      i ≠ periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex H :=
    (Finset.mem_erase.mp hi).1
  have hiFirstMem :
      i ∈ (Finset.univ : Finset (Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))).erase
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex H) :=
    (Finset.mem_erase.mp hi).2
  have hiFirst :
      i ≠ periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex H :=
    (Finset.mem_erase.mp hiFirstMem).1
  have hiValNeZero : i.1 ≠ 0 := by
    intro h0
    apply hiFirst
    apply Fin.ext
    simpa using h0
  have hiValNeLast : i.1 ≠ H := by
    intro hlast
    apply hiLast
    apply Fin.ext
    simpa using hlast
  have hiPos : 1 ≤ i.1 := Nat.one_le_iff_ne_zero.mpr hiValNeZero
  have hiLt : i.1 < H := by
    have hbound : i.1 < H + 1 := by
      simpa [periodicHypercubicEvenPositiveHalfCylinderSlabCount] using i.2
    omega
  let kLeft : Fin H := ⟨i.1 - 1, by omega⟩
  let kRight : Fin H := ⟨i.1, hiLt⟩
  let jLeft : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) :=
    ⟨kLeft.1 + 1, by simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
  let jRight : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) :=
    ⟨kRight.1 + 1, by simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
  have hjLeft : jLeft = i.castSucc := by
    apply Fin.ext
    simp [jLeft, kLeft, Nat.sub_add_cancel hiPos]
  have hjRight : jRight = i.succ := by
    apply Fin.ext
    simp [jRight, kRight]
  have hLeft :
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path₁ i =
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path₂ i := by
    unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft
    calc
      path₁ i.castSucc = path₁ jLeft := by rw [hjLeft]
      _ =
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
            H N path₁).2 kLeft := by
        symm
        exact
          periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_interior_apply
            H N path₁ kLeft
      _ =
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
            H N path₂).2 kLeft := by rw [hInterior]
      _ = path₂ jLeft :=
        periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_interior_apply
          H N path₂ kLeft
      _ = path₂ i.castSucc := by rw [hjLeft]
  have hRight :
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path₁ i =
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path₂ i := by
    unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight
    calc
      path₁ i.succ = path₁ jRight := by rw [hjRight]
      _ =
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
            H N path₁).2 kRight := by
        symm
        exact
          periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_interior_apply
            H N path₁ kRight
      _ =
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
            H N path₂).2 kRight := by rw [hInterior]
      _ = path₂ jRight :=
        periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_interior_apply
          H N path₂ kRight
      _ = path₂ i.succ := by rw [hjRight]
  rw [hLeft, hRight]

/-- In the three-factor coordinates, the untouched interior Wilson product is
independent of the exposed outer boundary pair.  Only the inward pair and the
deeper interior remain. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepInteriorPathKernel_outer_independent
    (M N : ℕ)
    (beta : ℝ)
    (outer₁ outer₂ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N)
    (rest :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) ×
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPath M N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepInteriorPathKernel
        M N beta (outer₁, rest) =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepInteriorPathKernel
        M N beta (outer₂, rest) := by
  let outerSplit :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
      (M + 2) N
  let innerSplit :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv
      M N
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathOuterInnerDeepMeasurableEquiv M N
  let path₁ := e.symm (outer₁, rest)
  let path₂ := e.symm (outer₂, rest)
  have hStrict₁ : (outerSplit path₁).2 = innerSplit.symm rest := by
    have hs := congrArg (fun z => z.2) (e.apply_symm_apply (outer₁, rest))
    change innerSplit ((outerSplit path₁).2) = rest at hs
    apply innerSplit.injective
    calc
      innerSplit ((outerSplit path₁).2) = rest := hs
      _ = innerSplit (innerSplit.symm rest) := (innerSplit.apply_symm_apply rest).symm
  have hStrict₂ : (outerSplit path₂).2 = innerSplit.symm rest := by
    have hs := congrArg (fun z => z.2) (e.apply_symm_apply (outer₂, rest))
    change innerSplit ((outerSplit path₂).2) = rest at hs
    apply innerSplit.injective
    calc
      innerSplit ((outerSplit path₂).2) = rest := hs
      _ = innerSplit (innerSplit.symm rest) := (innerSplit.apply_symm_apply rest).symm
  have hStrict : (outerSplit path₁).2 = (outerSplit path₂).2 :=
    hStrict₁.trans hStrict₂.symm
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepInteriorPathKernel
  exact
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel_congr_of_interior_eq
      (M + 2) N beta path₁ path₂ hStrict

/-- A canonical harmless outer pair used only to name the outer-independent
interior message.  Both configurations are the identity link field. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfReferenceOuterPair
    (M N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N :=
  ((fun _ => 1), (fun _ => 1))

/-- The interior Wilson product as a function only of the inward pair and the
deeper path, with outer-boundary dependence removed by the preceding theorem. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerDeepInteriorPathKernel
    (M N : ℕ)
    (beta : ℝ)
    (rest :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) ×
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPath M N) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepInteriorPathKernel
    M N beta
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfReferenceOuterPair M N, rest)

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepInteriorPathKernel_eq_innerDeep
    (M N : ℕ)
    (beta : ℝ)
    (outer :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N)
    (rest :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) ×
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPath M N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepInteriorPathKernel
        M N beta (outer, rest) =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerDeepInteriorPathKernel
        M N beta rest := by
  exact
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepInteriorPathKernel_outer_independent
      M N beta outer
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfReferenceOuterPair M N) rest

/-- The inward pair receives the remaining deeper Wilson chain after integrating
out all still-deeper spatial slices. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage
    (M N : ℕ)
    (beta : ℝ)
    (inner :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) : ℝ :=
  ∫ deep,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerDeepInteriorPathKernel
      M N beta (inner, deep)
    ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPathHaarMeasure M N)

/-- The innermost deep-Haar integral factors into the actual pair one-step
kernel times the outer-independent inward message. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand_integral_deep_eq_pairKernel_mul_message
    (M N : ℕ)
    (beta : ℝ)
    (outer inner :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) :
    (∫ deep,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand
        M N beta (outer, (inner, deep))
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPathHaarMeasure M N)) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
          (M + 2) N beta (outer, inner) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage
          M N beta inner := by
  calc
    (∫ deep,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand
        M N beta (outer, (inner, deep))
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPathHaarMeasure M N)) =
      ∫ deep,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            (M + 2) N beta (outer, inner) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerDeepInteriorPathKernel
            M N beta (inner, deep)
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPathHaarMeasure M N) := by
      apply integral_congr_ae
      filter_upwards with deep
      simp [periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand]
    _ =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
          (M + 2) N beta (outer, inner) *
        (∫ deep,
          periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerDeepInteriorPathKernel
            M N beta (inner, deep)
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPathHaarMeasure M N)) := by
      rw [integral_const_mul]
    _ =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
          (M + 2) N beta (outer, inner) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage
          M N beta inner := by
      rfl

/-- After the deep variables have been integrated out, the complete path-Haar
amplitude is a genuine pair-Haar kernel integral with a constant outer state
and the inward Wilson message.  This is the immediate precursor of the ambient
Hilbert--Schmidt transfer-operator matrix coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugePathKernel_integral_eq_outer_inner_message
    (M N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (∫ path,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        (M + 2) N beta path
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (M + 2) N)) =
      ∫ outer, ∫ inner,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            (M + 2) N beta (outer, inner) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepHaarMessage
            M N beta inner
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N) := by
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugePathKernel_integral_eq_outer_inner_deep
    M N hN beta hbeta]
  apply integral_congr_ae
  filter_upwards with outer
  apply integral_congr_ae
  filter_upwards with inner
  exact
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand_integral_deep_eq_pairKernel_mul_message
      M N beta outer inner

end

end MathlibAnalytic
end MGAP4D
