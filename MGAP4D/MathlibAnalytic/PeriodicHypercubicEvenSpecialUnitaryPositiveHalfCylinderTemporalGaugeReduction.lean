import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeAction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- One temporal-link field for each adjacent slab of the positive reflection
half-cylinder.  At a fixed slab, the field is indexed by spatial-slice vertices
and records the actual time-like link variable before temporal gauge fixing. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField
    (H N : ℕ) : Type :=
  Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) →
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N

/-- Read a slab temporal-link field at a natural index, returning the identity
outside the physical slab range.  This auxiliary totalization is used only to
form ordered prefix products. -/
private def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkAtNat
    {H N : ℕ}
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N)
    (k : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N :=
  if hk : k < periodicHypercubicEvenPositiveHalfCylinderSlabCount H then
    U ⟨k, hk⟩
  else
    1

/-- Ordered cumulative gauge field from the primary fixed slice to one slice
of the positive half-cylinder.  The order is Euclidean time order, so this
works for the noncommutative `SU(N)` gauge group. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge
    (H N : ℕ)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N)
    (j : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1)) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N :=
  ((List.range j.1).map fun k =>
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkAtNat U k).prod

/-- The cumulative gauge field at the primary fixed slice is the identity. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge_zero
    (H N : ℕ)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge
        H N U ⟨0, Nat.zero_lt_succ _⟩ = 1 := by
  simp [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge]

/-- Moving across one slab multiplies the cumulative gauge field by that slab's
temporal-link field on the right. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge_succ
    (H N : ℕ)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge H N U i.succ =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge
          H N U i.castSucc * U i := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge
  rw [show List.range i.succ.1 = List.range i.castSucc.1 ++ [i.1] by
    simp [List.range_succ]]
  simp [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkAtNat,
    i.2]

/-- Pointwise form of the cumulative-gauge recursion. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge_succ_apply
    (H N : ℕ)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (v : PeriodicHypercubicEvenSpatialSliceVertex H) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge H N U i.succ v =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge
          H N U i.castSucc v * U i v := by
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge_succ]
  rfl

/-- The time-like link after applying the cumulative gauge field on its two
endpoint slices. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderGaugeFixedTemporalLink
    (H N : ℕ)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (v : PeriodicHypercubicEvenSpatialSliceVertex H) :
    Matrix.specialUnitaryGroup (Fin N) ℂ :=
  periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge
      H N U i.castSucc v *
    U i v *
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge
      H N U i.succ v)⁻¹

/-- The recursively constructed cumulative gauge field sends every positive
half-cylinder temporal link exactly to the identity. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderGaugeFixedTemporalLink_eq_one
    (H N : ℕ)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (v : PeriodicHypercubicEvenSpatialSliceVertex H) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderGaugeFixedTemporalLink
        H N U i v = 1 := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderGaugeFixedTemporalLink
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge_succ_apply]
  group

/-- The unfixed temporal crossing action of one actual slab.  The temporal-link
field appears at the two spatial endpoints of each link.  After temporal gauge
fixing this becomes the canonical relative-boundary crossing action. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryUnfixedTemporalCrossingAction
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (U : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ((periodicHypercubicEvenSpatialSliceLinkList H).map fun e =>
    specialUnitaryWilsonPlaquetteEnergy N
      ((A e)⁻¹ * U e.1 * B e *
        (U (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹)).sum

/-- Relative boundary variable after applying a lower-slice gauge field `γ` and
the upper-slice field `γ * U`.  It is conjugate to the unfixed temporal
plaquette word by the lower gauge field at the spatial target vertex. -/
theorem
    periodicHypercubicEvenSpecialUnitaryUnfixedTemporalRelative_gaugeReduction
    (H N : ℕ)
    (γ U : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ((periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A e)⁻¹ *
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N (γ * U) B e) =
      γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2) *
        ((A e)⁻¹ * U e.1 * B e *
          (U (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹) *
        (γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹ := by
  simp [periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform]
  group

/-- Exact one-slab temporal-gauge reduction of the crossing action. -/
theorem
    periodicHypercubicEvenSpecialUnitaryUnfixedTemporalCrossingAction_eq_temporalGauge
    (H N : ℕ)
    (γ U : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryUnfixedTemporalCrossingAction H N A U B =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N (γ * U) B) := by
  unfold periodicHypercubicEvenSpecialUnitaryUnfixedTemporalCrossingAction
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
  simp_rw [periodicHypercubicEvenSpecialUnitaryUnfixedTemporalRelative_gaugeReduction]
  simp_rw [specialUnitaryWilsonPlaquetteEnergy_conjInvariant]

/-- Symmetric unfixed one-slab Wilson action: spatial half-actions on the two
boundary slices plus the actual temporal-link crossing action. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabAction
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (U : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  (1 / 2 : ℝ) * periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N A +
    periodicHypercubicEvenSpecialUnitaryUnfixedTemporalCrossingAction H N A U B +
    (1 / 2 : ℝ) * periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N B

/-- Exact one-slab action equality after temporal gauge fixing. -/
theorem periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabAction_eq_temporalGauge
    (H N : ℕ)
    (γ U : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabAction H N A U B =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N (γ * U) B) := by
  unfold periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabAction
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant]
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant]
  rw [periodicHypercubicEvenSpecialUnitaryUnfixedTemporalCrossingAction_eq_temporalGauge]

/-- Unfixed one-slab Boltzmann factor before temporal gauge fixing. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabKernel
    (H N : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (U : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  Real.exp (-beta * periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabAction H N A U B)

/-- Exact one-slab Boltzmann reduction to the existing temporal-gauge kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabKernel_eq_temporalGauge
    (H N : ℕ)
    (beta : ℝ)
    (γ U : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabKernel H N beta A U B =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N (γ * U) B) := by
  unfold periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabKernel
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  rw [periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabAction_eq_temporalGauge]

/-- Spatial path obtained after the cumulative temporal gauge transformation. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath
    (H N : ℕ)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N :=
  fun j =>
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge H N U j)
      (path j)

/-- The primary endpoint is unchanged by the chosen temporal gauge. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath_zero
    (H N : ℕ)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath
        H N U path ⟨0, Nat.zero_lt_succ _⟩ =
      path ⟨0, Nat.zero_lt_succ _⟩ := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge_zero]
  exact periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform_one H N
    (path ⟨0, Nat.zero_lt_succ _⟩)

/-- Residual gauge field accumulated at the antipodal fixed slice. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTerminalGauge
    (H N : ℕ)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N :=
  periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge
    H N U (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))

/-- The antipodal endpoint is transformed by the residual accumulated gauge
field; it is not generally pointwise fixed by temporal gauge fixing. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath_last
    (H N : ℕ)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath
        H N U path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTerminalGauge H N U)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) := by
  rfl

/-- Complete unfixed Wilson action across all positive-half-cylinder slabs. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction
    (H N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) : ℝ :=
  ∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
    periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabAction H N
      (path i.castSucc) (U i) (path i.succ)

/-- The full unfixed positive-half-cylinder action is exactly the existing
temporal-gauge path action evaluated on the cumulatively transformed spatial
path. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction_eq_temporalGauge
    (H N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction H N path U =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath
          H N U path) := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
  apply Finset.sum_congr rfl
  intro i _hi
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath
  rw [periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabAction_eq_temporalGauge
    (γ := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge
      H N U i.castSucc)]
  rw [← periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge_succ
    H N U i]

/-- Complete unfixed Boltzmann path integrand before temporal gauge fixing. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
    (H N : ℕ)
    (beta : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) : ℝ :=
  ∏ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
    periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabKernel H N beta
      (path i.castSucc) (U i) (path i.succ)

/-- Exact pathwise temporal-gauge reduction of the full positive-half-cylinder
Boltzmann integrand.  All time-like links are removed, while their accumulated
residual action survives only through the transformed spatial path and its
antipodal endpoint. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_eq_temporalGauge
    (H N : ℕ)
    (beta : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
        H N beta path U =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath
          H N U path) := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
  apply Finset.prod_congr rfl
  intro i _hi
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath
  rw [periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabKernel_eq_temporalGauge
    (γ := periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge
      H N U i.castSucc)]
  rw [← periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderCumulativeGauge_succ
    H N U i]

end

end MathlibAnalytic
end MGAP4D