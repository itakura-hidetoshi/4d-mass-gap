import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNormalizedOneSlabBetaContinuity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalCenteredTransferConvergence
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Complex normalized one-slab transfer: beta continuity and local resolvent stability

The real normalized physical transfer is continuous in operator norm on the
nonnegative Wilson-coupling half-line.  The existing Riesz/CFC top-sector
machinery lives on the genuine complex physical Hilbert space, so the next
step is to transport that continuity through the canonical scalar extension.

The scalar-extension map is an isometry in operator norm.  Hence the genuine
complex normalized one-slab transfer is continuous in beta.  At every fixed
complex spectral parameter belonging to the resolvent set at a base coupling,
openness of the invertible bounded operators then gives local stability of the
resolvent set and continuity of the actual resolvent in beta.

This is the pointwise-in-contour input for the next compact-circle argument.
No continuity of the excited-sector gap is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Set Filter Topology
open scoped InnerProductSpace Ring Topology

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

local instance complexNormalizedBetaContinuitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance complexNormalizedBetaContinuitySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance complexNormalizedBetaContinuitySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance complexNormalizedBetaContinuitySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance complexNormalizedBetaContinuitySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance complexNormalizedBetaContinuitySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance complexNormalizedBetaContinuityRealCompleteSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance complexNormalizedBetaContinuityComplexCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- Canonical scalar extension from real physical bounded operators to genuine
complex physical bounded operators is an operator-norm isometry, hence
1-Lipschitz. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_lipschitz
    (H N : ℕ) :
    LipschitzWith 1
      (fun T :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N T) := by
  apply LipschitzWith.mk_one
  intro T U
  simp only [dist_eq_norm]
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_sub]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_norm]

/-- The genuine complex normalized physical transfer as a family over the fixed
nonnegative Wilson-coupling half-line. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
    (H N : ℕ)
    (hN : 0 < N) :
    Set.Ici (0 : ℝ) →
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N :=
  fun beta =>
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
      H N hN beta.1 beta.2

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : Set.Ici (0 : ℝ)) :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
        H N hN beta =
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta.1 beta.2 := rfl

/-- Every member of the complex normalized half-line family has operator norm
exactly one. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : Set.Ici (0 : ℝ)) :
    ‖periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
      H N hN beta‖ = 1 := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine] using
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_norm
      H N hN beta.1 beta.2

/-- The genuine complex normalized physical transfer is continuous in operator
norm on the entire nonnegative coupling half-line. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine_continuous
    (H N : ℕ)
    (hN : 0 < N) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
        H N hN) := by
  let C :=
    fun T :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N T
  let T :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine
      H N hN
  have hC : Continuous C := by
    simpa [C] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_lipschitz
        H N).continuous
  have hT : Continuous T := by
    simpa [T] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperatorHalfLine_continuous
        H N hN
  have hcomp : Continuous (C ∘ T) := hC.comp hT
  simpa [
    C, T, Function.comp_def,
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine,
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator] using hcomp

/-- A fixed complex resolvent point at a base coupling remains in the resolvent
set for all sufficiently nearby nonnegative couplings. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_resolventSet_eventually_beta
    (H N : ℕ)
    (hN : 0 < N)
    (beta0 : Set.Ici (0 : ℝ))
    (z : ℂ)
    (hz :
      z ∈ resolventSet ℂ
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
          H N hN beta0)) :
    ∀ᶠ beta in 𝓝 beta0,
      z ∈ resolventSet ℂ
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
          H N hN beta) := by
  let E := PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N
  let A := E →L[ℂ] E
  let S :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
      H N hN
  let shift : Set.Ici (0 : ℝ) → A :=
    fun beta => algebraMap ℂ A z - S beta
  have hS : Continuous S := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine_continuous
        H N hN
  have hshift : Continuous shift := by
    simpa [shift] using
      (continuous_const.sub hS)
  have hzUnit : IsUnit (shift beta0) := by
    simpa [shift, S] using hz
  have hopen : {x : A | IsUnit x} ∈ 𝓝 (shift beta0) :=
    Units.isOpen.mem_nhds hzUnit
  have hnear :
      ∀ᶠ beta in 𝓝 beta0, IsUnit (shift beta) :=
    hshift.continuousAt.eventually_mem hopen
  filter_upwards [hnear] with beta hbeta
  simpa [shift, S] using hbeta

/-- At every fixed spectral parameter in the base resolvent set, the genuine
complex normalized Wilson resolvent is operator-norm continuous in beta. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_resolvent_continuousAt_beta
    (H N : ℕ)
    (hN : 0 < N)
    (beta0 : Set.Ici (0 : ℝ))
    (z : ℂ)
    (hz :
      z ∈ resolventSet ℂ
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
          H N hN beta0)) :
    ContinuousAt
      (fun beta : Set.Ici (0 : ℝ) =>
        resolvent
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
            H N hN beta) z)
      beta0 := by
  let E := PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N
  let A := E →L[ℂ] E
  let S :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
      H N hN
  let shift : Set.Ici (0 : ℝ) → A :=
    fun beta => algebraMap ℂ A z - S beta
  have hS : Continuous S := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine_continuous
        H N hN
  have hshift : Continuous shift := by
    simpa [shift] using
      (continuous_const.sub hS)
  have hzUnit : IsUnit (shift beta0) := by
    simpa [shift, S] using hz
  rcases hzUnit with ⟨u, hu⟩
  have hub : (↑u : A) = shift beta0 := by
    simpa using hu
  have hshiftAt :
      Tendsto shift (𝓝 beta0) (𝓝 (↑u : A)) := by
    rw [hub]
    exact hshift.continuousAt
  have hinvAt :
      ContinuousAt (fun x : A => Ring.inverse x) (↑u : A) :=
    NormedRing.inverse_continuousAt u
  have hinv :=
    hinvAt.tendsto.comp hshiftAt
  change Tendsto
    (fun beta : Set.Ici (0 : ℝ) =>
      resolvent (S beta) z)
    (𝓝 beta0)
    (𝓝 (resolvent (S beta0) z))
  simpa [resolvent, shift, Function.comp_def, hub] using hinv

end

end MathlibAnalytic
end MGAP4D
