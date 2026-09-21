import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferNormalizedBetaResolventContinuity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCRieszProjector
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic

/-!
# Canonical Riesz contour stability under Wilson-coupling perturbation

At a fixed nonnegative coupling beta₀, the normalized complex physical transfer
has the isolated top spectral point 1 and the canonical Riesz circle centered at
1.  The preceding theorem unit established operator-norm continuity of the
normalized complex transfer and pointwise beta-continuity of the resolvent.

This file upgrades that pointwise statement to a contour-wide one.  The key
topological step is deliberately generic: for a continuous map into a complete
normed ring, the preimage of the units is open, proved directly with
`Units.ofNearby`.  This avoids the instance ambiguity of the generic
`Units.isOpen` theorem for continuous-linear-map endomorphism rings under the
pinned Lean 4.30.0-rc2 toolchain.

Applied to the joint shift
  (beta,z) ↦ z - S_beta,
the unit locus is open.  Compactness of the canonical Riesz sphere and the
generalized tube lemma then produce one beta-neighborhood on which the entire
fixed contour remains in the resolvent set.

This is the uniform spectral-persistence input needed for beta-continuity of
the Riesz projector itself.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Set Filter Topology Metric
open scoped InnerProductSpace Ring Topology

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

local instance rieszContourBetaStabilitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance rieszContourBetaStabilitySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance rieszContourBetaStabilitySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance rieszContourBetaStabilitySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance rieszContourBetaStabilitySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance rieszContourBetaStabilitySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance rieszContourBetaStabilityRealCompleteSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance rieszContourBetaStabilityComplexCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- A continuous map into a complete normed ring has an open unit locus.

This direct `Units.ofNearby` proof is useful when the target carries a
specialized multiplication instance whose definitional equality with the
generic normed-ring instance is too opaque for `Units.isOpen`. -/
private theorem isOpen_isUnit_preimage_of_continuous
    {X A : Type*}
    [TopologicalSpace X]
    [NormedRing A]
    [HasSummableGeomSeries A]
    (f : X → A)
    (hf : Continuous f) :
    IsOpen {x : X | IsUnit (f x)} := by
  nontriviality A
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hx with ⟨u, hu⟩
  have hpos : 0 < ‖(↑u⁻¹ : A)‖⁻¹ :=
    inv_pos.mpr (Units.norm_pos u⁻¹)
  have hnear :
      ∀ᶠ y in 𝓝 x, dist (f y) (f x) < ‖(↑u⁻¹ : A)‖⁻¹ :=
    (Metric.tendsto_nhds.1 hf.continuousAt) _ hpos
  filter_upwards [hnear] with y hy
  have hnorm : ‖f y - (↑u : A)‖ < ‖(↑u⁻¹ : A)‖⁻¹ := by
    rw [← hu] at hy
    simpa [dist_eq_norm] using hy
  exact (u.ofNearby (f y) hnorm).isUnit

private theorem complex_re_gt_of_mem_closedBall_one_half_gap_beta
    {q : ℝ} (hq : q < 1) {z : ℂ}
    (hz : z ∈ Metric.closedBall (1 : ℂ) ((1 - q) / 2)) :
    q < z.re := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have hre : |z.re - 1| ≤ ‖z - (1 : ℂ)‖ := by
    simpa using Complex.abs_re_le_norm (z - (1 : ℂ))
  have hlow : -(z.re - 1) ≤ (1 - q) / 2 := by
    calc
      -(z.re - 1) ≤ |-(z.re - 1)| := le_abs_self _
      _ = |z.re - 1| := abs_neg _
      _ ≤ ‖z - (1 : ℂ)‖ := hre
      _ ≤ (1 - q) / 2 := hz
  linarith

/-- The canonical Riesz circle chosen at beta₀ remains entirely in the
resolvent set for every sufficiently nearby nonnegative coupling beta.

The circle itself is fixed at its beta₀ radius; only the transfer operator
moves. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_canonicalRieszCircle_eventually_subset_resolventSet
    (H N : ℕ)
    (hN : 0 < N)
    (beta0 : Set.Ici (0 : ℝ)) :
    let r :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
        H N hN beta0.1 beta0.2
    ∀ᶠ beta in 𝓝 beta0,
      Metric.sphere (1 : ℂ) r ⊆
        resolventSet ℂ
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
            H N hN beta) := by
  dsimp
  let E := PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N
  let A := E →L[ℂ] E
  let S :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
      H N hN
  let q :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta0.1 beta0.2‖
  let r :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
      H N hN beta0.1 beta0.2
  let shift : Set.Ici (0 : ℝ) × ℂ → A :=
    fun p => algebraMap ℂ A p.2 - S p.1
  have hS : Continuous S := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine_continuous
        H N hN
  have halg : Continuous (fun z : ℂ => algebraMap ℂ A z) := by
    fun_prop
  have hshift : Continuous shift := by
    simpa [shift] using
      (halg.comp continuous_snd).sub (hS.comp continuous_fst)
  have hopen :
      IsOpen {p : Set.Ici (0 : ℝ) × ℂ | IsUnit (shift p)} :=
    isOpen_isUnit_preimage_of_continuous shift hshift
  have hq : q < 1 := by
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta0.1 beta0.2
  have hr : 0 < r := by
    simpa [r] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius_pos
        H N hN beta0.1 beta0.2
  have hrDef : r = (1 - q) / 2 := by
    simp [r, q,
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius]
  have hbase :
      ({beta0} : Set (Set.Ici (0 : ℝ))) ×ˢ Metric.sphere (1 : ℂ) r ⊆
        {p : Set.Ici (0 : ℝ) × ℂ | IsUnit (shift p)} := by
    rintro ⟨beta, z⟩ ⟨hbeta, hzSphere⟩
    have hbetaEq : beta = beta0 := by
      simpa using hbeta
    subst beta
    have hzClosed : z ∈ Metric.closedBall (1 : ℂ) r := by
      rw [Metric.mem_sphere] at hzSphere
      rw [Metric.mem_closedBall]
      exact hzSphere.le
    have hzq : q < z.re := by
      apply complex_re_gt_of_mem_closedBall_one_half_gap_beta hq
      simpa [hrDef] using hzClosed
    have hzNe : z ≠ (1 : ℂ) := by
      intro hzOne
      subst z
      rw [Metric.mem_sphere] at hzSphere
      have hzero : (0 : ℝ) = r := by
        simpa using hzSphere
      exact hr.ne' hzero.symm
    have hres :
        z ∈ resolventSet ℂ
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta0.1 beta0.2) :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rightHalfPlane_except_one_subset_complex_resolventSet
        H N hN beta0.1 beta0.2 ⟨by simpa [q] using hzq, hzNe⟩
    have hunit := spectrum.mem_resolventSet_iff.mp hres
    simpa [
      shift, S,
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine] using
      hunit
  obtain ⟨u, v, huOpen, hvOpen, hbetaU, hSphereV, huv⟩ :=
    generalized_tube_lemma
      (s := ({beta0} : Set (Set.Ici (0 : ℝ))))
      (t := Metric.sphere (1 : ℂ) r)
      isCompact_singleton (isCompact_sphere (1 : ℂ) r) hopen hbase
  have hbeta0U : beta0 ∈ u := hbetaU (by simp)
  have huNhds : u ∈ 𝓝 beta0 := huOpen.mem_nhds hbeta0U
  filter_upwards [huNhds] with beta hbeta
  intro z hz
  have hp :
      (beta, z) ∈
        {p : Set.Ici (0 : ℝ) × ℂ | IsUnit (shift p)} :=
    huv ⟨hbeta, hSphereV hz⟩
  have hunit : IsUnit (shift (beta, z)) := hp
  have hunit' :
      IsUnit
        (algebraMap ℂ A z -
          periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
            H N hN beta) := by
    simpa [shift, S] using hunit
  exact spectrum.mem_resolventSet_iff.mpr hunit'

/-- On the same fixed beta₀ canonical circle, the nearby resolvent is
continuous in the spectral parameter for all sufficiently nearby beta. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_resolvent_continuousOn_canonicalRieszCircle_eventually_beta
    (H N : ℕ)
    (hN : 0 < N)
    (beta0 : Set.Ici (0 : ℝ)) :
    let r :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
        H N hN beta0.1 beta0.2
    ∀ᶠ beta in 𝓝 beta0,
      ContinuousOn
        (fun z : ℂ =>
          resolvent
            (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
              H N hN beta) z)
        (Metric.sphere (1 : ℂ) r) := by
  dsimp
  have hres :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_canonicalRieszCircle_eventually_subset_resolventSet
      H N hN beta0
  filter_upwards [hres] with beta hbeta
  intro z hz
  have hzRes :
      z ∈ resolventSet ℂ
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
          H N hN beta) :=
    Set.mem_of_subset_of_mem hbeta hz
  have hderiv :
      HasDerivAt
        (resolvent
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
            H N hN beta))
        (-
          resolvent
              (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
                H N hN beta) z ^
            2)
        z := by
    with_reducible_and_instances
      exact
        spectrum.hasDerivAt_resolvent_const_left
          (a :=
            periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
              H N hN beta)
          (k := z) hzRes
  have hdiff :
      DifferentiableAt ℂ
        (resolvent
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
            H N hN beta))
        z :=
    hderiv.differentiableAt
  exact hdiff.continuousAt.continuousWithinAt

end

end MathlibAnalytic
end MGAP4D
