import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferRieszContourBetaStability
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

/-!
# Fixed-contour Riesz projector continuity in the Wilson coupling

At a fixed nonnegative coupling beta₀, the preceding theorem unit gives a
canonical circle around the isolated normalized top spectral point 1 that
remains in the resolvent set for all sufficiently nearby beta.

This file upgrades that contour persistence to operator-norm continuity of the
normalized Riesz projector built on the *fixed beta₀ circle*.  The proof does
not assume continuity of the excited-sector gap.

The route is:

1. use contour persistence to obtain one beta-neighborhood on which every
   point of the fixed circle stays in the resolvent set;
2. prove joint continuity of the resolvent in (beta,z) on that neighborhood
   times the fixed circle, directly through continuity of inversion on units;
3. use Heine-Cantor on the compact circle to obtain uniform convergence in z
   as beta -> beta₀;
4. push that uniform estimate through the pinned Mathlib circle-integral norm
   estimate;
5. identify the base fixed-contour projector with the already established CFC
   top spectral projection.

Thus the output is a continuous local Riesz continuation anchored at the
canonical CFC top projector at beta₀.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Set Filter Topology Metric
open scoped InnerProductSpace Ring Topology

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

local instance rieszProjectorBetaContinuitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance rieszProjectorBetaContinuitySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance rieszProjectorBetaContinuitySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance rieszProjectorBetaContinuitySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance rieszProjectorBetaContinuitySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance rieszProjectorBetaContinuitySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance rieszProjectorBetaContinuityRealCompleteSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance rieszProjectorBetaContinuityComplexCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- The normalized Riesz projector using the canonical circle chosen at beta₀,
while the transfer operator itself is evaluated at beta. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
    (H N : ℕ)
    (hN : 0 < N)
    (beta0 beta : Set.Ici (0 : ℝ)) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N :=
  let r :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
      H N hN beta0.1 beta0.2
  (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    (∮ z in C((1 : ℂ), r),
      resolvent
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
          H N hN beta) z)

/-- On a beta-neighborhood supplied by contour persistence, the resolvent is
jointly continuous in beta and z along the fixed beta₀ canonical circle. -/
private theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_resolvent_joint_continuousOn_fixedCanonicalCircle
    (H N : ℕ)
    (hN : 0 < N)
    (beta0 : Set.Ici (0 : ℝ)) :
    let r :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
        H N hN beta0.1 beta0.2
    ∃ U ∈ 𝓝 beta0,
      ContinuousOn
        (fun p : Set.Ici (0 : ℝ) × ℂ =>
          resolvent
            (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
              H N hN p.1) p.2)
        (U ×ˢ Metric.sphere (1 : ℂ) r) := by
  dsimp
  let E := PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N
  let A := E →L[ℂ] E
  let S :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
      H N hN
  let r :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
      H N hN beta0.1 beta0.2
  let U : Set (Set.Ici (0 : ℝ)) :=
    {beta |
      Metric.sphere (1 : ℂ) r ⊆
        resolventSet ℂ (S beta)}
  have hU : U ∈ 𝓝 beta0 := by
    simpa [U, S, r] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_canonicalRieszCircle_eventually_subset_resolventSet
        H N hN beta0
  refine ⟨U, hU, ?_⟩
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
  intro p hp
  have hpRes : p.2 ∈ resolventSet ℂ (S p.1) :=
    hp.1 hp.2
  have hpUnit : IsUnit (shift p) := by
    simpa [shift] using (spectrum.mem_resolventSet_iff.mp hpRes)
  rcases hpUnit with ⟨u, hu⟩
  have hub : (↑u : A) = shift p := by
    simpa using hu
  have hshiftAt : Tendsto shift (𝓝 p) (𝓝 (↑u : A)) := by
    rw [hub]
    exact hshift.continuousAt
  have hinvAt :=
    @NormedRing.inverse_continuousAt A _ _ u
  have hinv :=
    hinvAt.tendsto.comp hshiftAt
  have hcontAt :
      ContinuousAt
        (fun q : Set.Ici (0 : ℝ) × ℂ => resolvent (S q.1) q.2)
        p := by
    change Tendsto
      (fun q : Set.Ici (0 : ℝ) × ℂ => resolvent (S q.1) q.2)
      (𝓝 p)
      (𝓝 (resolvent (S p.1) p.2))
    simpa [resolvent, shift, Function.comp_def, hub] using hinv
  exact hcontAt.continuousWithinAt

/-- The fixed beta₀ canonical Riesz projector is operator-norm continuous at
beta₀.  No beta-continuity of the excited-sector gap is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_continuousAt
    (H N : ℕ)
    (hN : 0 < N)
    (beta0 : Set.Ici (0 : ℝ)) :
    ContinuousAt
      (fun beta : Set.Ici (0 : ℝ) =>
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
          H N hN beta0 beta)
      beta0 := by
  let E := PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N
  let A := E →L[ℂ] E
  let S :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
      H N hN
  let r :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
      H N hN beta0.1 beta0.2
  have hr : 0 < r := by
    simpa [r] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius_pos
        H N hN beta0.1 beta0.2
  obtain ⟨U, hU, hJoint⟩ :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_resolvent_joint_continuousOn_fixedCanonicalCircle
      H N hN beta0
  have hbeta0U : beta0 ∈ U :=
    mem_of_mem_nhds hU
  have hcontEvent :
      ∀ᶠ beta in 𝓝 beta0,
        ContinuousOn
          (fun z : ℂ => resolvent (S beta) z)
          (Metric.sphere (1 : ℂ) r) := by
    simpa [S, r] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_resolvent_continuousOn_canonicalRieszCircle_eventually_beta
        H N hN beta0
  have hbaseContinuous :
      ContinuousOn
        (fun z : ℂ => resolvent (S beta0) z)
        (Metric.sphere (1 : ℂ) r) :=
    mem_of_mem_nhds hcontEvent
  have hbaseIntegrable :
      CircleIntegrable
        (fun z : ℂ => resolvent (S beta0) z)
        (1 : ℂ) r :=
    hbaseContinuous.circleIntegrable hr.le
  change Tendsto
    (fun beta : Set.Ici (0 : ℝ) =>
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
        H N hN beta0 beta)
    (𝓝 beta0)
    (𝓝
      (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
        H N hN beta0 beta0))
  rw [Uniform.tendsto_nhds_right, tendsto_def]
  intro W hW
  have hWmetric :
      W ∈ @uniformity A PseudoMetricSpace.toUniformSpace := by
    with_reducible_and_instances
      exact hW
  rcases Metric.mem_uniformity_dist.1 hWmetric with ⟨eps, heps, hWdist⟩
  let C : ℝ := eps / (2 * r)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let dEnt : Set (A × A) :=
    {p | dist p.1 p.2 < C}
  have hdEnt : dEnt ∈ uniformity A := by
    simpa [dEnt] using
      (Metric.dist_mem_uniformity hC :
        {p : A × A | dist p.1 p.2 < C} ∈ uniformity A)
  obtain ⟨v, hvWithin, hvEnt⟩ :=
    (isCompact_sphere (1 : ℂ) r).mem_uniformity_of_prod
      (f := fun beta z => resolvent (S beta) z)
      hJoint hbeta0U hdEnt
  have hv :
      ∀ beta ∈ v, ∀ z ∈ Metric.sphere (1 : ℂ) r,
        dist (resolvent (S beta) z) (resolvent (S beta0) z) < C := by
    intro beta hbeta z hz
    simpa [dEnt] using hvEnt beta hbeta z hz
  have hvNhds : v ∈ 𝓝 beta0 :=
    nhds_of_nhdsWithin_of_nhds hU hvWithin
  filter_upwards [hvNhds, hcontEvent] with beta hbetaV hbetaContinuous
  have hbetaIntegrable :
      CircleIntegrable
        (fun z : ℂ => resolvent (S beta) z)
        (1 : ℂ) r :=
    hbetaContinuous.circleIntegrable hr.le
  have hpoint :
      ∀ z ∈ Metric.sphere (1 : ℂ) r,
        ‖resolvent (S beta) z - resolvent (S beta0) z‖ ≤ C := by
    intro z hz
    have hzClose := hv beta hbetaV z hz
    simpa [dist_eq_norm] using hzClose.le
  have hbound :
      ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (∮ z in C((1 : ℂ), r),
            (resolvent (S beta) z - resolvent (S beta0) z))‖ ≤
        r * C :=
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      hr.le hpoint
  have hdiff :
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
          H N hN beta0 beta -
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
          H N hN beta0 beta0 =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        (∮ z in C((1 : ℂ), r),
          (resolvent (S beta) z - resolvent (S beta0) z)) := by
    change
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (∮ z in C((1 : ℂ), r), resolvent (S beta) z) -
        (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (∮ z in C((1 : ℂ), r), resolvent (S beta0) z) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (∮ z in C((1 : ℂ), r),
            (resolvent (S beta) z - resolvent (S beta0) z))
    calc
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
            (∮ z in C((1 : ℂ), r), resolvent (S beta) z) -
          (2 * Real.pi * Complex.I : ℂ)⁻¹ •
            (∮ z in C((1 : ℂ), r), resolvent (S beta0) z) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ((∮ z in C((1 : ℂ), r), resolvent (S beta) z) -
            (∮ z in C((1 : ℂ), r), resolvent (S beta0) z)) := by
              exact (smul_sub _ _ _).symm
      _ =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (∮ z in C((1 : ℂ), r),
            (resolvent (S beta) z - resolvent (S beta0) z)) := by
              rw [circleIntegral.integral_sub hbetaIntegrable hbaseIntegrable]
  apply hWdist
  rw [dist_comm, dist_eq_norm, hdiff]
  calc
    ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ •
        (∮ z in C((1 : ℂ), r),
          (resolvent (S beta) z - resolvent (S beta0) z))‖
        ≤ r * C := hbound
    _ = eps / 2 := by
      dsimp [C]
      field_simp [hr.ne']
      <;> ring
    _ < eps := by linarith

/-- At the base coupling, the fixed canonical Riesz projector is exactly the
already established CFC top spectral projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_at_base_eq_cfcTopProjection
    (H N : ℕ)
    (hN : 0 < N)
    (beta0 : Set.Ici (0 : ℝ)) :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
        H N hN beta0 beta0 =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta0.1 beta0.2 := by
  simpa only [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector,
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine_apply] using
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjector_eq_cfcTopProjection
      H N hN beta0.1 beta0.2

/-- The fixed-contour Riesz continuation tends to the canonical CFC top
projection at beta₀. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_tendsto_cfcTopProjection
    (H N : ℕ)
    (hN : 0 < N)
    (beta0 : Set.Ici (0 : ℝ)) :
    Tendsto
      (fun beta : Set.Ici (0 : ℝ) =>
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
          H N hN beta0 beta)
      (𝓝 beta0)
      (𝓝
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta0.1 beta0.2)) := by
  rw [←
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_at_base_eq_cfcTopProjection
      H N hN beta0]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_continuousAt
      H N hN beta0

end

end MathlibAnalytic
end MGAP4D
