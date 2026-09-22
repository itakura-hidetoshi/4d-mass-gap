import MGAP4D.MathlibAnalytic.ContinuousLinearMapIdempotentRankPersistence
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferFixedContourTopAbsorption
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferTopRayUniqueness

/-!
# Nearby fixed-contour and canonical top-projector identification

The fixed-contour Riesz continuation is norm-close to the rank-one canonical
projection at the base coupling. Its idempotence therefore gives a genuinely
finite-dimensional range of dimension at most one. Bilateral absorption of the
nearby canonical rank-one projection then identifies the ranges and operators.

The final theorem proves operator-norm continuity of the actual moving CFC top
projection on the nonnegative coupling half-line. No continuity of the excited
spectral gap or of a chosen vacuum vector is assumed. All neighborhoods are
finite-volume neighborhoods; no volume-uniform or continuum assertion is made.
-/

namespace MGAP4D.MathlibAnalytic

open Set Filter Topology Metric
open scoped InnerProductSpace Ring Topology

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

/-- Norm-close idempotent rank persistence gives actual finite-dimensionality,
not merely a numerical bound on `finrank` (which alone would not suffice). -/
theorem continuousLinearMap_finiteDimensional_range_of_idempotent_norm_sub_lt_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q P : E →L[ℂ] E)
    (hQidem : Q * Q = Q) (hclose : ‖Q - P‖ < 1)
    [FiniteDimensional ℂ P.range] :
    FiniteDimensional ℂ Q.range := by
  let f : Q.range →ₗ[ℂ] P.range :=
    { toFun := fun x => ⟨P x.1, ⟨x.1, rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact P.map_add x.1 y.1
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact P.map_smul c x.1 }
  have hf : Function.Injective f := by
    change Function.Injective
      (fun x : Q.range => (⟨P x.1, ⟨x.1, rfl⟩⟩ : P.range))
    exact
      continuousLinearMap_rangeRestriction_injective_of_idempotent_norm_sub_lt_one
        Q P hQidem hclose
  exact FiniteDimensional.of_injective f hf

/-- Finite-dimensional range comparison and bilateral absorption identify an
operator with an idempotent. Equal ranges alone would not identify projections
with different kernels; the second absorption identity supplies this step. -/
theorem continuousLinearMap_eq_of_finiteDimensional_range_absorption
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q P : E →L[ℂ] E)
    (hPidem : P * P = P)
    (hQP : Q * P = P) (hPQ : P * Q = P)
    [FiniteDimensional ℂ Q.range]
    (hdim : Module.finrank ℂ Q.range ≤ Module.finrank ℂ P.range) :
    Q = P := by
  have hle : P.range ≤ Q.range := by
    intro x hx
    rcases hx with ⟨u, hu⟩
    -- Normalize the LinearMap range witness before applying the CLM.
    have huP : P u = x := hu
    refine ⟨P u, ?_⟩
    change Q (P u) = x
    have happ := congrArg (fun T : E →L[ℂ] E => T u) hQP
    change Q (P u) = P u at happ
    exact happ.trans huP
  have hrange : P.range = Q.range :=
    Submodule.eq_of_le_of_finrank_le hle hdim
  apply ContinuousLinearMap.ext
  intro x
  have hmem : Q x ∈ P.range := by
    rw [hrange]
    exact ⟨x, rfl⟩
  rcases hmem with ⟨u, hu⟩
  have huP : P u = Q x := hu
  have hPfix : P (Q x) = Q x := by
    have happ := congrArg (fun T : E →L[ℂ] E => T u) hPidem
    change P (P u) = P u at happ
    exact
      (congrArg (fun v : E => P v) huP.symm).trans (happ.trans huP)
  have hPQx := congrArg (fun T : E →L[ℂ] E => T x) hPQ
  change P (Q x) = P x at hPQx
  exact hPfix.symm.trans hPQx

/-- An operator-valued limit supplies the strict norm threshold used in the
rank-persistence argument. Instance unfolding stays local to metric transport. -/
private theorem eventually_opNorm_sub_lt_one_of_tendsto
    {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {l : Filter α} (Q : α → E →L[ℂ] E) (P : E →L[ℂ] E)
    (hQ : Tendsto Q l (𝓝 P)) :
    ∀ᶠ a in l, ‖Q a - P‖ < 1 := by
  have hdist : ∀ᶠ a in l, dist (Q a) P < (1 : ℝ) := by
    with_reducible_and_instances
      exact (Metric.tendsto_nhds.1 hQ) 1 zero_lt_one
  filter_upwards [hdist] with a ha
  have heq : dist (Q a) P = ‖Q a - P‖ := by
    with_reducible_and_instances
      exact dist_eq_norm _ _
  exact heq ▸ ha

local instance projectorIdentificationSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance projectorIdentificationSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance projectorIdentificationSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance projectorIdentificationSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance projectorIdentificationSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance projectorIdentificationSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance projectorIdentificationRealCompleteSpace (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance projectorIdentificationComplexCompleteSpace (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- The literal canonical CFC top projection has complex range dimension one.
Nonvanishing follows from the norm-one canonical nonnegative top vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_finrank_range
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Module.finrank ℂ
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta).range = 1 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_range_eq_span_nonnegativeTop
  ]
  apply finrank_span_singleton
  intro hzero
  have hnorm :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta)‖ = 1 := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOfReal_norm,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm]
  rw [hzero, norm_zero] at hnorm
  exact zero_ne_one hnorm

/-- Near the base coupling, the fixed-contour Riesz range is finite-dimensional
and has complex dimension at most one. These two conclusions are kept together
so that the dimension bound cannot be misused on an infinite-dimensional range. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_eventually_finiteDimensional_finrank_le_one
    (H N : ℕ) (hN : 0 < N) (beta0 : Set.Ici (0 : ℝ)) :
    ∀ᶠ beta in 𝓝 beta0,
      FiniteDimensional ℂ
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
          H N hN beta0 beta).range ∧
      Module.finrank ℂ
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
          H N hN beta0 beta).range ≤ 1 := by
  let E := PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N
  let Q : Set.Ici (0 : ℝ) → E →L[ℂ] E :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
      H N hN beta0
  let P0 : E →L[ℂ] E :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
      H N hN beta0.1 beta0.2
  have hP0dim : Module.finrank ℂ P0.range = 1 :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_finrank_range
      H N hN beta0.1 beta0.2
  letI : FiniteDimensional ℂ P0.range :=
    FiniteDimensional.of_finrank_eq_succ hP0dim
  have hQlimit : Tendsto Q (𝓝 beta0) (𝓝 P0) :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_tendsto_cfcTopProjection
      H N hN beta0
  have hclose : ∀ᶠ beta in 𝓝 beta0, ‖Q beta - P0‖ < 1 :=
    eventually_opNorm_sub_lt_one_of_tendsto Q P0 hQlimit
  have hidem :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_eventually_mul_self
      H N hN beta0
  filter_upwards [hclose, hidem] with beta hc hi
  change FiniteDimensional ℂ (Q beta).range ∧
    Module.finrank ℂ (Q beta).range ≤ 1
  refine ⟨continuousLinearMap_finiteDimensional_range_of_idempotent_norm_sub_lt_one
    (Q beta) P0 hi hc, ?_⟩
  exact
    (continuousLinearMap_finrank_range_le_of_idempotent_norm_sub_lt_one
      (Q beta) P0 hi hc).trans hP0dim.le

/-- The actual nearby canonical CFC top projection is exactly the Riesz
continuation on the fixed base contour. This is an equality of operators,
not just an identification of their ranges. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_eventually_eq_cfcTopProjection
    (H N : ℕ) (hN : 0 < N) (beta0 : Set.Ici (0 : ℝ)) :
    ∀ᶠ beta in 𝓝 beta0,
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
          H N hN beta0 beta =
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta.1 beta.2 := by
  have hfinite :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_eventually_finiteDimensional_finrank_le_one
      H N hN beta0
  have habsorb :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_eventually_absorbs_cfcTopProjection
      H N hN beta0
  filter_upwards [hfinite, habsorb] with beta hf ha
  let E := PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N
  let Q : E →L[ℂ] E :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
      H N hN beta0 beta
  let P : E →L[ℂ] E :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
      H N hN beta.1 beta.2
  letI : FiniteDimensional ℂ Q.range := hf.1
  have hPdim : Module.finrank ℂ P.range = 1 :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_finrank_range
      H N hN beta.1 beta.2
  have hPidem : P * P = P :=
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_isStarProjection
      H N hN beta.1 beta.2).isIdempotentElem
  exact continuousLinearMap_eq_of_finiteDimensional_range_absorption
    Q P hPidem ha.1 ha.2 (hf.2.trans hPdim.ge)

/-- Consequently the fixed-contour continuation has exact rank one locally. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_eventually_finrank_eq_one
    (H N : ℕ) (hN : 0 < N) (beta0 : Set.Ici (0 : ℝ)) :
    ∀ᶠ beta in 𝓝 beta0,
      Module.finrank ℂ
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
          H N hN beta0 beta).range = 1 := by
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_eventually_eq_cfcTopProjection
      H N hN beta0
  ] with beta heq
  rw [heq]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_finrank_range
      H N hN beta.1 beta.2

/-- Operator-norm continuity of the actual moving canonical CFC top projection
on the nonnegative coupling half-line, including the endpoint beta = 0. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_halfLine_continuous
    (H N : ℕ) (hN : 0 < N) :
    Continuous
      (fun beta : Set.Ici (0 : ℝ) =>
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta.1 beta.2) := by
  apply continuous_iff_continuousAt.mpr
  intro beta0
  have hQ :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_tendsto_cfcTopProjection
      H N hN beta0
  have heq :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_eventually_eq_cfcTopProjection
      H N hN beta0
  change Tendsto
    (fun beta : Set.Ici (0 : ℝ) =>
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta.1 beta.2)
    (𝓝 beta0)
    (𝓝
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta0.1 beta0.2))
  exact (Filter.tendsto_congr' heq).mp hQ

end
end MGAP4D.MathlibAnalytic
