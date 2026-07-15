import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridSourceOverlapTransportEnergyBCF
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryExplicitDobrushin
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Every fixed-background overlap transport energy has the direct universal
square bound. -/
theorem continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportEnergyBCF_le_two_norm_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkConditionalOverlapObservableTransportEnergyBCF
        A B background target O ≤ (2 * ‖O‖) ^ 2 := by
  let μ := C.singleLinkConditionalOverlapCouplingMeasure A B target
  let f := C.singleLinkConditionalOverlapObservableTransportBCF
    background target O
  let c : ℝ := (2 * ‖O‖) ^ 2
  letI : IsProbabilityMeasure μ :=
    continuousCompactOriented_singleLinkConditionalOverlapCouplingMeasure_isProbability
      C A B target
  have hfInt : Integrable (fun z => (f z) ^ 2) μ := by
    simpa [μ, f] using
      continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportBCF_sq_integrable
        C A B background target O
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportEnergyBCF
  change (∫ z, (f z) ^ 2 ∂μ) ≤ c
  calc
    (∫ z, (f z) ^ 2 ∂μ) ≤ ∫ _z, c ∂μ := by
      apply integral_mono hfInt (integrable_const c)
      intro z
      have hAbs :=
        continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportBCF_abs_le
          C background target O z
      dsimp [c]
      have hBounds := abs_le.mp hAbs
      nlinarith [norm_nonneg O]
    _ = c := by simp

/-- Pull the integrated source-step overlap transport energy back to the
original independent Gibbs-pair carrier. -/
theorem continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_eq_integral_endpointMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridSourceOverlapTransportEnergyBCF target source O =
      ∫ z : C.base.Configuration × C.base.Configuration,
        let pair := C.independentPairHybridEndpointPairMap source z
        C.singleLinkConditionalOverlapObservableTransportEnergyBCF
          pair.1 pair.2 pair.1 target O
        ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
  let fiber := fun pair : C.base.Configuration × C.base.Configuration =>
    C.singleLinkConditionalOverlapObservableTransportEnergyBCF
      pair.1 pair.2 pair.1 target O
  have hJoint :=
    continuous_compact_oriented_independentPairHybridSourceOverlapTransportIntegrandBCF_integrable
      C target source O
  have hFiberIntegrable : Integrable fiber
      (C.independentPairHybridEndpointPairMeasure source) := by
    simpa
      [fiber,
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportMeasure,
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportIntegrandBCF,
        ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportEnergyBCF,
        continuous_compact_oriented_configurationPairConditionalOverlapCouplingKernel_apply]
      using hJoint.integral_compProd
  rw [continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_eq_integral_fiber]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMeasure
  simpa [fiber] using
    MeasureTheory.integral_map
      (continuous_compact_oriented_independentPairHybridEndpointPairMap_measurable
        C source).aemeasurable
      hFiberIntegrable.aestronglyMeasurable

/-- It is enough to control Gibbs-exponent oscillation pointwise on the actual
endpoint map, rather than on every arbitrary configuration pair. -/
theorem continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_le_compactHaarOscillationInfluence_of_endpointMap_oscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target source : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hOsc : ∀ z : C.base.Configuration × C.base.Configuration,
      ∀ u v : C.base.Gauge,
        let pair := C.independentPairHybridEndpointPairMap source z
        (C.base.gibbsExponent (C.base.replaceLink pair.1 target u) -
          C.base.gibbsExponent (C.base.replaceLink pair.2 target u)) -
        (C.base.gibbsExponent (C.base.replaceLink pair.1 target v) -
          C.base.gibbsExponent (C.base.replaceLink pair.2 target v)) ≤ R) :
    C.independentPairHybridSourceOverlapTransportEnergyBCF target source O ≤
      (2 * ‖O‖) ^ 2 * compactHaarOscillationInfluence R := by
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  let endpointMap := C.independentPairHybridEndpointPairMap source
  let fiber := fun pair : C.base.Configuration × C.base.Configuration =>
    C.singleLinkConditionalOverlapObservableTransportEnergyBCF
      pair.1 pair.2 pair.1 target O
  let c : ℝ := (2 * ‖O‖) ^ 2 * compactHaarOscillationInfluence R
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  have hJoint :=
    continuous_compact_oriented_independentPairHybridSourceOverlapTransportIntegrandBCF_integrable
      C target source O
  have hFiberIntegrable : Integrable fiber
      (C.independentPairHybridEndpointPairMeasure source) := by
    simpa
      [fiber,
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportMeasure,
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportIntegrandBCF,
        ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportEnergyBCF,
        continuous_compact_oriented_configurationPairConditionalOverlapCouplingKernel_apply]
      using hJoint.integral_compProd
  have hCompAEStrong : AEStronglyMeasurable
      (fun z => fiber (endpointMap z)) μ :=
    hFiberIntegrable.aestronglyMeasurable.comp_aemeasurable
      (continuous_compact_oriented_independentPairHybridEndpointPairMap_measurable
        C source).aemeasurable
  have hCompIntegrable : Integrable (fun z => fiber (endpointMap z)) μ := by
    apply (integrable_const ((2 * ‖O‖) ^ 2)).mono'
    · exact hCompAEStrong
    · filter_upwards [] with z
      have hNonneg :=
        continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportEnergyBCF_nonneg
          C (endpointMap z).1 (endpointMap z).2 (endpointMap z).1 target O
      have hLe :=
        continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportEnergyBCF_le_two_norm_sq
          C (endpointMap z).1 (endpointMap z).2 (endpointMap z).1 target O
      simpa [fiber, Real.norm_eq_abs, abs_of_nonneg hNonneg] using hLe
  rw [continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_eq_integral_endpointMap]
  change (∫ z, fiber (endpointMap z) ∂μ) ≤ c
  calc
    (∫ z, fiber (endpointMap z) ∂μ) ≤ ∫ _z, c ∂μ := by
      apply integral_mono hCompIntegrable (integrable_const c)
      intro z
      exact
        continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportEnergyBCF_le_compactHaarOscillationInfluence_of_oscillation
          C (endpointMap z).1 (endpointMap z).2 (endpointMap z).1 target O
            R hR (hOsc z)
    _ = c := by simp

/-- For the canonical compact-oriented `SU(N)` Wilson system, every off-diagonal
source step is bounded by the actual shared-plaquette Dobrushin entry. -/
theorem specialUnitaryContinuousCompactOriented_independentPairHybridSourceOverlapTransportEnergyBCF_le_sharedPlaquetteInfluence
    (geometry : FiniteOrientedFourDimensionalPlaquetteGeometry)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target source : geometry.Edge)
    (hNe : target ≠ source)
    (O : BoundedContinuousFunction
      (specialUnitaryContinuousCompactOrientedDensityRatioSystem
        geometry N hN beta beta_nonneg).base.Configuration ℝ) :
    let C := specialUnitaryContinuousCompactOrientedDensityRatioSystem
      geometry N hN beta beta_nonneg
    C.independentPairHybridSourceOverlapTransportEnergyBCF target source O ≤
      (2 * ‖O‖) ^ 2 *
        specialUnitaryCompactOrientedSharedPlaquetteInfluence
          geometry N hN beta beta_nonneg target source := by
  classical
  dsimp only
  let C := specialUnitaryContinuousCompactOrientedDensityRatioSystem
    geometry N hN beta beta_nonneg
  letI : T2Space C.base.Gauge := by
    dsimp [C]
    infer_instance
  let R := beta *
    (4 * ((C.base.sharedPlaquettes target source).card : ℝ))
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hBound :
      C.independentPairHybridSourceOverlapTransportEnergyBCF target source O ≤
        (2 * ‖O‖) ^ 2 * compactHaarOscillationInfluence R := by
    apply
      continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_le_compactHaarOscillationInfluence_of_endpointMap_oscillation
        C target source O R hR
    intro z u v
    let pair := C.independentPairHybridEndpointPairMap source z
    have hAgreeRev :=
      continuous_compact_oriented_independentPairHybridEndpointPairMap_agreeOffLink
        C source z
    have hAgree : C.base.AgreeOffLink pair.1 pair.2 source := by
      intro edge hEdge
      exact (hAgreeRev edge hEdge).symm
    have hAbs :=
      specialUnitaryCompactOriented_gibbsExponent_sourceResponse_oscillation_abs_le
        geometry N hN beta beta_nonneg pair.1 pair.2
          target source u v hAgree
    exact le_trans (le_abs_self _) (by simpa [C, R, pair] using hAbs)
  simpa [C, R,
    specialUnitaryCompactOrientedSharedPlaquetteInfluence, hNe] using hBound

/-- Periodic compact-Haar `SU(N)` source-to-target transport is controlled by the
actual periodic Dobrushin matrix entry away from the diagonal. -/
theorem periodicHypercubicSpecialUnitary_independentPairHybridSourceOverlapTransportEnergyBCF_le_influence
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target source : PeriodicHypercubicEdge n)
    (hNe : target ≠ source)
    (O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).independentPairHybridSourceOverlapTransportEnergyBCF
        target source O ≤
      (2 * ‖O‖) ^ 2 *
        specialUnitaryCompactOrientedSharedPlaquetteInfluence
          (periodicHypercubicFiniteOrientedGeometry n)
          N hN beta beta_nonneg target source := by
  simpa [periodicHypercubicSpecialUnitaryWilsonSystem] using
    specialUnitaryContinuousCompactOriented_independentPairHybridSourceOverlapTransportEnergyBCF_le_sharedPlaquetteInfluence
      (periodicHypercubicFiniteOrientedGeometry n)
      N hN beta beta_nonneg target source hNe O

/-- On every active periodic neighbor, the integrated source transport energy is
bounded by the common explicit coefficient `eta_beta`. -/
theorem periodicHypercubicSpecialUnitary_independentPairHybridSourceOverlapTransportEnergyBCF_le_eta_of_active
    (n N : ℕ)
    [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target source : PeriodicHypercubicEdge n)
    (hActive : source ∈ periodicHypercubicActiveNeighbors n target)
    (O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).independentPairHybridSourceOverlapTransportEnergyBCF
        target source O ≤
      (2 * ‖O‖) ^ 2 * periodicHypercubicSpecialUnitaryDobrushinEta beta := by
  have hData :=
    (periodicHypercubicPhysical_mem_activeNeighbors_iff n target source).mp hActive
  have hNe : target ≠ source := Ne.symm hData.2
  calc
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).independentPairHybridSourceOverlapTransportEnergyBCF
        target source O ≤
      (2 * ‖O‖) ^ 2 *
        specialUnitaryCompactOrientedSharedPlaquetteInfluence
          (periodicHypercubicFiniteOrientedGeometry n)
          N hN beta beta_nonneg target source :=
      periodicHypercubicSpecialUnitary_independentPairHybridSourceOverlapTransportEnergyBCF_le_influence
        n N hN beta beta_nonneg target source hNe O
    _ = (2 * ‖O‖) ^ 2 *
        periodicHypercubicSpecialUnitaryDobrushinEta beta := by
      rw [periodicHypercubicSpecialUnitary_influence_eq_eta_of_active
        n N hn hN beta beta_nonneg target source hActive]

end

end MathlibAnalytic
end MGAP4D