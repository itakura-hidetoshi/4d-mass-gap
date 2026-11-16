import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedBeta0PlaquetteIncidenceGreenL1V5_PZ37AMI
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRandomScanGibbsCovarianceTelescope
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRandomScanGibbsCovarianceRemainderLimit
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMJ — true original beta0 SU2 all-plaquette Gibbs covariance L1

AMI already proves for the ORIGINAL interacting finite-volume SU2 Wilson Gibbs
model: every physical link is incident to at most 6 coordinate plaquettes,
the sum over all real plaquette character variation profiles at a fixed link
is at most 12, and the original fixed-plaquette finite Dobrushin random-scan
Green resolvent has total link variation at most 8/(1-rho0).

This file combines those source-certified pieces with the already-proved
ACTUAL compact-Haar Gibbs random-scan covariance telescope and its vanishing
remainder. First a generic finite-family covariance-summation theorem is
proved, then specialized to every genuine four-edge physical SU2 plaquette.

The result is the UNCONDITIONAL (no support-separation hypothesis) finite-
volume uniform all-plaquette absolute Gibbs susceptibility bound
  sum_q |Cov_Gibbs(chi_q,chi_p)| <= 96/(1-rho0), for every H>0.
This does NOT assert spatial coordinate distance decay, all-H physical OS
transfer spectral gap, Hamiltonian spectral gap, changing continuum coupling
compatibility or four-dimensional Yang--Mills continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Finite-family theorem for the actual compact Wilson Gibbs covariance:
an L1 bound on all left-observable link variations, together with a bound on
the right-observable actual random-scan Green resolvent total link variation,
bounds the sum of ABSOLUTE finite Gibbs connected correlations.

The proof is the true finite random-scan covariance telescope, interchange of
two finite sums, and the existing independent zero-remainder limit. There is
no imposed covariance inequality, product-measure approximation or invented
free-Haar law. -/
theorem compactOrientedGibbsCovariance_abs_sum_le_of_finiteFamilyGreenL1
    {ι : Type*} [Fintype ι]
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (F : ι → BoundedContinuousFunction C.base.Configuration ℝ)
    (PF : (i : ι) →
      ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
        (fun A => F i A))
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (B R : ℝ)
    (hBNonneg : 0 ≤ B)
    (hFamilyVariation :
      ∀ e : C.base.geometry.Edge, (∑ i : ι, (PF i).variation e) ≤ B)
    (hGreenL1 : ∀ M : ℕ,
      continuousCompactOrientedGaugeWilsonTotalVariation
        (continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
          D P.variation M) ≤ R) :
    (∑ i : ι,
      |C.gibbsCovarianceReal (fun A => F i A) (fun A => O A)|) ≤
        B * R := by
  classical
  let w (M : ℕ) (e : C.base.geometry.Edge) : ℝ :=
    continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
      D P.variation M e
  have hwNonneg (M : ℕ) (e : C.base.geometry.Edge) :
      0 ≤ w M e :=
    continuous_compact_oriented_dobrushinRandomScanFiniteResolventProfile_nonneg
      D P.variation P.variation_nonneg M e
  have hwL1 (M : ℕ) :
      (∑ e : C.base.geometry.Edge, w M e) ≤ R := by
    simpa only [w, continuousCompactOrientedGaugeWilsonTotalVariation] using
      hGreenL1 M
  have hFinite (M : ℕ) :
      (∑ i : ι,
        |C.gibbsCovarianceReal (fun A => F i A) (fun A => O A) -
          C.gibbsCovarianceReal (fun A => F i A)
            (fun A =>
              ((P.toRandomScanCenteredState).randomScanIterate D M).observable A)|)
        ≤ B * R := by
    calc
      (∑ i : ι,
        |C.gibbsCovarianceReal (fun A => F i A) (fun A => O A) -
          C.gibbsCovarianceReal (fun A => F i A)
            (fun A =>
              ((P.toRandomScanCenteredState).randomScanIterate D M).observable A)|)
          ≤ ∑ i : ι, ∑ e : C.base.geometry.Edge,
                (PF i).variation e * w M e := by
          apply Finset.sum_le_sum
          intro i _
          simpa only [w] using
            (continuous_compact_oriented_gibbsCovarianceReal_randomScanCenteredState_partial_telescope_abs_le_finiteResolventProfile
              C hEdge (F i) (PF i) P D M)
      _ = ∑ e : C.base.geometry.Edge,
            ∑ i : ι, (PF i).variation e * w M e := by
          rw [Finset.sum_comm]
      _ = ∑ e : C.base.geometry.Edge,
            (∑ i : ι, (PF i).variation e) * w M e := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.sum_mul]
      _ ≤ ∑ e : C.base.geometry.Edge, B * w M e := by
          apply Finset.sum_le_sum
          intro e _
          exact mul_le_mul_of_nonneg_right
            (hFamilyVariation e) (hwNonneg M e)
      _ = B * ∑ e : C.base.geometry.Edge, w M e := by
          rw [Finset.mul_sum]
      _ ≤ B * R := mul_le_mul_of_nonneg_left (hwL1 M) hBNonneg
  have hTermTendsto (i : ι) :
      Tendsto
        (fun M : ℕ =>
          |C.gibbsCovarianceReal (fun A => F i A) (fun A => O A) -
            C.gibbsCovarianceReal (fun A => F i A)
              (fun A =>
                ((P.toRandomScanCenteredState).randomScanIterate D M).observable A)|)
        atTop
        (nhds |C.gibbsCovarianceReal (fun A => F i A) (fun A => O A)|) := by
    have hRemainder :=
      continuous_compact_oriented_gibbsCovarianceReal_randomScanCenteredState_iterate_tendsto_zero
        C (F i) O P D D.coefficient_nonneg D.coefficient_lt_one hEdge
    have hSub :
        Tendsto
          (fun M : ℕ =>
            C.gibbsCovarianceReal (fun A => F i A) (fun A => O A) -
              C.gibbsCovarianceReal (fun A => F i A)
                (fun A =>
                  ((P.toRandomScanCenteredState).randomScanIterate D M).observable A))
          atTop
          (nhds (C.gibbsCovarianceReal (fun A => F i A) (fun A => O A) - 0)) :=
      tendsto_const_nhds.sub hRemainder
    simpa using hSub.abs
  have hSumTendsto :
      Tendsto
        (fun M : ℕ =>
          ∑ i : ι,
            |C.gibbsCovarianceReal (fun A => F i A) (fun A => O A) -
              C.gibbsCovarianceReal (fun A => F i A)
                (fun A =>
                  ((P.toRandomScanCenteredState).randomScanIterate D M).observable A)|)
        atTop
        (nhds (∑ i : ι,
          |C.gibbsCovarianceReal (fun A => F i A) (fun A => O A)|)) := by
    refine tendsto_finset_sum _ (fun i _ => ?_)
    exact hTermTendsto i
  exact le_of_tendsto' hSumTendsto hFinite

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "beta0" => GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling

private instance p4Q2PZ37AMJ_nezero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  change 2 * (H + 1) ≠ 0
  omega⟩
private instance p4Q2PZ37AMJ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
private instance p4Q2PZ37AMJ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
private instance p4Q2PZ37AMJ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
private instance p4Q2PZ37AMJ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
private instance p4Q2PZ37AMJ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
private instance p4Q2PZ37AMJ_nontrivial : Nontrivial G := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : G => (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace GroundStatePosteriorJoint

/-- The ORIGINAL interacting fixed-beta0 finite-volume SU2 Wilson Gibbs law
has volume-independent absolute connected-correlation summability over ALL
genuine oriented four-edge physical plaquettes, for each selected p, H>0.

No assumption of disjoint supports or of any positive pairwise distance is
needed. The uniform constant is 96/(1-rho0). The proof uses the actual Gibbs
random-scan covariance telescope, not random-scan update time as Euclidean
time. No physical OS transfer or 4D continuum Yang--Mills mass gap follows. -/
theorem p4Q2PZ37AMJ_originalFixedBeta0PhysicalPlaquetteGibbsCovariance_l1_le
    (H : ℕ) (hH : 0 < H)
    (p : PeriodicHypercubicEvenPlaquette H) :
    (∑ q : PeriodicHypercubicEvenPlaquette H,
      |(p4Q2PZ37AMG_originalFixedBeta0System H).gibbsCovarianceReal
        (fun A => p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H q A)
        (fun A => p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H p A)|) ≤
      96 * (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta0)⁻¹ := by
  let C := p4Q2PZ37AMG_originalFixedBeta0System H
  let F : PeriodicHypercubicEvenPlaquette H →
      BoundedContinuousFunction C.base.Configuration ℝ :=
    fun q => p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H q
  let PF (q : PeriodicHypercubicEvenPlaquette H) :
      ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
        (fun A => F q A) :=
    ContinuousCompactOrientedGaugeWilsonLinkVariationBound.ofFiniteSupport
      (C := C) (F q) (periodicHypercubicEvenPlaquetteEdgeSupport H q)
      (fun A B hAB =>
        p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF_eq_of_eqOn_edges
          H q A B hAB)
  let O : BoundedContinuousFunction C.base.Configuration ℝ := F p
  let P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O :=
    ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile.ofFiniteSupport
      (C := C) O (periodicHypercubicEvenPlaquetteEdgeSupport H p)
      (fun A B hAB =>
        p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF_eq_of_eqOn_edges
          H p A B hAB)
  let Ddata : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C :=
    periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
      (PeriodicHypercubicEvenSideLength H) 2
      (by change 3 ≤ 2 * (H + 1); omega)
      (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
      p4Q2PZ37AMG_originalFixedBeta0ActiveTVMajorant_strict
  have hEdge : 0 < Fintype.card (PeriodicHypercubicEvenEdge H) :=
    periodicHypercubicEvenEdge_card_pos H
  have hFamily (e : PeriodicHypercubicEvenEdge H) :
      (∑ q : PeriodicHypercubicEvenPlaquette H,
        (PF q).variation e) ≤ 12 := by
    change
      (∑ q : PeriodicHypercubicEvenPlaquette H,
        if e ∈ periodicHypercubicEvenPlaquetteEdgeSupport H q
          then 2 * ‖p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H q‖
          else (0 : ℝ)) ≤ 12
    exact p4Q2PZ37AMI_originalPlaquetteCharacterVariationAtLink_sum_le_twelve H e
  have hMass (M : ℕ) :
      continuousCompactOrientedGaugeWilsonTotalVariation
        (continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
          Ddata P.variation M) ≤
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta0)⁻¹ * 8 := by
    simpa only [C, F, O, P, Ddata] using
      p4Q2PZ37AMI_originalPhysicalPlaquetteRandomScanGreenL1_le_eight
        H M hH p
  have hEstimate :
      (∑ q : PeriodicHypercubicEvenPlaquette H,
        |C.gibbsCovarianceReal (fun A => F q A) (fun A => O A)|) ≤
        (12 : ℝ) *
          ((1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta0)⁻¹ * 8) :=
    compactOrientedGibbsCovariance_abs_sum_le_of_finiteFamilyGreenL1
      C hEdge F PF P Ddata 12
      ((1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta0)⁻¹ * 8)
      (by norm_num) hFamily hMass
  calc
    (∑ q : PeriodicHypercubicEvenPlaquette H,
      |(p4Q2PZ37AMG_originalFixedBeta0System H).gibbsCovarianceReal
        (fun A => p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H q A)
        (fun A => p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H p A)|) =
      ∑ q : PeriodicHypercubicEvenPlaquette H,
        |C.gibbsCovarianceReal (fun A => F q A) (fun A => O A)| := by rfl
    _ ≤ (12 : ℝ) *
          ((1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta0)⁻¹ * 8) :=
      hEstimate
    _ = 96 * (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta0)⁻¹ := by
      ring

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.compactOrientedGibbsCovariance_abs_sum_le_of_finiteFamilyGreenL1
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMJ_originalFixedBeta0PhysicalPlaquetteGibbsCovariance_l1_le
