import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityEigenspaceInternalDecompositionReceiptL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroPointSpectrumIntegerGridL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroAllCardinalityFiniteSetProductWitnessL2
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The finite real cardinality grid attached to a finite coordinate type. -/
def continuousLinearMapCardinalityIntegerGridL2
    {ι : Type*}
    [Fintype ι] :
    Set ℝ :=
  Set.range fun k : Fin (Fintype.card ι + 1) => (k.1 : ℝ)

/-- Explicit resolvent candidate obtained by inverting the scalar action on each
cardinality sector. -/
noncomputable def continuousLinearMapCardinalityResolventCandidateL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (lam : ℝ)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    V →L[ℝ] V :=
  ∑ k ∈ Finset.range (Fintype.card ι + 1),
    (lam - (k : ℝ))⁻¹ •
      continuousLinearMapCardinalitySectorProjectorL2 Q k hComm

/-- A scalar outside the cardinality grid differs from every admissible integer
weight. -/
theorem continuousLinearMap_cardinalityResolventCoefficient_ne_zero
    {ι : Type*}
    [Fintype ι]
    {lam : ℝ}
    (hLam : lam ∉ continuousLinearMapCardinalityIntegerGridL2 (ι := ι))
    {k : ℕ}
    (hk : k < Fintype.card ι + 1) :
    lam - (k : ℝ) ≠ 0 := by
  intro hZero
  apply hLam
  refine ⟨⟨k, hk⟩, ?_⟩
  exact (sub_eq_zero.mp hZero).symm

/-- One cardinality-resolvent summand is a left inverse on its matching sector. -/
theorem continuousLinearMap_algebraMap_sub_univ_sum_mul_inv_smul_cardinalitySectorProjectorL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (lam : ℝ)
    (k : ℕ)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (hNe : lam - (k : ℝ) ≠ 0) :
    (algebraMap ℝ (V →L[ℝ] V) lam - ∑ i : ι, Q i) *
        ((lam - (k : ℝ))⁻¹ •
          continuousLinearMapCardinalitySectorProjectorL2 Q k hComm) =
      continuousLinearMapCardinalitySectorProjectorL2 Q k hComm := by
  rw [mul_smul_comm]
  rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [continuousLinearMap_univ_sum_mul_cardinalitySectorProjectorL2_eq_natCast_smul
    Q k hIdempotent hComm]
  rw [← sub_smul, smul_smul, inv_mul_cancel₀ hNe, one_smul]

/-- One cardinality-resolvent summand is a right inverse on its matching sector. -/
theorem continuousLinearMap_inv_smul_cardinalitySectorProjectorL2_mul_algebraMap_sub_univ_sum
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (lam : ℝ)
    (k : ℕ)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (hk : k ≤ Fintype.card ι)
    (hNe : lam - (k : ℝ) ≠ 0) :
    ((lam - (k : ℝ))⁻¹ •
        continuousLinearMapCardinalitySectorProjectorL2 Q k hComm) *
        (algebraMap ℝ (V →L[ℝ] V) lam - ∑ i : ι, Q i) =
      continuousLinearMapCardinalitySectorProjectorL2 Q k hComm := by
  rw [smul_mul_assoc]
  rw [mul_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  rw [continuousLinearMap_cardinalitySectorProjectorL2_mul_univ_sum_eq_natCast_smul
    Q k hIdempotent hComm hk]
  rw [← sub_smul, smul_smul, inv_mul_cancel₀ hNe, one_smul]

/-- The explicit cardinality resolvent is a left inverse outside the finite
integer grid. -/
theorem continuousLinearMap_algebraMap_sub_univ_sum_mul_cardinalityResolventCandidateL2_eq_one
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (lam : ℝ)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (hLam : lam ∉ continuousLinearMapCardinalityIntegerGridL2 (ι := ι)) :
    (algebraMap ℝ (V →L[ℝ] V) lam - ∑ i : ι, Q i) *
        continuousLinearMapCardinalityResolventCandidateL2 Q lam hComm = 1 := by
  classical
  rw [continuousLinearMapCardinalityResolventCandidateL2, Finset.mul_sum]
  calc
    (∑ k ∈ Finset.range (Fintype.card ι + 1),
        (algebraMap ℝ (V →L[ℝ] V) lam - ∑ i : ι, Q i) *
          ((lam - (k : ℝ))⁻¹ •
            continuousLinearMapCardinalitySectorProjectorL2 Q k hComm)) =
      ∑ k ∈ Finset.range (Fintype.card ι + 1),
        continuousLinearMapCardinalitySectorProjectorL2 Q k hComm := by
      apply Finset.sum_congr rfl
      intro k hk
      exact
        continuousLinearMap_algebraMap_sub_univ_sum_mul_inv_smul_cardinalitySectorProjectorL2
          Q lam k hIdempotent hComm
          (continuousLinearMap_cardinalityResolventCoefficient_ne_zero
            hLam (Finset.mem_range.mp hk))
    _ = 1 :=
      continuousLinearMap_sum_range_cardinalitySectorProjectorL2_eq_one Q hComm

/-- The explicit cardinality resolvent is a right inverse outside the finite
integer grid. -/
theorem continuousLinearMap_cardinalityResolventCandidateL2_mul_algebraMap_sub_univ_sum_eq_one
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (lam : ℝ)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f))
    (hLam : lam ∉ continuousLinearMapCardinalityIntegerGridL2 (ι := ι)) :
    continuousLinearMapCardinalityResolventCandidateL2 Q lam hComm *
        (algebraMap ℝ (V →L[ℝ] V) lam - ∑ i : ι, Q i) = 1 := by
  classical
  rw [continuousLinearMapCardinalityResolventCandidateL2, Finset.sum_mul]
  calc
    (∑ k ∈ Finset.range (Fintype.card ι + 1),
        ((lam - (k : ℝ))⁻¹ •
            continuousLinearMapCardinalitySectorProjectorL2 Q k hComm) *
          (algebraMap ℝ (V →L[ℝ] V) lam - ∑ i : ι, Q i)) =
      ∑ k ∈ Finset.range (Fintype.card ι + 1),
        continuousLinearMapCardinalitySectorProjectorL2 Q k hComm := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkLe : k ≤ Fintype.card ι :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      exact
        continuousLinearMap_inv_smul_cardinalitySectorProjectorL2_mul_algebraMap_sub_univ_sum
          Q lam k hIdempotent hComm hkLe
          (continuousLinearMap_cardinalityResolventCoefficient_ne_zero
            hLam (Finset.mem_range.mp hk))
    _ = 1 :=
      continuousLinearMap_sum_range_cardinalitySectorProjectorL2_eq_one Q hComm

/-- The spectrum of a finite sum of commuting idempotents is contained in the
finite cardinality grid.  No finite-dimensionality assumption is used. -/
theorem continuousLinearMap_spectrum_univ_sum_commuting_idempotents_subset_cardinalityIntegerGridL2
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (Q : ι → V →L[ℝ] V)
    (hIdempotent : ∀ i : ι, ∀ f : V, Q i (Q i f) = Q i f)
    (hComm : ∀ i j : ι, ∀ f : V, Q i (Q j f) = Q j (Q i f)) :
    spectrum ℝ (∑ i : ι, Q i) ⊆
      continuousLinearMapCardinalityIntegerGridL2 (ι := ι) := by
  intro lam hSpectrum
  by_contra hLam
  have hResolvent : lam ∈ resolventSet ℝ (∑ i : ι, Q i) :=
    spectrum.mem_resolventSet_of_left_right_inverse
      (continuousLinearMap_algebraMap_sub_univ_sum_mul_cardinalityResolventCandidateL2_eq_one
        Q lam hIdempotent hComm hLam)
      (continuousLinearMap_cardinalityResolventCandidateL2_mul_algebraMap_sub_univ_sum_eq_one
        Q lam hIdempotent hComm hLam)
  have hNotResolvent : lam ∉ resolventSet ℝ (∑ i : ι, Q i) := by
    simpa [spectrum] using hSpectrum
  exact hNotResolvent hResolvent

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_fullSpectrumEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- Explicit actual resolvent candidate for the finite-volume beta-zero
heat-bath Hamiltonian. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathResolventCandidateL2
    (lam : ℝ) :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  ∑ k ∈ Finset.range 325,
    (lam - (k : ℝ))⁻¹ •
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2 k

/-- The actual resolvent candidate is a left inverse outside the integer grid. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_algebraMap_sub_heatBathHamiltonianL2_mul_resolventCandidate_eq_one
    (lam : ℝ)
    (hLam : lam ∉
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2) :
    (algebraMap ℝ
        (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
          Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
        lam -
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2) *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathResolventCandidateL2 lam = 1 := by
  classical
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_univ_sum_fluctuationL2]
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathResolventCandidateL2,
    continuousLinearMapCardinalityResolventCandidateL2,
    continuousLinearMapCardinalityIntegerGridL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324] using
      (continuousLinearMap_algebraMap_sub_univ_sum_mul_cardinalityResolventCandidateL2_eq_one
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        lam
        (fun edge f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
            edge f)
        (fun target source f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
            target source f)
        hLam)

/-- The actual resolvent candidate is a right inverse outside the integer grid. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_resolventCandidate_mul_algebraMap_sub_heatBathHamiltonianL2_eq_one
    (lam : ℝ)
    (hLam : lam ∉
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathResolventCandidateL2 lam *
        (algebraMap ℝ
            (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
              Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            lam -
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2) = 1 := by
  classical
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_univ_sum_fluctuationL2]
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathResolventCandidateL2,
    continuousLinearMapCardinalityResolventCandidateL2,
    continuousLinearMapCardinalityIntegerGridL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324] using
      (continuousLinearMap_cardinalityResolventCandidateL2_mul_algebraMap_sub_univ_sum_eq_one
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        lam
        (fun edge f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
            edge f)
        (fun target source f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
            target source f)
        hLam)

/-- The full real operator spectrum is contained in the actual integer grid. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathSpectrumL2_subset_allowed_integer_grid :
    spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 ⊆
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2 := by
  classical
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_univ_sum_fluctuationL2]
  simpa [continuousLinearMapCardinalityIntegerGridL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324] using
      (continuousLinearMap_spectrum_univ_sum_commuting_idempotents_subset_cardinalityIntegerGridL2
        (Q := fun edge :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
              edge)
        (fun edge f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
            edge f)
        (fun target source f =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
            target source f))

/-- Every admissible integer grid value belongs to the full real operator
spectrum because its cardinality projector is nonzero and is annihilated by the
corresponding shifted Hamiltonian. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_allowed_integer_grid_subset_heatBathSpectrumL2 :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2 ⊆
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 := by
  rintro lam ⟨k, rfl⟩
  rw [spectrum.mem_iff]
  intro hUnit
  let E :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      k.1
  have hkLe : k.1 ≤ 324 := by omega
  have hE : E ≠ 0 := by
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_of_le_324
        k.1 hkLe
  have hAnnihilate :
      (algebraMap ℝ
          (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
            Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (k.1 : ℝ) -
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2) * E = 0 := by
    rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_mul_fluctuationCardinalityProjectorL2_eq_natCast_smul]
    rw [sub_self]
  let u := hUnit.unit
  have hu :
      (u :
          Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
            Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
        algebraMap ℝ
            (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
              Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            (k.1 : ℝ) -
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 :=
    hUnit.unit_spec
  have hEZero : E = 0 := by
    calc
      E = ((↑(u⁻¹) :
          Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
            Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) *
          (u :
            Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
              Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) * E := by
            rw [u.inv_mul, one_mul]
      _ = (↑(u⁻¹) :
          Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
            Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) *
          ((u :
            Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
              Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) * E) := by
            rw [mul_assoc]
      _ = 0 := by rw [hu, hAnnihilate, mul_zero]
  exact hE hEZero

/-- The full real operator spectrum is exactly the 325-point integer grid. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathSpectrumL2_eq_allowed_integer_grid :
    spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2 := by
  exact Set.Subset.antisymm
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathSpectrumL2_subset_allowed_integer_grid
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_allowed_integer_grid_subset_heatBathSpectrumL2

/-- The actual point spectrum also equals the complete 325-point integer grid. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_eq_allowed_integer_grid :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2 := by
  apply Set.Subset.antisymm
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_subset_allowed_integer_grid
  · rintro lam ⟨k, rfl⟩
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_mem_heatBathPointSpectrumL2_of_le_324
        k.1 (by omega)

/-- There is no residual full-spectrum part beyond the point spectrum in the
finite-volume beta-zero system. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_eq_heatBathSpectrumL2 :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 =
      spectrum ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_eq_allowed_integer_grid,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathSpectrumL2_eq_allowed_integer_grid]

/-- Compact receipt for the exact finite-volume beta-zero full spectrum. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFullSpectrumIntegerGridL2Receipt :
    Prop :=
  (∀ lam : ℝ,
    lam ∉ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2 →
      (algebraMap ℝ
          (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
            Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          lam -
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2) *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathResolventCandidateL2 lam = 1 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathResolventCandidateL2 lam *
          (algebraMap ℝ
              (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
                Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
              lam -
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2) = 1) ∧
  spectrum ℝ
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 =
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2 ∧
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 =
    spectrum ℝ
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2

/-- The exact finite-volume beta-zero full-spectrum receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFullSpectrumIntegerGridL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFullSpectrumIntegerGridL2Receipt := by
  exact ⟨
    fun lam hLam => ⟨
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_algebraMap_sub_heatBathHamiltonianL2_mul_resolventCandidate_eq_one
        lam hLam,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_resolventCandidate_mul_algebraMap_sub_heatBathHamiltonianL2_eq_one
        lam hLam⟩,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathSpectrumL2_eq_allowed_integer_grid,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_eq_heatBathSpectrumL2⟩

end

end MathlibAnalytic
end MGAP4D
