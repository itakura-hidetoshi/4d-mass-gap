import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitBoundaryGramNoncollapseEquivalence
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSMidpointPairLaw
import Mathlib.Tactic

/-!
# Finite centered same-root decay as an actual Wilson midpoint correlation estimate

The current same-root mass-gap route has localized the remaining common Euclidean-time decay input
to finite boundary Gram moments.  This file exposes the underlying physical-time content one step
more explicitly.

The already-canonical factorial finite midpoint law is an exact statement about the actual finite
Wilson source: for every fixed nonnegative rational shift `r`, the symmetric pair of scalar
coordinates at `-(q+r)` and `q+r` has, eventually on the selected factorial tail, exactly the same
law as the midpoint-resolved pair at `-q` and `q+2r`.

We first integrate that finite pair-law identity against arbitrary bounded-continuous products.
For a literal fixed-slot carrier `F`, we then define the actual finite midpoint mean-subtracted
correlation

`M_n(F;r) = E_n[F(x_{-q}) F(x_{q+2r})] - E_n[tau_r F]^2`.

The translated centered OS form is eventually exactly `M_n(F;r)`.  Consequently the smoothed
boundary-Gram common-decay input is, under the explicit temporal-reach hypothesis already used by
the current route, exactly the statement

`M_n(F; s + t/2) <= exp(-m t) M_n(F; s)`

eventually, uniformly in every literal positive-time-smoothed fixed-slot carrier and every
nonnegative rational full time `t`.

Thus the remaining positive-rate problem is a genuine physical Euclidean two-time correlation
decay estimate for the actual finite Wilson-derived scalar process.  No stochastic update time,
old Hilbert carrier, transfer-operator premise, or numerical mass constant is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Finite factorial midpoint pair-law equality integrated against a product of arbitrary
bounded-continuous fixed-slot observables.  This is still an exact statement on the actual finite
Wilson-derived scalar path measure. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_osShiftedPair_product_expectation_eventually_eq_midpoint
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (r : ℚ) (hr : 0 ≤ r)
    (F G : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (∫ x,
          F (fun q : J => x (-(q.1 + r))) *
            G (fun q : J => x (q.1 + r))
        ∂periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n))
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
          (L.subsequence n)) =
        ∫ x,
          F (fun q : J => x (-q.1)) *
            G (fun q : J => x ((q.1 + r) + r))
          ∂periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence n) := by
  filter_upwards [
    L.factorial_osShiftedPair_law_eventually_eq_midpoint
      H N hN beta hbeta J hJ r hr] with n hn
  let μ : Measure (ℚ → ℝ) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      (L.subsequence n)
  let S : C(ℚ → ℝ, (∀ q : J, ℝ) × (∀ q : J, ℝ)) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSShiftedPairContinuousMap J r
  let M : C(ℚ → ℝ, (∀ q : J, ℝ) × (∀ q : J, ℝ)) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointPairContinuousMap J r
  let fstMap : C(((∀ q : J, ℝ) × (∀ q : J, ℝ)), ∀ q : J, ℝ) :=
    ⟨Prod.fst, continuous_fst⟩
  let sndMap : C(((∀ q : J, ℝ) × (∀ q : J, ℝ)), ∀ q : J, ℝ) :=
    ⟨Prod.snd, continuous_snd⟩
  let Phi : BoundedContinuousFunction ((∀ q : J, ℝ) × (∀ q : J, ℝ)) ℝ :=
    (F.compContinuous fstMap) * (G.compContinuous sndMap)
  change Measure.map S μ = Measure.map M μ at hn
  change (∫ x, Phi (S x) ∂μ) = ∫ x, Phi (M x) ∂μ
  calc
    (∫ x, Phi (S x) ∂μ) = ∫ z, Phi z ∂Measure.map S μ := by
      symm
      exact
        MeasureTheory.integral_map
          S.measurable.aemeasurable Phi.continuous.aestronglyMeasurable
    _ = ∫ z, Phi z ∂Measure.map M μ := by rw [hn]
    _ = ∫ x, Phi (M x) ∂μ := by
      exact
        MeasureTheory.integral_map
          M.measurable.aemeasurable Phi.continuous.aestronglyMeasurable

/-- Reindexed form of the finite midpoint product identity, on exactly the probability measures
used by the same-root finite-to-Hilbert centered-form bridge. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_osShiftedPair_product_expectation_reindexed_eventually_eq_midpoint
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (r : ℚ) (hr : 0 ≤ r)
    (F G : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (∫ x,
          F (fun q : J => x (-(q.1 + r))) *
            G (fun q : J => x (q.1 + r))
        ∂(periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n))
          (fun k =>
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
              (L.subsequence k))
          n : Measure (ℚ → ℝ))) =
        ∫ x,
          F (fun q : J => x (-q.1)) *
            G (fun q : J => x ((q.1 + r) + r))
          ∂(periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            (fun k =>
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
                (L.subsequence k))
            n : Measure (ℚ → ℝ)) := by
  have hraw :=
    L.factorial_osShiftedPair_product_expectation_eventually_eq_midpoint
      H N hN beta hbeta J hJ r hr F G
  filter_upwards [hraw] with n hn
  rw [←
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure_spacing_reindex
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      L.subsequence n]
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure_toMeasure]
  exact hn

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- Actual finite Wilson midpoint-resolved mean-subtracted correlation at total half-separation
`r`.  The two observable copies sit at the physical rational-time slots `-q` and `q+2r`; the
subtracted scalar is the actual finite mean of the translated cylinder `tau_r F`. -/
noncomputable def fixedSlotCarrierFiniteTranslatedMidpointMeanSubtractedCorrelation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (r : ℚ) (hr : 0 ≤ r)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) : ℝ :=
  let K := primaryScalarFiniteNonnegativeSlotIndexTimeTranslate r hr J
  let G := (P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate r hr F
  let m := (P.fixedSlotDataOfIndex K).fixedSlotCarrierFiniteMean G n
  let μ :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      (fun k =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
          (L.subsequence k))
      n
  (∫ x,
      F.observable (fun q : (P.fixedSlotDataOfIndex J).slots => x (-q.1)) *
        F.observable (fun q : (P.fixedSlotDataOfIndex J).slots => x ((q.1 + r) + r))
      ∂(μ : Measure (ℚ → ℝ))) - m ^ 2

/-- The current translated centered finite form is eventually exactly the midpoint-resolved actual
Wilson two-time correlation. -/
theorem fixedSlotCarrierFiniteTranslatedMeanSubtractedReflectionForm_eventually_eq_midpoint
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (r : ℚ) (hr : 0 ≤ r)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    ∀ᶠ n : ℕ in atTop,
      P.fixedSlotCarrierFiniteTranslatedMeanSubtractedReflectionForm J r hr F n =
        P.fixedSlotCarrierFiniteTranslatedMidpointMeanSubtractedCorrelation J r hr F n := by
  have hpair :=
    L.factorial_osShiftedPair_product_expectation_reindexed_eventually_eq_midpoint
      H N hN beta hbeta
      (P.fixedSlotDataOfIndex J).slots
      (fun q => (P.fixedSlotDataOfIndex J).slots_nonneg q.1 q.2)
      r hr F.observable F.observable
  filter_upwards [hpair] with n hn
  let K := primaryScalarFiniteNonnegativeSlotIndexTimeTranslate r hr J
  let G := (P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate r hr F
  let m := (P.fixedSlotDataOfIndex K).fixedSlotCarrierFiniteMean G n
  have hsub := congrArg (fun z : ℝ => z - m ^ 2) hn
  change
    ((∫ x,
        F.observable
            (fun q : (P.fixedSlotDataOfIndex J).slots => x (q.1 + r)) *
          F.observable
            (fun q : (P.fixedSlotDataOfIndex J).slots => x (-r + -q.1))
        ∂(periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n))
          (fun k =>
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
              (L.subsequence k))
          n : Measure (ℚ → ℝ))) - m ^ 2) =
      ((∫ x,
          F.observable
              (fun q : (P.fixedSlotDataOfIndex J).slots => x (-q.1)) *
            F.observable
              (fun q : (P.fixedSlotDataOfIndex J).slots => x ((q.1 + r) + r))
          ∂(periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            (fun k =>
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
                (L.subsequence k))
            n : Measure (ℚ → ℝ))) - m ^ 2)
  simpa [mul_comm] using hsub

/-- Midpoint-resolved form aligned with the positive smoothing time `s` and subsequent half-time
separation `h` used throughout the current finite gap reduction. -/
noncomputable def fixedSlotCarrierFiniteSmoothedCenteredMidpointCorrelation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) : ℝ :=
  P.fixedSlotCarrierFiniteTranslatedMidpointMeanSubtractedCorrelation
    J ((s : ℚ) + h) (add_nonneg s.2 hh) F n

/-- The exact finite centered quantity whose limit is the smoothed same-root Hilbert correlation is
eventually the literal physical-time midpoint correlation. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_eventually_eq_midpoint
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    ∀ᶠ n : ℕ in atTop,
      P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm J s h hh F n =
        P.fixedSlotCarrierFiniteSmoothedCenteredMidpointCorrelation J s h hh F n := by
  simpa [
    fixedSlotCarrierFiniteSmoothedCenteredReflectionForm,
    fixedSlotCarrierFiniteSmoothedCenteredMidpointCorrelation] using
    P.fixedSlotCarrierFiniteTranslatedMeanSubtractedReflectionForm_eventually_eq_midpoint
      J ((s : ℚ) + h) (add_nonneg s.2 hh) F

/-- Under explicit primary temporal-reach divergence, the finite boundary Gram moment itself is
eventually exactly the literal midpoint-resolved physical two-time correlation. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm_eventually_eq_midpoint
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
          H periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
        atTop atTop)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    ∀ᶠ n : ℕ in atTop,
      P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm J s h hh F n =
        P.fixedSlotCarrierFiniteSmoothedCenteredMidpointCorrelation J s h hh F n := by
  have hmid :=
    P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_eventually_eq_midpoint J s h hh F
  have hgram :=
    P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm_eventually_eq_boundaryGramMoment
      hreach J s h hh F
  filter_upwards [hmid, hgram] with n hmid_n hgram_n
  calc
    P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm J s h hh F n =
        P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm J s h hh F n :=
      hgram_n.symm
    _ = P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm J s h hh F n :=
      (P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_eq_wilsonSourceCentered
        J s h hh F n).symm
    _ = P.fixedSlotCarrierFiniteSmoothedCenteredMidpointCorrelation J s h hh F n :=
      hmid_n

/-- Common physical Euclidean-time decay stated directly on actual finite midpoint-resolved
centered two-time correlations. -/
def FixedSlotCarrierFiniteSmoothedCenteredMidpointUniformDecayAt
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (m : ℝ) : Prop :=
  ∀ (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat) (_hs : 0 < s)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (t : NNRat),
    ∀ᶠ n : ℕ in atTop,
      P.fixedSlotCarrierFiniteSmoothedCenteredMidpointCorrelation
          J s ((t : ℚ) / 2) (div_nonneg t.2 (by norm_num)) F n ≤
        Real.exp (-m * (t : ℝ)) *
          P.fixedSlotCarrierFiniteSmoothedCenteredMidpointCorrelation
            J s 0 le_rfl F n

/-- Under the already-explicit temporal-reach scaling input, common decay of the actual finite
boundary Gram moments is exactly common decay of the literal midpoint-resolved Wilson two-time
correlations. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramUniformDecayAt_iff_midpoint_of_temporalReach
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
          H periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
        atTop atTop)
    (m : ℝ) :
    P.FixedSlotCarrierFiniteSmoothedCenteredBoundaryGramUniformDecayAt m ↔
      P.FixedSlotCarrierFiniteSmoothedCenteredMidpointUniformDecayAt m := by
  constructor
  · intro hdec J s hs F t
    have hsep :=
      P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm_eventually_eq_midpoint
        hreach J s ((t : ℚ) / 2) (div_nonneg t.2 (by norm_num)) F
    have hzero :=
      P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm_eventually_eq_midpoint
        hreach J s 0 le_rfl F
    filter_upwards [hdec J s hs F t, hsep, hzero] with n hn hsep_n hzero_n
    rw [← hsep_n, ← hzero_n]
    exact hn
  · intro hdec J s hs F t
    have hsep :=
      P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm_eventually_eq_midpoint
        hreach J s ((t : ℚ) / 2) (div_nonneg t.2 (by norm_num)) F
    have hzero :=
      P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm_eventually_eq_midpoint
        hreach J s 0 le_rfl F
    filter_upwards [hdec J s hs F t, hsep, hzero] with n hn hsep_n hzero_n
    rw [hsep_n, hzero_n]
    exact hn

/-- The original finite common-decay hypothesis of the same-root mass-gap reduction is therefore,
under explicit temporal-reach divergence, exactly a common decay estimate for literal finite Wilson
midpoint correlations. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt_iff_midpoint_of_temporalReach
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
          H periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
        atTop atTop)
    (m : ℝ) :
    P.FixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt m ↔
      P.FixedSlotCarrierFiniteSmoothedCenteredMidpointUniformDecayAt m := by
  exact
    (P.fixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt_iff_boundaryGram_of_temporalReach
      hreach m).trans
      (P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramUniformDecayAt_iff_midpoint_of_temporalReach
        hreach m)

/-- Clean endpoint of the reduction: a strictly positive common decay rate for the literal finite
Wilson midpoint correlations, together with nontriviality of the exact same-root excitation sector,
produces a strictly positive coercivity certificate for the actual graph-closed Hamiltonian. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_positiveCoercivity_of_midpointDecay_of_nontrivial
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
          H periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
        atTop atTop)
    {m : ℝ}
    (hm : 0 < m)
    (hdec : P.FixedSlotCarrierFiniteSmoothedCenteredMidpointUniformDecayAt m)
    (hne : ∃ x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert, x ≠ 0) :
    ∃ μ : ℝ, 0 < μ ∧
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalCoerciveAt μ := by
  have hgram : P.FixedSlotCarrierFiniteSmoothedCenteredBoundaryGramUniformDecayAt m :=
    (P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramUniformDecayAt_iff_midpoint_of_temporalReach
      hreach m).2 hdec
  exact
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_positiveCoercivity_of_boundaryGramDecay_of_nontrivial
      hreach hm hgram hne

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
