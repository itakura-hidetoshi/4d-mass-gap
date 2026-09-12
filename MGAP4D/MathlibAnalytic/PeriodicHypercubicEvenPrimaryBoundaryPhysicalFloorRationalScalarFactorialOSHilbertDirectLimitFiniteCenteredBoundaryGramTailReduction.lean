import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitFiniteCenteredBoundaryGramMoment
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalSlotTemporalReach
import Mathlib.Tactic

/-!
# Factorial tail reduction to centered boundary Gram estimates

The preceding same-root layer identifies each admissible finite centered Wilson-source form with a
boundary integral of squared Bochner Gram moments.  The remaining geometric side condition is not
factorial alignment alone: every translated finite cylinder must also fit inside the actual primary
half extent.  This file discharges exactly that side condition from the already-explicit primary
temporal-reach hypothesis

`H_n * a_n -> +infinity`.

No relation between this reach and any separately named physical volume is asserted.  In
particular, reach divergence remains an explicit scaling input rather than something inferred from
Prokhorov compactness or factorial spacing.

After transporting reach divergence through the selected Prokhorov subsequence, every fixed
translated/smoothed literal cylinder is eventually admissible.  Hence the Wilson-source centered
forms and their boundary Gram-moment representations are eventually exactly equal.  The two
finite quantitative hypotheses isolated by the same-root mass-gap reduction are then proved
exactly equivalent to hypotheses stated directly on those boundary Gram moments:

* one common centered Euclidean-time decay rate;
* one strictly positive centered zero-separation floor.

Thus, under transparent primary temporal-reach divergence, the remaining quantitative problem is
localized to the actual finite boundary Gram moments.  No positive rate or positive floor is proved
here, and no heat-bath, old-carrier, or numerical mass constant is imported.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Divergence of the explicit primary temporal reach is preserved by every strictly cofinal
primary-scalar Prokhorov subsequence.  The reindexed lattice spacing is exactly the one used by the
current finite Wilson-source forms. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_primaryTemporalReach_tendsto_atTop
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
          H periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
        atTop atTop) :
    Tendsto
      (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
        (fun n => H (L.subsequence n))
        (fun n =>
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence n)))
      atTop atTop := by
  have hcomp := hreach.comp L.subsequence_strictMono.tendsto_atTop
  simpa [
    periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach,
    Function.comp_def] using hcomp

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- Every fixed translated literal cylinder used by the current same-root finite forms is
admissible on an eventual selected factorial tail once the explicit primary temporal reach
diverges. -/
theorem fixedSlotCarrierFiniteTranslatedCentered_eventually_admissible_of_temporalReach
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
          H periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
        atTop atTop)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    ∀ᶠ n : ℕ in atTop,
      let K := primaryScalarFiniteNonnegativeSlotIndexTimeTranslate h hh J
      let G := (P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate h hh F
      let Cyl := (P.fixedSlotDataOfIndex K).fixedSlotCarrierPositiveCylinder G
      PeriodicHypercubicEvenPrimarySpatialPositiveRationalSlotsAdmissible
        (H (L.subsequence n))
        (fun k =>
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence k))
        n Cyl.slots := by
  let K := primaryScalarFiniteNonnegativeSlotIndexTimeTranslate h hh J
  let G := (P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate h hh F
  let Cyl := (P.fixedSlotDataOfIndex K).fixedSlotCarrierPositiveCylinder G
  let H' : ℕ → ℕ := fun n => H (L.subsequence n)
  let spacing' : ℕ → ℝ := fun n =>
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      (L.subsequence n)
  have hspacing' : ∀ n, 0 < spacing' n := by
    intro n
    exact
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        (L.subsequence n)
  have hreach' :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H' spacing')
        atTop atTop := by
    simpa [H', spacing'] using
      L.factorial_primaryTemporalReach_tendsto_atTop H N hN beta hbeta hreach
  have htail :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder_eventually_admissible_of_temporalReach
      H' spacing' hspacing' hreach' Cyl
  simpa [H', spacing', K, G, Cyl] using htail

/-- The smoothed centered cylinder at fixed positive smoothing time and fixed subsequent separation
is eventually admissible on the selected factorial tail under the same explicit reach input. -/
theorem fixedSlotCarrierFiniteSmoothedCentered_eventually_admissible_of_temporalReach
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
      let K := primaryScalarFiniteNonnegativeSlotIndexTimeTranslate
        ((s : ℚ) + h) (add_nonneg s.2 hh) J
      let G := (P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate
        ((s : ℚ) + h) (add_nonneg s.2 hh) F
      let Cyl := (P.fixedSlotDataOfIndex K).fixedSlotCarrierPositiveCylinder G
      PeriodicHypercubicEvenPrimarySpatialPositiveRationalSlotsAdmissible
        (H (L.subsequence n))
        (fun k =>
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence k))
        n Cyl.slots := by
  simpa only using
    P.fixedSlotCarrierFiniteTranslatedCentered_eventually_admissible_of_temporalReach
      hreach J ((s : ℚ) + h) (add_nonneg s.2 hh) F

/-- Under explicit reach divergence, every fixed translated centered Wilson-source form is
eventually exactly its boundary Gram-moment square integral. -/
theorem fixedSlotCarrierFiniteTranslatedCenteredWilsonSourceReflectionForm_eventually_eq_boundaryGramMoment
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
          H periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
        atTop atTop)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    ∀ᶠ n : ℕ in atTop,
      P.fixedSlotCarrierFiniteTranslatedCenteredWilsonSourceReflectionForm J h hh F n =
        P.fixedSlotCarrierFiniteTranslatedCenteredBoundaryGramMomentForm J h hh F n := by
  filter_upwards [
    P.fixedSlotCarrierFiniteTranslatedCentered_eventually_admissible_of_temporalReach
      hreach J h hh F] with n hn
  exact
    P.fixedSlotCarrierFiniteTranslatedCenteredWilsonSourceReflectionForm_eq_boundaryGramMoment
      J h hh F n hn

/-- Under explicit reach divergence, every fixed smoothed centered Wilson-source form is eventually
exactly its boundary Gram-moment square integral. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm_eventually_eq_boundaryGramMoment
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
      P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm J s h hh F n =
        P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm J s h hh F n := by
  filter_upwards [
    P.fixedSlotCarrierFiniteSmoothedCentered_eventually_admissible_of_temporalReach
      hreach J s h hh F] with n hn
  exact
    P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm_eq_boundaryGramMoment
      J s h hh F n hn

/-- Common centered Euclidean-time decay stated entirely on the actual finite boundary Gram-moment
square integrals. -/
def FixedSlotCarrierFiniteSmoothedCenteredBoundaryGramUniformDecayAt
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (m : ℝ) : Prop :=
  ∀ (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat) (_hs : 0 < s)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (t : NNRat),
    ∀ᶠ n : ℕ in atTop,
      P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm
          J s ((t : ℚ) / 2) (div_nonneg t.2 (by norm_num)) F n ≤
        Real.exp (-m * (t : ℝ)) *
          P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm
            J s 0 le_rfl F n

/-- One strictly positive zero-separation tail floor, stated entirely on an actual finite boundary
Gram-moment square integral. -/
def FixedSlotCarrierFiniteSmoothedCenteredBoundaryGramPositiveFloor
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) : Prop :=
  ∃ v : ℝ, 0 < v ∧
    ∃ J : PrimaryScalarFiniteNonnegativeSlotIndex,
      ∃ s : NNRat, ∃ _hs : 0 < s,
        ∃ F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier,
          ∀ᶠ n : ℕ in atTop,
            v ≤ P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm
              J s 0 le_rfl F n

/-- Under explicit temporal-reach divergence, common centered decay on the actual Wilson-source
forms is exactly equivalent to common decay on their eventual boundary Gram-moment
representations. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceUniformDecayAt_iff_boundaryGram_of_temporalReach
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
          H periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
        atTop atTop)
    (m : ℝ) :
    P.FixedSlotCarrierFiniteSmoothedCenteredWilsonSourceUniformDecayAt m ↔
      P.FixedSlotCarrierFiniteSmoothedCenteredBoundaryGramUniformDecayAt m := by
  constructor
  · intro hdec J s hs F t
    have hsep :=
      P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm_eventually_eq_boundaryGramMoment
        hreach J s ((t : ℚ) / 2) (div_nonneg t.2 (by norm_num)) F
    have hzero :=
      P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm_eventually_eq_boundaryGramMoment
        hreach J s 0 le_rfl F
    filter_upwards [hdec J s hs F t, hsep, hzero] with n hn hsep_n hzero_n
    rw [← hsep_n, ← hzero_n]
    exact hn
  · intro hdec J s hs F t
    have hsep :=
      P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm_eventually_eq_boundaryGramMoment
        hreach J s ((t : ℚ) / 2) (div_nonneg t.2 (by norm_num)) F
    have hzero :=
      P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm_eventually_eq_boundaryGramMoment
        hreach J s 0 le_rfl F
    filter_upwards [hdec J s hs F t, hsep, hzero] with n hn hsep_n hzero_n
    rw [hsep_n, hzero_n]
    exact hn

/-- Under explicit temporal-reach divergence, the Wilson-source noncollapse input is exactly
equivalent to a positive tail floor for one actual boundary Gram-moment square integral. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredWilsonSourcePositiveFloor_iff_boundaryGram_of_temporalReach
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
          H periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
        atTop atTop) :
    P.FixedSlotCarrierFiniteSmoothedCenteredWilsonSourcePositiveFloor ↔
      P.FixedSlotCarrierFiniteSmoothedCenteredBoundaryGramPositiveFloor := by
  constructor
  · rintro ⟨v, hv, J, s, hs, F, hfloor⟩
    refine ⟨v, hv, J, s, hs, F, ?_⟩
    have heq :=
      P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm_eventually_eq_boundaryGramMoment
        hreach J s 0 le_rfl F
    filter_upwards [hfloor, heq] with n hn heq_n
    rw [← heq_n]
    exact hn
  · rintro ⟨v, hv, J, s, hs, F, hfloor⟩
    refine ⟨v, hv, J, s, hs, F, ?_⟩
    have heq :=
      P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm_eventually_eq_boundaryGramMoment
        hreach J s 0 le_rfl F
    filter_upwards [hfloor, heq] with n hn heq_n
    rw [heq_n]
    exact hn

/-- The original finite common-decay hypothesis from the same-root mass-gap reduction is, under
explicit temporal-reach divergence, exactly a common decay estimate on the actual boundary Gram
moments. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt_iff_boundaryGram_of_temporalReach
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
      P.FixedSlotCarrierFiniteSmoothedCenteredBoundaryGramUniformDecayAt m := by
  exact
    (P.fixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt_iff_wilsonSource m).trans
      (P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceUniformDecayAt_iff_boundaryGram_of_temporalReach
        hreach m)

/-- The original finite noncollapse hypothesis from the same-root mass-gap reduction is, under
explicit temporal-reach divergence, exactly a positive tail floor on one actual boundary Gram
moment. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredPositiveFloor_iff_boundaryGram_of_temporalReach
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
          H periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
        atTop atTop) :
    P.FixedSlotCarrierFiniteSmoothedCenteredPositiveFloor ↔
      P.FixedSlotCarrierFiniteSmoothedCenteredBoundaryGramPositiveFloor := by
  exact
    P.fixedSlotCarrierFiniteSmoothedCenteredPositiveFloor_iff_wilsonSource.trans
      (P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourcePositiveFloor_iff_boundaryGram_of_temporalReach
        hreach)

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
