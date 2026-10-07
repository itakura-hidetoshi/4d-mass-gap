import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentSwappedSeedRightResampling
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedDistance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorVariationPropagation
import Mathlib.Tactic

/-!
# Four-link posterior variation profile of the canonical Gram--Schmidt seed

The swapped receiver of PR #5244 places the actual mode-dependent factor on
the right endpoint, where the existing posterior one-link machinery acts.

At Krylov depth zero this factor is the theorem-generated SU(2)
primary-plaquette Gram--Schmidt mode.  The next safe locality statement is not
to identify that mode with one posterior local Boltzmann factor.  Instead, this
file records its actual finite coordinate support.

The continuous Gram--Schmidt slice observable depends on the holonomy of the
canonical primary spatial plaquette, hence on exactly its four spatial links.
We package this as a proof-relevant posterior link-variation bound

  delta_e = 2 ||O||  on the four seed links,
            0         off the seed.

This supplies the native input required by the existing posterior Dobrushin
variation/covariance machinery.  No covariance is identified with an L2
coordinate norm, no output drift is removed, and no positive Krylov depth is
given a hard support.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3GramSchmidtSeedVariationTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance p3GramSchmidtSeedVariationCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance p3GramSchmidtSeedVariationSecondCountableTopology :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance p3GramSchmidtSeedVariationMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance p3GramSchmidtSeedVariationBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance p3GramSchmidtSeedVariationSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The four seed links form an actual embedding into the spatial-slice link
carrier. -/
noncomputable def physicalYangMillsSU2PrimaryPlaquetteSeedLinkEmbedding
    (H : ℕ) :
    Fin 4 ↪ PeriodicHypercubicEvenSpatialSliceLink H where
  toFun := physicalYangMillsSU2PrimaryPlaquetteSeedLink H
  inj' := by
    intro i j hij
    apply periodicHypercubicEvenPrimarySpatialPlaquetteEdge_injective H
    have hEmbedded :=
      congrArg (periodicHypercubicEvenSpatialSliceLinkEmbedding H) hij
    simpa only [physicalYangMillsSU2PrimaryPlaquetteSeedLink_embedding] using hEmbedded

/-- The literal four-link support of the canonical primary-plaquette seed. -/
noncomputable def physicalYangMillsSU2PrimaryPlaquetteSeedLinkSet
    (H : ℕ) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Finset.univ.map (physicalYangMillsSU2PrimaryPlaquetteSeedLinkEmbedding H)

@[simp] theorem physicalYangMillsSU2PrimaryPlaquetteSeedLink_mem_seedLinkSet
    (H : ℕ)
    (k : Fin 4) :
    physicalYangMillsSU2PrimaryPlaquetteSeedLink H k ∈
      physicalYangMillsSU2PrimaryPlaquetteSeedLinkSet H := by
  classical
  simp [physicalYangMillsSU2PrimaryPlaquetteSeedLinkSet,
    physicalYangMillsSU2PrimaryPlaquetteSeedLinkEmbedding]

@[simp] theorem physicalYangMillsSU2PrimaryPlaquetteSeedLinkSet_card
    (H : ℕ) :
    (physicalYangMillsSU2PrimaryPlaquetteSeedLinkSet H).card = 4 := by
  classical
  simp [physicalYangMillsSU2PrimaryPlaquetteSeedLinkSet]

/-- The seed-link presentation from the distance package is exactly the
four-edge presentation used by the primary spatial-slice plaquette holonomy. -/
theorem physicalYangMillsSU2PrimaryPlaquetteSeedLink_eq_primarySpatialSlicePlaquetteEdge
    (H : ℕ)
    (k : Fin 4) :
    physicalYangMillsSU2PrimaryPlaquetteSeedLink H k =
      periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k := by
  apply periodicHypercubicEvenSpatialSliceLinkEmbedding_injective H
  rw [physicalYangMillsSU2PrimaryPlaquetteSeedLink_embedding]
  fin_cases k <;> rfl

/-- Agreement on the four seed links forces equality of the canonical
Gram--Schmidt seed observable. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable_eq_of_eqOn_seedLinkSet
    (H mode : ℕ)
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (hAC :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        e ∈ physicalYangMillsSU2PrimaryPlaquetteSeedLinkSet H →
          A e = C e) :
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
        H mode A =
      periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
        H mode C := by
  have hEdge :
      ∀ k : Fin 4,
        A (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k) =
          C (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k) := by
    intro k
    rw [←
      physicalYangMillsSU2PrimaryPlaquetteSeedLink_eq_primarySpatialSlicePlaquetteEdge
        H k]
    exact
      hAC
        (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k)
        (physicalYangMillsSU2PrimaryPlaquetteSeedLink_mem_seedLinkSet H k)
  change
    specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode mode
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialSlicePlaquette H)) =
      specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode mode
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy C
          (periodicHypercubicEvenPrimarySpatialSlicePlaquette H))
  rw [
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomy_eq_orientedFourEdge
      H 2 A,
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomy_eq_orientedFourEdge
      H 2 C
  ]
  unfold orientedFourEdgePlaquetteWord
  simpa only [hEdge]

/-- Posterior link-variation bound carried by exactly the four primary seed
links.  The on-support constant is the universal oscillation bound
`2 * ||O||`; off the seed it is exactly zero. -/
noncomputable def
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorLinkVariationBound
    (H mode : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
      H 2
      (fun A =>
        periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
          H mode A) := by
  classical
  let O :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
      H mode
  let S := physicalYangMillsSU2PrimaryPlaquetteSeedLinkSet H
  refine
    { variation := fun e => if e ∈ S then 2 * ‖O‖ else 0
      variation_nonneg := ?_
      variation_bound := ?_ }
  · intro e
    by_cases he : e ∈ S
    · simp [he]
    · simp [he]
  · intro e A C hAgree
    by_cases he : e ∈ S
    · simp only [he, if_true]
      rw [← Real.norm_eq_abs]
      calc
        ‖O A - O C‖ ≤ ‖O A‖ + ‖O C‖ := norm_sub_le _ _
        _ ≤ ‖O‖ + ‖O‖ :=
          add_le_add (O.norm_coe_le_norm A) (O.norm_coe_le_norm C)
        _ = 2 * ‖O‖ := by ring
    · have hEq :
          periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
              H mode A =
            periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
              H mode C := by
        apply
          periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable_eq_of_eqOn_seedLinkSet
            H mode
        intro source hSource
        exact hAgree source (by
          intro hse
          subst source
          exact he hSource)
      simp [he, hEq]

@[simp] theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorLinkVariationBound_variation
    (H mode : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorLinkVariationBound
      H mode).variation e =
      if e ∈ physicalYangMillsSU2PrimaryPlaquetteSeedLinkSet H then
        2 *
          ‖periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
            H mode‖
      else 0 := by
  rfl

/-- On every literal seed link the declared variation is the exact coarse
oscillation constant. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorLinkVariationBound_seed
    (H mode : ℕ)
    (k : Fin 4) :
    (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorLinkVariationBound
      H mode).variation
        (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k) =
      2 *
        ‖periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
          H mode‖ := by
  simp

/-- Positive distance from the four-link seed forces zero declared variation. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorLinkVariationBound_eq_zero_of_seedDistance_pos
    (H mode : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDist : 0 < physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source) :
    (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorLinkVariationBound
      H mode).variation source = 0 := by
  classical
  have hNot :
      source ∉ physicalYangMillsSU2PrimaryPlaquetteSeedLinkSet H := by
    intro hSource
    rcases Finset.mem_map.mp hSource with ⟨k, _hk, hk⟩
    have hk' :
        physicalYangMillsSU2PrimaryPlaquetteSeedLink H k = source := by
      simpa [physicalYangMillsSU2PrimaryPlaquetteSeedLinkEmbedding] using hk
    subst source
    simpa using hDist
  simp [
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorLinkVariationBound_variation,
    hNot
  ]

/-- In particular every radius-two exterior source has zero initial
Gram--Schmidt seed variation. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteFarLinks_two_GramSchmidtPosteriorLinkVariation_eq_zero
    (H mode : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hFar : source ∈ physicalYangMillsSU2PrimaryPlaquetteFarLinks H 2) :
    (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorLinkVariationBound
      H mode).variation source = 0 := by
  apply
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorLinkVariationBound_eq_zero_of_seedDistance_pos
      H mode source
  have hgt :=
    (physicalYangMillsSU2PrimaryPlaquette_mem_farLinks H 2 source).mp hFar
  omega

/-- Canonical midpoint-centered posterior variation profile of the same
four-link Gram--Schmidt seed observable. -/
noncomputable def
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
    (H mode : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile
      H 2
      (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
        H mode) :=
  (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorLinkVariationBound
    H mode).toCenteredVariationProfile

/-- At Krylov depth zero the actual mode-dependent one-slice factor is exactly
the corresponding canonical primary-plaquette Gram--Schmidt physical mode. -/
@[simp] theorem physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor_zero
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n : ℕ)
    (k : Fin 3) :
    physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 0 k =
      periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
        (halfExtent (n + 1)) k.1 := by
  simp [physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor]

/-- Hence the r=0 seed-right bounded-continuous receiver from PR #5244 is
literally built from the canonical Gram--Schmidt physical seed mode. -/
theorem physicalYangMillsSU2AdjacentFineSeedRightBCF_zero
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n : ℕ)
    (k : Fin 3) :
    GroundStatePosteriorJoint.physicalYangMillsSU2AdjacentFineSeedRightBCF
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 0 k =
      GroundStatePosteriorJoint.decomposableRightOutputBCF
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n)
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
          (halfExtent (n + 1)) k.1) := by
  simp [
    GroundStatePosteriorJoint.physicalYangMillsSU2AdjacentFineSeedRightBCF,
    physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
  ]

end

end MathlibAnalytic
end MGAP4D
