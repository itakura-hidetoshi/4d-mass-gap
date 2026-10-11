import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonOneLinkIntegratedParallelogram
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwelveColorQuadraticHomogeneity
import Mathlib.Tactic

/-!
# P4-Q2-BN: actual Wilson right/left twelve-color Haar reference parallelogram

BM proved the exact integrated ORIGINAL Wilson mass-weighted one-link Haar
parallelogram for bounded strongly measurable concrete joint observables.
Here that statement is summed over every REAL spatial link of every color,
then transported to the genuine left boundary by the already-established
physical joint endpoint swap. Every true link-color cardinality is retained.

The finite twelve-color sum and its normalized 1/12 original Wilson version
therefore obey the parallelogram identity in ENNReal. The pre-existing
finite-energy theorem converts the unnormalized original Wilson twelve-color
reference into a real quadratic form on the bounded concrete joint core.

This DOES NOT identify the original reference with the physical E12 form,
assert a reverse original-reference Poincare inequality, or automatically
descend the original reference to the full joint L² quotient.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1600000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

/-- Preserve the parallelogram law under a nonnegative ENNReal weight,
without any assumption of cancellation at infinity. -/
theorem p4Q2BN_weight_parallelogram
    (w xPlus xMinus xF xG : ENNReal)
    (h : xPlus + xMinus = (2 : ENNReal) * (xF + xG)) :
    w * xPlus + w * xMinus =
      (2 : ENNReal) * (w * xF + w * xG) := by
  calc
    w * xPlus + w * xMinus = w * (xPlus + xMinus) :=
      (mul_add w xPlus xMinus).symm
    _ = w * ((2 : ENNReal) * (xF + xG)) := by rw [h]
    _ = (2 : ENNReal) * (w * (xF + xG)) := by ac_rfl
    _ = (2 : ENNReal) * (w * xF + w * xG) := by
      rw [mul_add]

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "C12" =>
  PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor

/-- Right original Wilson all-link reference, with each actual link in the
given physical spatial-color class and no product-independence premise. -/
theorem p4Q2BN_originalRightColorAllLinkReference_parallelogram
    (c : Fin 6) (F G : Joint → ℝ)
    (hF : StronglyMeasurable F) (hG : StronglyMeasurable G)
    (boundF : ℝ) (hboundF : ∀ z, ‖F z‖ ≤ boundF)
    (boundG : ℝ) (hboundG : ∀ z, ‖G z‖ ≤ boundG) :
    p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c
        (fun z => F z + G z) +
      p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c
        (fun z => F z - G z) =
      (2 : ENNReal) *
        (p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c F +
          p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c G) := by
  classical
  let A : p4Q2BA_ColorLinks H c → ENNReal := fun e =>
    p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta e.1
      (fun z => F z + G z)
  let D : p4Q2BA_ColorLinks H c → ENNReal := fun e =>
    p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta e.1
      (fun z => F z - G z)
  let X : p4Q2BA_ColorLinks H c → ENNReal := fun e =>
    p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta e.1 F
  let Y : p4Q2BA_ColorLinks H c → ENNReal := fun e =>
    p4Q2AZ_originalJointHaarReferenceEnergy H N hN beta hbeta e.1 G
  change (∑ e, A e) + (∑ e, D e) =
    (2 : ENNReal) * ((∑ e, X e) + (∑ e, Y e))
  calc
    (∑ e, A e) + (∑ e, D e) = ∑ e, (A e + D e) :=
      (Finset.sum_add_distrib).symm
    _ = ∑ e, (2 : ENNReal) * (X e + Y e) := by
      apply Finset.sum_congr rfl
      intro e _he
      dsimp [A, D, X, Y]
      exact
        p4Q2BM_originalJointOneLinkHaarReference_parallelogram
          H N hN beta hbeta e.1 F G hF hG boundF hboundF boundG hboundG
    _ = (2 : ENNReal) * (∑ e, (X e + Y e)) := by
      rw [Finset.mul_sum]
    _ = (2 : ENNReal) * ((∑ e, X e) + (∑ e, Y e)) := by
      rw [Finset.sum_add_distrib]

/-- Genuine original Wilson left-link color reference obtained from the
right-side theorem by the EXISTING physical endpoint swap of the input. -/
theorem p4Q2BN_originalLeftColorAllLinkReference_parallelogram
    (c : Fin 6) (F G : Joint → ℝ)
    (hF : StronglyMeasurable F) (hG : StronglyMeasurable G)
    (boundF : ℝ) (hboundF : ∀ z, ‖F z‖ ≤ boundF)
    (boundG : ℝ) (hboundG : ∀ z, ‖G z‖ ≤ boundG) :
    p4Q2BB_leftColorAllLinkHaarReferenceSum H N hN beta hbeta c
        (fun z => F z + G z) +
      p4Q2BB_leftColorAllLinkHaarReferenceSum H N hN beta hbeta c
        (fun z => F z - G z) =
      (2 : ENNReal) *
        (p4Q2BB_leftColorAllLinkHaarReferenceSum H N hN beta hbeta c F +
          p4Q2BB_leftColorAllLinkHaarReferenceSum H N hN beta hbeta c G) := by
  change
    p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c
        (p4Q2BB_swapConcrete H N (fun z => F z + G z)) +
      p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c
        (p4Q2BB_swapConcrete H N (fun z => F z - G z)) =
      (2 : ENNReal) *
        (p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c
            (p4Q2BB_swapConcrete H N F) +
          p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta c
            (p4Q2BB_swapConcrete H N G))
  have hPlus :
      p4Q2BB_swapConcrete H N (fun z => F z + G z) =
        (fun z => p4Q2BB_swapConcrete H N F z +
          p4Q2BB_swapConcrete H N G z) := by
    rfl
  have hMinus :
      p4Q2BB_swapConcrete H N (fun z => F z - G z) =
        (fun z => p4Q2BB_swapConcrete H N F z -
          p4Q2BB_swapConcrete H N G z) := by
    rfl
  rw [hPlus, hMinus]
  exact p4Q2BN_originalRightColorAllLinkReference_parallelogram
    H N hN beta hbeta c
    (p4Q2BB_swapConcrete H N F) (p4Q2BB_swapConcrete H N G)
    (p4Q2BB_swapConcrete_stronglyMeasurable H N F hF)
    (p4Q2BB_swapConcrete_stronglyMeasurable H N G hG)
    boundF (p4Q2BB_swapConcrete_norm_le H N F boundF hboundF)
    boundG (p4Q2BB_swapConcrete_norm_le H N G boundG hboundG)

/-- Every normalized genuine right/left color Haar average inherits
the full, unmodified original Wilson parallelogram law. -/
theorem p4Q2BN_twelveColorOriginalHaarReferenceAverage_parallelogram
    (c : C12) (F G : Joint → ℝ)
    (hF : StronglyMeasurable F) (hG : StronglyMeasurable G)
    (boundF : ℝ) (hboundF : ∀ z, ‖F z‖ ≤ boundF)
    (boundG : ℝ) (hboundG : ∀ z, ‖G z‖ ≤ boundG) :
    p4Q2BB_twelveColorOriginalHaarReferenceAverage
        H N hN beta hbeta c (fun z => F z + G z) +
      p4Q2BB_twelveColorOriginalHaarReferenceAverage
        H N hN beta hbeta c (fun z => F z - G z) =
      (2 : ENNReal) *
        (p4Q2BB_twelveColorOriginalHaarReferenceAverage
            H N hN beta hbeta c F +
          p4Q2BB_twelveColorOriginalHaarReferenceAverage
            H N hN beta hbeta c G) := by
  cases c with
  | inl k =>
      change
        ((Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
            p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta k
              (fun z => F z + G z)) +
          ((Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
            p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta k
              (fun z => F z - G z)) =
        (2 : ENNReal) *
          (((Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
              p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta k F) +
            ((Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
              p4Q2BA_colorAllLinkHaarReferenceSum H N hN beta hbeta k G))
      exact p4Q2BN_weight_parallelogram _ _ _ _ _
        (p4Q2BN_originalRightColorAllLinkReference_parallelogram
          H N hN beta hbeta k F G hF hG boundF hboundF boundG hboundG)
  | inr k =>
      change
        ((Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
            p4Q2BB_leftColorAllLinkHaarReferenceSum H N hN beta hbeta k
              (fun z => F z + G z)) +
          ((Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
            p4Q2BB_leftColorAllLinkHaarReferenceSum H N hN beta hbeta k
              (fun z => F z - G z)) =
        (2 : ENNReal) *
          (((Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
              p4Q2BB_leftColorAllLinkHaarReferenceSum H N hN beta hbeta k F) +
            ((Fintype.card (p4Q2BA_ColorLinks H k) : ENNReal)⁻¹ *
              p4Q2BB_leftColorAllLinkHaarReferenceSum H N hN beta hbeta k G))
      exact p4Q2BN_weight_parallelogram _ _ _ _ _
        (p4Q2BN_originalLeftColorAllLinkReference_parallelogram
          H N hN beta hbeta k F G hF hG boundF hboundF boundG hboundG)

/-- The exact original Wilson unnormalized twelve-color Haar reference sum
satisfies parallelogram in ENNReal for bounded concrete observables. -/
theorem p4Q2BN_originalTwelveColorReferenceSum_parallelogram
    (F G : Joint → ℝ)
    (hF : StronglyMeasurable F) (hG : StronglyMeasurable G)
    (boundF : ℝ) (hboundF : ∀ z, ‖F z‖ ≤ boundF)
    (boundG : ℝ) (hboundG : ∀ z, ‖G z‖ ≤ boundG) :
    (∑ c : C12, p4Q2BB_twelveColorOriginalHaarReferenceAverage
        H N hN beta hbeta c (fun z => F z + G z)) +
      (∑ c : C12, p4Q2BB_twelveColorOriginalHaarReferenceAverage
        H N hN beta hbeta c (fun z => F z - G z)) =
      (2 : ENNReal) *
        ((∑ c : C12, p4Q2BB_twelveColorOriginalHaarReferenceAverage
            H N hN beta hbeta c F) +
          (∑ c : C12, p4Q2BB_twelveColorOriginalHaarReferenceAverage
            H N hN beta hbeta c G)) := by
  classical
  let A : C12 → ENNReal := fun c =>
    p4Q2BB_twelveColorOriginalHaarReferenceAverage
      H N hN beta hbeta c (fun z => F z + G z)
  let D : C12 → ENNReal := fun c =>
    p4Q2BB_twelveColorOriginalHaarReferenceAverage
      H N hN beta hbeta c (fun z => F z - G z)
  let X : C12 → ENNReal := fun c =>
    p4Q2BB_twelveColorOriginalHaarReferenceAverage H N hN beta hbeta c F
  let Y : C12 → ENNReal := fun c =>
    p4Q2BB_twelveColorOriginalHaarReferenceAverage H N hN beta hbeta c G
  change (∑ c, A c) + (∑ c, D c) =
    (2 : ENNReal) * ((∑ c, X c) + (∑ c, Y c))
  calc
    (∑ c, A c) + (∑ c, D c) = ∑ c, (A c + D c) :=
      (Finset.sum_add_distrib).symm
    _ = ∑ c, (2 : ENNReal) * (X c + Y c) := by
      apply Finset.sum_congr rfl
      intro c _hc
      dsimp [A, D, X, Y]
      exact p4Q2BN_twelveColorOriginalHaarReferenceAverage_parallelogram
        H N hN beta hbeta c F G hF hG boundF hboundF boundG hboundG
    _ = (2 : ENNReal) * (∑ c, (X c + Y c)) := by
      rw [Finset.mul_sum]
    _ = (2 : ENNReal) * ((∑ c, X c) + (∑ c, Y c)) := by
      rw [Finset.sum_add_distrib]

/-- The physical original 1/12 twelve-color reference obeys the same
parallelogram without changing the original Wilson mass weighting. -/
theorem p4Q2BN_originalPhysicalTwelveColorHaarReference_parallelogram
    (F G : Joint → ℝ)
    (hF : StronglyMeasurable F) (hG : StronglyMeasurable G)
    (boundF : ℝ) (hboundF : ∀ z, ‖F z‖ ≤ boundF)
    (boundG : ℝ) (hboundG : ∀ z, ‖G z‖ ≤ boundG) :
    p4Q2BC_originalPhysicalTwelveColorHaarReference
        H N hN beta hbeta (fun z => F z + G z) +
      p4Q2BC_originalPhysicalTwelveColorHaarReference
        H N hN beta hbeta (fun z => F z - G z) =
      (2 : ENNReal) *
        (p4Q2BC_originalPhysicalTwelveColorHaarReference
            H N hN beta hbeta F +
          p4Q2BC_originalPhysicalTwelveColorHaarReference
            H N hN beta hbeta G) := by
  unfold p4Q2BC_originalPhysicalTwelveColorHaarReference
  exact p4Q2BN_weight_parallelogram _ _ _ _ _
    (p4Q2BN_originalTwelveColorReferenceSum_parallelogram
      H N hN beta hbeta F G hF hG boundF hboundF boundG hboundG)

/-- Concrete bounded physical joint observables obey the REAL twelve-color
original Wilson reference parallelogram, by exact finite ENNReal sums. -/
theorem p4Q2BN_originalWilsonTwelveColorHaarReferenceReal_parallelogram
    (F G : Joint → ℝ)
    (hF : StronglyMeasurable F) (hG : StronglyMeasurable G)
    (boundF : ℝ) (hboundF : ∀ z, ‖F z‖ ≤ boundF)
    (boundG : ℝ) (hboundG : ∀ z, ‖G z‖ ≤ boundG) :
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal H N hN beta hbeta
        (fun z => F z + G z) +
      p4Q2BD_originalWilsonTwelveColorHaarReferenceReal H N hN beta hbeta
        (fun z => F z - G z) =
      (2 : ℝ) *
        (p4Q2BD_originalWilsonTwelveColorHaarReferenceReal H N hN beta hbeta F +
          p4Q2BD_originalWilsonTwelveColorHaarReferenceReal H N hN beta hbeta G) := by
  let E : (Joint → ℝ) → ENNReal := fun K =>
    ∑ c : C12, p4Q2BB_twelveColorOriginalHaarReferenceAverage
      H N hN beta hbeta c K
  have hboundPlus : ∀ z, ‖F z + G z‖ ≤ boundF + boundG := by
    intro z
    exact (norm_add_le (F z) (G z)).trans
      (add_le_add (hboundF z) (hboundG z))
  have hboundMinus : ∀ z, ‖F z - G z‖ ≤ boundF + boundG := by
    intro z
    exact (norm_sub_le (F z) (G z)).trans
      (add_le_add (hboundF z) (hboundG z))
  have hPlus : E (fun z => F z + G z) ≠ ∞ :=
    p4Q2BD_originalWilsonTwelveColorHaarReference_ne_top
      H N hN beta hbeta (fun z => F z + G z)
        (hF.add hG) (boundF + boundG) hboundPlus
  have hMinus : E (fun z => F z - G z) ≠ ∞ :=
    p4Q2BD_originalWilsonTwelveColorHaarReference_ne_top
      H N hN beta hbeta (fun z => F z - G z)
        (hF.sub hG) (boundF + boundG) hboundMinus
  have hFiniteF : E F ≠ ∞ :=
    p4Q2BD_originalWilsonTwelveColorHaarReference_ne_top
      H N hN beta hbeta F hF boundF hboundF
  have hFiniteG : E G ≠ ∞ :=
    p4Q2BD_originalWilsonTwelveColorHaarReference_ne_top
      H N hN beta hbeta G hG boundG hboundG
  have hENN :
      E (fun z => F z + G z) + E (fun z => F z - G z) =
        (2 : ENNReal) * (E F + E G) :=
    p4Q2BN_originalTwelveColorReferenceSum_parallelogram
      H N hN beta hbeta F G hF hG boundF hboundF boundG hboundG
  have hReal := congrArg ENNReal.toReal hENN
  rw [ENNReal.toReal_add hPlus hMinus,
    ENNReal.toReal_mul, ENNReal.toReal_add hFiniteF hFiniteG] at hReal
  change (E (fun z => F z + G z)).toReal +
      (E (fun z => F z - G z)).toReal =
      (2 : ℝ) * ((E F).toReal + (E G).toReal)
  simpa only [ENNReal.toReal_ofNat] using hReal

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
