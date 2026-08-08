import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusOneSlabMixedSecondOrderRealization
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeCanonicalPerronGroundContinuity
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGroundLiftedConnectedSecondOrderCancellation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set TopologicalSpace
open scoped BigOperators InnerProduct

noncomputable section

/-- Continuous right extension of the canonically normalized Perron ground.
The `max 0 β` device lets the already-proved continuity on `Ici 0` be used by
ordinary real filter calculus while agreeing literally with the physical family
for every nonnegative coupling. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : ℝ) :
    FiniteEvenFourTorusZ2SliceHilbert H :=
  finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
    H energyIdentity energyNontrivial
    ⟨max 0 β, le_max_left (0 : ℝ) β⟩

@[simp] theorem finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_of_nonneg
    (H : ℕ)
    (energyIdentity energyNontrivial β : ℝ)
    (hβ : 0 ≤ β) :
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
        H energyIdentity energyNontrivial β =
      finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
        H energyIdentity energyNontrivial ⟨β, hβ⟩ := by
  simp [finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension,
    max_eq_right hβ]

/-- The right-extended canonical Perron ground is continuous as a finite
Euclidean vector. -/
theorem continuous_finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Continuous
      (finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
        H energyIdentity energyNontrivial) := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
  apply
    (continuous_finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
      H energyIdentity energyNontrivial hEnergy).comp
  exact Continuous.subtype_mk (continuous_const.max continuous_id) _

/-- At beta zero the canonical mass-one Perron ground is exactly the uniform
probability vector on boundary configurations. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_zero_apply
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
        H energyIdentity energyNontrivial ⟨0, by simp⟩ A =
      (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ := by
  let β0 : Set.Ici (0 : ℝ) := ⟨0, by simp⟩
  let p :=
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
      H energyIdentity energyNontrivial β0
  have hspec :=
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_spec
      H energyIdentity energyNontrivial hEnergy β0
  have hk :
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
          H energyIdentity energyNontrivial 0 =
        fun _ _ => (1 : ℝ) := by
    funext X Y
    rw [← finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_eq_couplingFamily]
    exact finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_zero
      H energyIdentity energyNontrivial X Y
  have hfix := hspec.2.2
  change
    finiteKernelNormalizedOperator
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
          H energyIdentity energyNontrivial 0) p = p at hfix
  rw [hk] at hfix
  have hA := congrArg (fun q : FiniteEvenFourTorusZ2SliceHilbert H => q A) hfix
  rw [finiteKernelNormalizedOperator_one_apply] at hA
  have hsum : ∑ X : FiniteEvenFourTorusZ2SliceConfiguration H, p X = 1 := hspec.1
  rw [hsum, mul_one] at hA
  simpa [β0, p] using hA.symm

@[simp] theorem finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_zero_apply
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
        H energyIdentity energyNontrivial 0 A =
      (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_of_nonneg
    H energyIdentity energyNontrivial 0 (le_refl 0)]
  exact
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_zero_apply
      H energyIdentity energyNontrivial hEnergy A

/-- Every coordinate of the right-extended canonical ground converges to the
uniform beta-zero mass. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_tendsto_apply_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Tendsto
      (fun β : ℝ =>
        finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
          H energyIdentity energyNontrivial β A)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds
        (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹) := by
  let toPi :=
    PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : FiniteEvenFourTorusZ2SliceConfiguration H => ℝ)
  have hVec :=
    continuous_finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
      H energyIdentity energyNontrivial hEnergy
  have hPlain :
      Continuous (fun β : ℝ =>
        toPi
          (finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
            H energyIdentity energyNontrivial β)) :=
    toPi.continuous.comp hVec
  have hCoord :
      Continuous (fun β : ℝ =>
        finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
          H energyIdentity energyNontrivial β A) := by
    simpa [toPi] using (continuous_apply A).comp hPlain
  have hWithin := hCoord.continuousAt.continuousWithinAt.tendsto
  simpa only [finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_zero_apply
    H energyIdentity energyNontrivial hEnergy A] using hWithin

/-- The right-coordinate kernel difference has an explicit first-order slope.
All left-boundary and temporal-crossing terms cancel; only the right spatial
Wilson action difference remains. -/
theorem finiteEvenFourTorusZ2OneSlabCouplingFamily_rightDifference_quadraticSlope
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Tendsto
      (fun β : ℝ =>
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
            H energyIdentity energyNontrivial β A y -
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
            H energyIdentity energyNontrivial β A y') / β)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds
        (-((1 / 2 : ℝ) *
          (finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial y -
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial y')))) := by
  have hd0 :=
    ((finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_hasDerivAt_named
        H energyIdentity energyNontrivial 0 A y).sub
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_hasDerivAt_named
        H energyIdentity energyNontrivial 0 A y')).tendsto_slope_zero_right
  have hd :
      Tendsto
        (fun β : ℝ =>
          (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
              H energyIdentity energyNontrivial β A y -
            finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
              H energyIdentity energyNontrivial β A y') / β)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds
          (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile
              H energyIdentity energyNontrivial 0 A y -
            finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile
              H energyIdentity energyNontrivial 0 A y')) := by
    simpa [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_zero,
      div_eq_mul_inv, mul_comm] using hd0
  have htarget :
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile
          H energyIdentity energyNontrivial 0 A y -
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile
          H energyIdentity energyNontrivial 0 A y' =
      -((1 / 2 : ℝ) *
        (finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial y -
          finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial y')) := by
    rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile_zero,
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile_zero,
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_eq_additive,
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_eq_additive]
    ring
  rw [htarget] at hd
  simpa only [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_eq_couplingFamily]
    using hd

/-- Exact coordinate-difference form of the Perron fixed-vector equation.
The common output-independent normalization derivative never appears: the
actual normalization scalar multiplies a kernel difference directly. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_coordinateDifference_fixed
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (β : ℝ)
    (hβ : 0 ≤ β)
    (y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
          H energyIdentity energyNontrivial ⟨β, hβ⟩ y -
        finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
          H energyIdentity energyNontrivial ⟨β, hβ⟩ y' =
      finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
          H energyIdentity energyNontrivial β *
        ∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
          (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
              H energyIdentity energyNontrivial β A y -
            finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
              H energyIdentity energyNontrivial β A y') *
            finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
              H energyIdentity energyNontrivial ⟨β, hβ⟩ A := by
  let p :=
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
      H energyIdentity energyNontrivial ⟨β, hβ⟩
  have hfix :=
    (finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_spec
      H energyIdentity energyNontrivial hEnergy ⟨β, hβ⟩).2.2
  have hy := congrArg (fun q : FiniteEvenFourTorusZ2SliceHilbert H => q y) hfix
  have hy' := congrArg (fun q : FiniteEvenFourTorusZ2SliceHilbert H => q y') hfix
  change
    finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
        H energyIdentity energyNontrivial β *
      (∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
          H energyIdentity energyNontrivial β A y * p A) = p y at hy
  change
    finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
        H energyIdentity energyNontrivial β *
      (∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
          H energyIdentity energyNontrivial β A y' * p A) = p y' at hy'
  change
    p y - p y' =
      finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
          H energyIdentity energyNontrivial β *
        ∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
          (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
              H energyIdentity energyNontrivial β A y -
            finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
              H energyIdentity energyNontrivial β A y') * p A
  rw [← hy, ← hy']
  rw [← Finset.mul_sum]
  apply congrArg
    (fun z : ℝ =>
      finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
        H energyIdentity energyNontrivial β * z)
  rw [Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- The actual canonical Perron ground has an explicit right first-order
coordinate-difference slope at beta zero.  It is obtained solely from the
fixed-vector equation, mass-one normalization, kernel first variation, and
continuity of the ground and operator-norm normalization. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_coordinateDifference_slope
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Tendsto
      (fun β : ℝ =>
        (finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
            H energyIdentity energyNontrivial β y -
          finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
            H energyIdentity energyNontrivial β y') / β)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds
        (-((Fintype.card
            (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
          (1 / 2 : ℝ) *
          (finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial y -
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial y')))) := by
  classical
  let C := FiniteEvenFourTorusZ2SliceConfiguration H
  let n : ℝ := Fintype.card C
  have hn : n ≠ 0 := by
    dsimp [n, C]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card C ≠ 0)
  let slope : ℝ :=
    -((1 / 2 : ℝ) *
      (finiteEvenFourTorusZ2SpatialWilsonAction
          H energyIdentity energyNontrivial y -
        finiteEvenFourTorusZ2SpatialWilsonAction
          H energyIdentity energyNontrivial y'))
  have hNorm :
      Tendsto
        (finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
          H energyIdentity energyNontrivial)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds n⁻¹) := by
    have ht :=
      (continuous_finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
        H energyIdentity energyNontrivial).continuousAt.tendsto
    have ht' := ht.mono_left inf_le_left
    simpa [n, C, finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization_zero]
      using ht'
  have hTerm : ∀ A : C,
      Tendsto
        (fun β : ℝ =>
          ((finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
                H energyIdentity energyNontrivial β A y -
              finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
                H energyIdentity energyNontrivial β A y') / β) *
            finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
              H energyIdentity energyNontrivial β A)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (slope * n⁻¹)) := by
    intro A
    have hk :=
      finiteEvenFourTorusZ2OneSlabCouplingFamily_rightDifference_quadraticSlope
        H energyIdentity energyNontrivial A y y'
    have hp :=
      finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_tendsto_apply_zero
        H energyIdentity energyNontrivial hEnergy A
    simpa [slope, n, C] using hk.mul hp
  have hSum0 :=
    tendsto_finsetSum (Finset.univ : Finset C) (fun A _hA => hTerm A)
  have hSum :
      Tendsto
        (fun β : ℝ =>
          ∑ A : C,
            ((finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
                  H energyIdentity energyNontrivial β A y -
                finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
                  H energyIdentity energyNontrivial β A y') / β) *
              finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
                H energyIdentity energyNontrivial β A)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (∑ _A : C, slope * n⁻¹)) := by
    simpa using hSum0
  have hsumLimit : (∑ _A : C, slope * n⁻¹) = slope := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change n * (slope * n⁻¹) = slope
    field_simp [hn]
  rw [hsumLimit] at hSum
  have hRhs := hNorm.mul hSum
  have hEq :
      (fun β : ℝ =>
        (finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
            H energyIdentity energyNontrivial β y -
          finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
            H energyIdentity energyNontrivial β y') / β) =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun β : ℝ =>
        finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
            H energyIdentity energyNontrivial β *
          ∑ A : C,
            ((finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
                  H energyIdentity energyNontrivial β A y -
                finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
                  H energyIdentity energyNontrivial β A y') / β) *
              finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
                H energyIdentity energyNontrivial β A) := by
    filter_upwards [self_mem_nhdsWithin] with β hβ
    have hβpos : 0 < β := hβ
    have hβne : β ≠ 0 := ne_of_gt hβpos
    have hfixed :=
      finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_coordinateDifference_fixed
        H energyIdentity energyNontrivial hEnergy β (le_of_lt hβpos) y y'
    rw [finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_of_nonneg
      H energyIdentity energyNontrivial β (le_of_lt hβpos)]
    rw [hfixed]
    rw [div_eq_mul_inv, mul_assoc, Finset.sum_mul]
    apply congrArg
      (fun z : ℝ =>
        finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
          H energyIdentity energyNontrivial β * z)
    apply Finset.sum_congr rfl
    intro A _hA
    rw [div_eq_mul_inv]
    ring
  have hFinal := hRhs.congr' hEq.symm
  simpa [slope, n, C] using hFinal

end

end MathlibAnalytic
end MGAP4D
