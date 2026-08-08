import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusOneSlabMixedSecondOrderRealization
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeCanonicalPerronGroundContinuity
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorZeroCouplingSeed
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGroundLiftedConnectedSecondOrderCancellation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set TopologicalSpace
open scoped BigOperators

noncomputable section

/-- At beta zero the canonically mass-one Perron ground is constant on the
complete finite boundary carrier. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_zero_apply_eq
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
        H energyIdentity energyNontrivial ⟨0, le_refl 0⟩ A =
      finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
        H energyIdentity energyNontrivial ⟨0, le_refl 0⟩ B := by
  obtain ⟨c, _hcPos, hc⟩ :=
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_eq_pos_smul_chosenGround
      H energyIdentity energyNontrivial hEnergy ⟨0, le_refl 0⟩
  have hA := congrArg
    (fun p : FiniteEvenFourTorusZ2SliceHilbert H => p A) hc
  have hB := congrArg
    (fun p : FiniteEvenFourTorusZ2SliceHilbert H => p B) hc
  have hChosen :=
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_zero_apply_eq
      H energyIdentity energyNontrivial hEnergy A B
  calc
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
        H energyIdentity energyNontrivial ⟨0, le_refl 0⟩ A =
        c * finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H 0 energyIdentity energyNontrivial (by norm_num) hEnergy A := by
      simpa using hA
    _ = c * finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H 0 energyIdentity energyNontrivial (by norm_num) hEnergy B := by
      rw [hChosen]
    _ = finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
        H energyIdentity energyNontrivial ⟨0, le_refl 0⟩ B := by
      simpa using hB.symm

/-- Exact beta-zero canonical Perron ground.  Its mass-one normalization turns
the constant fixed ray into the uniform boundary vector. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_zero_apply
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
        H energyIdentity energyNontrivial ⟨0, le_refl 0⟩ A =
      (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ := by
  let p0 :=
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
      H energyIdentity energyNontrivial ⟨0, le_refl 0⟩
  let n : ℝ := Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H)
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) ≠ 0)
  have hsum : (∑ B : FiniteEvenFourTorusZ2SliceConfiguration H, p0 B) = 1 := by
    simpa [p0] using
      (finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_spec
        H energyIdentity energyNontrivial hEnergy ⟨0, le_refl 0⟩).1
  have hconst :
      ∀ B : FiniteEvenFourTorusZ2SliceConfiguration H, p0 B = p0 A := by
    intro B
    simpa [p0] using
      finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_zero_apply_eq
        H energyIdentity energyNontrivial hEnergy B A
  have hsumConst :
      (∑ B : FiniteEvenFourTorusZ2SliceConfiguration H, p0 B) = n * p0 A := by
    simp_rw [hconst]
    simp [n]
  have hprod : n * p0 A = 1 := by
    rw [← hsumConst]
    exact hsum
  have hInvMul : n⁻¹ * n = 1 := inv_mul_cancel₀ hn
  calc
    p0 A = 1 * p0 A := by ring
    _ = (n⁻¹ * n) * p0 A := by rw [hInvMul]
    _ = n⁻¹ * (n * p0 A) := by ring
    _ = n⁻¹ := by rw [hprod, mul_one]
    _ = (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ := rfl

/-- Continuous all-real extension of the physical canonical Perron ground,
obtained by clamping the coupling to the nonnegative half-line.  Only its
positive-side germ is used below. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : ℝ) : FiniteEvenFourTorusZ2SliceHilbert H :=
  finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
    H energyIdentity energyNontrivial
    ⟨max β 0, le_max_right β 0⟩

@[simp] theorem finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) :
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
        H energyIdentity energyNontrivial 0 =
      finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
        H energyIdentity energyNontrivial ⟨0, le_refl 0⟩ := by
  rfl

/-- On strictly positive coupling the clamped extension is literally the
physical canonical Perron ground. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_of_pos
    (H : ℕ)
    (energyIdentity energyNontrivial β : ℝ)
    (hβ : 0 < β) :
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
        H energyIdentity energyNontrivial β =
      finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
        H energyIdentity energyNontrivial ⟨β, le_of_lt hβ⟩ := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
  congr 1
  apply Subtype.ext
  simp [max_eq_left (le_of_lt hβ)]

/-- The all-real right extension is continuous. -/
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
  exact Continuous.subtype_mk (continuous_id.max continuous_const) _

/-- Difference between two output columns of the proof-independent raw coupling
family, at one fixed input configuration. -/
noncomputable def finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (x y y' : FiniteEvenFourTorusZ2SliceConfiguration H)
    (β : ℝ) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
      H energyIdentity energyNontrivial β x y -
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
      H energyIdentity energyNontrivial β x y'

@[simp] theorem finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (x y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference
      H energyIdentity energyNontrivial x y y' 0 = 0 := by
  unfold finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference
  rw [← finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_eq_couplingFamily,
    ← finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_eq_couplingFamily]
  simp

/-- Exact derivative at beta zero of one raw column difference. -/
theorem finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference_hasDerivAt_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (x y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    HasDerivAt
      (finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference
        H energyIdentity energyNontrivial x y y')
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
          H energyIdentity energyNontrivial x y -
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
          H energyIdentity energyNontrivial x y')
      0 := by
  have h :=
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_hasDerivAt_named
      H energyIdentity energyNontrivial 0 x y).sub
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_hasDerivAt_named
        H energyIdentity energyNontrivial 0 x y')
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile_zero,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile_zero] at h
  convert h using 1
  funext β
  unfold finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference
  rw [← finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_eq_couplingFamily,
    ← finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_eq_couplingFamily]

/-- The raw column-difference first variation is independent of the input
configuration and is exactly the output spatial-action difference. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_columnDifference_eq
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (x y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
          H energyIdentity energyNontrivial x y -
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
          H energyIdentity energyNontrivial x y' =
      -(1 / 2 : ℝ) *
        (finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial y -
          finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial y') := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_eq_additive,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_eq_additive]
  ring

/-- Positive-side first slope of one raw output-column difference. -/
theorem finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference_div_tendsto
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (x y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Tendsto
      (fun β : ℝ =>
        finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference
          H energyIdentity energyNontrivial x y y' β / β)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds
        (-(1 / 2 : ℝ) *
          (finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial y -
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial y'))) := by
  have h :=
    (finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference_hasDerivAt_zero
      H energyIdentity energyNontrivial x y y').tendsto_slope_zero_right
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_columnDifference_eq]
  simpa using h

/-- Coordinate-difference form of the canonical Perron fixed equation.  The
operator-norm normalization appears only through its scalar value. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_coordinate_sub_eq
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (β : Set.Ici (0 : ℝ))
    (y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
          H energyIdentity energyNontrivial β y -
        finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
          H energyIdentity energyNontrivial β y' =
      finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
          H energyIdentity energyNontrivial β.1 *
        ∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
          (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
                H energyIdentity energyNontrivial β.1 x y -
            finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
                H energyIdentity energyNontrivial β.1 x y') *
            finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
              H energyIdentity energyNontrivial β x := by
  let p :=
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround
      H energyIdentity energyNontrivial β
  let K :=
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
      H energyIdentity energyNontrivial β.1
  let ν :=
    finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
      H energyIdentity energyNontrivial β.1
  have hfix :=
    (finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_spec
      H energyIdentity energyNontrivial hEnergy β).2.2
  have hy := congrArg (fun q : FiniteEvenFourTorusZ2SliceHilbert H => q y) hfix
  have hy' := congrArg (fun q : FiniteEvenFourTorusZ2SliceHilbert H => q y') hfix
  change ν * (∑ x : FiniteEvenFourTorusZ2SliceConfiguration H, K x y * p x) = p y at hy
  change ν * (∑ x : FiniteEvenFourTorusZ2SliceConfiguration H, K x y' * p x) = p y' at hy'
  change p y - p y' =
    ν * ∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
      (K x y - K x y') * p x
  calc
    p y - p y' =
        ν * (∑ x : FiniteEvenFourTorusZ2SliceConfiguration H, K x y * p x) -
          ν * (∑ x : FiniteEvenFourTorusZ2SliceConfiguration H, K x y' * p x) := by
      rw [hy, hy']
    _ = ν *
        ((∑ x : FiniteEvenFourTorusZ2SliceConfiguration H, K x y * p x) -
          ∑ x : FiniteEvenFourTorusZ2SliceConfiguration H, K x y' * p x) := by
      ring
    _ = ν * ∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
        (K x y - K x y') * p x := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro x _hx
      ring

/-- The first complement slope of the actual canonical Perron ground follows
directly from the fixed-vector equation.  No derivative of the operator norm,
Perron eigenvalue, eigenbasis, or spectral projector is used. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_coordinateDifference_div_tendsto
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
        ((Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
          (-(1 / 2 : ℝ) *
            (finiteEvenFourTorusZ2SpatialWilsonAction
                H energyIdentity energyNontrivial y -
              finiteEvenFourTorusZ2SpatialWilsonAction
                H energyIdentity energyNontrivial y')))) := by
  let α := FiniteEvenFourTorusZ2SliceConfiguration H
  let n : ℝ := Fintype.card α
  let d : ℝ :=
    -(1 / 2 : ℝ) *
      (finiteEvenFourTorusZ2SpatialWilsonAction
          H energyIdentity energyNontrivial y -
        finiteEvenFourTorusZ2SpatialWilsonAction
          H energyIdentity energyNontrivial y')
  let p :=
    finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
      H energyIdentity energyNontrivial
  let ν :=
    finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
      H energyIdentity energyNontrivial
  have hn : n ≠ 0 := by
    dsimp [n, α]
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) ≠ 0)
  have hν :
      Tendsto ν (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds n⁻¹) := by
    have h :=
      (continuous_finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
        H energyIdentity energyNontrivial).continuousAt.tendsto
    rw [finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization_zero] at h
    simpa [ν, n, α] using h.mono_left inf_le_left
  have hp : ∀ x : FiniteEvenFourTorusZ2SliceConfiguration H,
      Tendsto (fun β : ℝ => p β x)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds n⁻¹) := by
    intro x
    have h :=
      ((continuous_apply x).comp
        (continuous_finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension
          H energyIdentity energyNontrivial hEnergy)).continuousAt.tendsto
    have hp0 :=
      finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_zero_apply
        H energyIdentity energyNontrivial hEnergy x
    rw [finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_zero,
      hp0] at h
    simpa [p, n, α] using h.mono_left inf_le_left
  have hK : ∀ x : FiniteEvenFourTorusZ2SliceConfiguration H,
      Tendsto
        (fun β : ℝ =>
          finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference
            H energyIdentity energyNontrivial x y y' β / β)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds d) := by
    intro x
    simpa [d] using
      finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference_div_tendsto
        H energyIdentity energyNontrivial x y y'
  have hTerm : ∀ x : FiniteEvenFourTorusZ2SliceConfiguration H,
      Tendsto
        (fun β : ℝ =>
          (finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference
              H energyIdentity energyNontrivial x y y' β / β) * p β x)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (d * n⁻¹)) := by
    intro x
    exact (hK x).mul (hp x)
  have hSumRaw :
      Tendsto
        (fun β : ℝ =>
          ∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
            (finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference
                H energyIdentity energyNontrivial x y y' β / β) * p β x)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds
          (∑ _x : FiniteEvenFourTorusZ2SliceConfiguration H, d * n⁻¹)) := by
    simpa using
      tendsto_finsetSum (Finset.univ :
        Finset (FiniteEvenFourTorusZ2SliceConfiguration H))
        (fun x _hx => hTerm x)
  have hsumLimit :
      (∑ _x : FiniteEvenFourTorusZ2SliceConfiguration H, d * n⁻¹) = d := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change n * (d * n⁻¹) = d
    field_simp [hn]
  have hSum :
      Tendsto
        (fun β : ℝ =>
          ∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
            (finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference
                H energyIdentity energyNontrivial x y y' β / β) * p β x)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds d) := by
    rw [← hsumLimit]
    exact hSumRaw
  have hRhs :
      Tendsto
        (fun β : ℝ =>
          ν β *
            ∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
              (finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference
                  H energyIdentity energyNontrivial x y y' β / β) * p β x)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (n⁻¹ * d)) :=
    hν.mul hSum
  have hEq :
      (fun β : ℝ =>
        (p β y - p β y') / β) =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun β : ℝ =>
        ν β *
          ∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
            (finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference
                H energyIdentity energyNontrivial x y y' β / β) * p β x) := by
    filter_upwards [self_mem_nhdsWithin] with β hβ
    have hβpos : 0 < β := hβ
    have hFixed :=
      finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGround_coordinate_sub_eq
        H energyIdentity energyNontrivial hEnergy ⟨β, le_of_lt hβpos⟩ y y'
    have hpβ :=
      finiteEvenFourTorusZ2UnfixedGaugeCanonicalPerronGroundRightExtension_of_pos
        H energyIdentity energyNontrivial β hβpos
    change
      p β y - p β y' =
        ν β * ∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
          finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference
              H energyIdentity energyNontrivial x y y' β * p β x at hFixed
    simpa [p, ν, finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference,
      hpβ] using hFixed
    rw [hFixed]
    calc
      (ν β *
          ∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
            finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference
                H energyIdentity energyNontrivial x y y' β * p β x) / β =
          ν β *
            ((∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
              finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference
                  H energyIdentity energyNontrivial x y y' β * p β x) * β⁻¹) := by
        rw [div_eq_mul_inv]
        ring
      _ = ν β *
          ∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
            (finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference
                H energyIdentity energyNontrivial x y y' β * p β x) * β⁻¹ := by
        rw [Finset.sum_mul]
      _ = ν β *
          ∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
            (finiteEvenFourTorusZ2OneSlabCouplingFamilyColumnDifference
                H energyIdentity energyNontrivial x y y' β / β) * p β x := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _hx
        rw [div_eq_mul_inv]
        ring
  have h := hRhs.congr' hEq.symm
  simpa [p, ν, n, α, d] using h

end

end MathlibAnalytic
end MGAP4D
