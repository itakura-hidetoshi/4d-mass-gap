import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalZeroFreeCharacteristicCalculusCore
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The real shifted compressed operator `z I - A`. -/
def continuousLinearMapRealShift
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] V) (z : ℝ) : V →L[ℝ] V :=
  z • (1 : V →L[ℝ] V) - A

/-- The basis-independent real resolvent of a finite-dimensional continuous
endomorphism.  `Ring.inverse` is the true inverse on the resolvent set and is
zero away from the units. -/
def continuousLinearMapRealResolvent
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (z : ℝ) : V →L[ℝ] V :=
  Ring.inverse (continuousLinearMapRealShift A z)

/-- The operator-norm real resolvent profile. -/
def continuousLinearMapRealResolventNorm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (z : ℝ) : ℝ :=
  ‖continuousLinearMapRealResolvent A z‖

/-- A real operator-norm pseudospectrum at a prescribed resolvent-norm level.
It contains nonunits and units whose inverse norm exceeds `level`. -/
def continuousLinearMapRealPseudospectrum
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (level : ℝ) (A : V →L[ℝ] V) : Set ℝ :=
  {z | ¬ IsUnit (continuousLinearMapRealShift A z) ∨
    level < continuousLinearMapRealResolventNorm A z}

/-- A nonzero characteristic determinant makes the shifted finite-dimensional
continuous endomorphism a unit. -/
theorem continuousLinearMapRealShift_isUnit_of_characteristicDeterminant_ne_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (z : ℝ)
    (hdet : continuousLinearMapCharacteristicDeterminant A z ≠ 0) :
    IsUnit (continuousLinearMapRealShift A z) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  let T : V →L[ℝ] V := continuousLinearMapRealShift A z
  have hker : T.ker = ⊥ := by
    by_contra hne
    apply hdet
    exact LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hne
  have hinj : Function.Injective T := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective T := by
    exact LinearMap.range_eq_top.mp
      (LinearMap.ker_eq_bot_iff_range_eq_top.mp hker)
  exact ⟨hinj, hsurj⟩

/-- The ring inverse is a left inverse at every unit. -/
theorem ringInverse_mul_of_isUnit
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
    {x : R} (hx : IsUnit x) :
    Ring.inverse x * x = 1 := by
  rcases hx with ⟨u, rfl⟩
  simp [Ring.inverse_unit]

/-- The ring inverse is a right inverse at every unit. -/
theorem mul_ringInverse_of_isUnit
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
    {x : R} (hx : IsUnit x) :
    x * Ring.inverse x = 1 := by
  rcases hx with ⟨u, rfl⟩
  simp [Ring.inverse_unit]

/-- A nonzero characteristic determinant gives the left resolvent identity. -/
theorem continuousLinearMapRealResolvent_mul_shift
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (z : ℝ)
    (hdet : continuousLinearMapCharacteristicDeterminant A z ≠ 0) :
    continuousLinearMapRealResolvent A z *
      continuousLinearMapRealShift A z = 1 := by
  exact ringInverse_mul_of_isUnit
    (continuousLinearMapRealShift_isUnit_of_characteristicDeterminant_ne_zero
      A z hdet)

/-- A nonzero characteristic determinant gives the right resolvent identity. -/
theorem continuousLinearMapRealShift_mul_resolvent
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (z : ℝ)
    (hdet : continuousLinearMapCharacteristicDeterminant A z ≠ 0) :
    continuousLinearMapRealShift A z *
      continuousLinearMapRealResolvent A z = 1 := by
  exact mul_ringInverse_of_isUnit
    (continuousLinearMapRealShift_isUnit_of_characteristicDeterminant_ne_zero
      A z hdet)

/-- Unit shifted operators are points of the real Banach-algebra resolvent set. -/
theorem continuousLinearMap_mem_real_resolventSet_of_isUnit
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (z : ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift A z)) :
    z ∈ resolventSet ℝ A := by
  simpa [resolventSet, continuousLinearMapRealShift,
    Algebra.algebraMap_eq_smul_one] using hunit

/-- A unit with controlled inverse norm is excluded from the corresponding real
operator-norm pseudospectrum. -/
theorem continuousLinearMap_not_mem_realPseudospectrum_of_isUnit_of_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {level : ℝ} {A : V →L[ℝ] V} {z : ℝ}
    (hunit : IsUnit (continuousLinearMapRealShift A z))
    (hnorm : continuousLinearMapRealResolventNorm A z ≤ level) :
    z ∉ continuousLinearMapRealPseudospectrum level A := by
  simp [continuousLinearMapRealPseudospectrum, hunit, not_lt.mpr hnorm]

/-- Quantitative Neumann stability around a two-sided inverse.  A perturbation
smaller than one half in the normalized inverse scale remains invertible; its
true ring inverse is bounded and differs from the reference inverse by an
explicit quadratic condition-number estimate. -/
theorem continuousLinearMap_ringInverse_neumann_stability
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (B0 B R0 : V →L[ℝ] V)
    (hR0B0 : R0 * B0 = 1) (hB0R0 : B0 * R0 = 1)
    (hsmall : ‖R0 * (B0 - B)‖ < (1 : ℝ) / 2) :
    IsUnit B ∧
      ‖Ring.inverse B‖ ≤ 2 * ‖R0‖ ∧
      ‖Ring.inverse B - R0‖ ≤ 2 * ‖R0‖ ^ 2 * ‖B - B0‖ := by
  let D : V →L[ℝ] V := R0 * (B0 - B)
  have hD : ‖D‖ < 1 := lt_trans hsmall (by norm_num)
  let U : (V →L[ℝ] V)ˣ := Units.oneSub D hD
  let R : V →L[ℝ] V := (↑U⁻¹ : V →L[ℝ] V) * R0
  have hUval : (↑U : V →L[ℝ] V) = 1 - D := by
    simp [U]
  have hBfactor : B = B0 * (1 - D) := by
    dsimp [D]
    calc
      B = B0 - (B0 - B) := by abel
      _ = B0 * (1 - R0 * (B0 - B)) := by
        rw [mul_sub, mul_one, ← mul_assoc, hB0R0, one_mul]
  have hRB : R * B = 1 := by
    rw [hBfactor]
    dsimp [R]
    calc
      ((↑U⁻¹ : V →L[ℝ] V) * R0) * (B0 * (1 - D)) =
          (↑U⁻¹ : V →L[ℝ] V) * (R0 * B0) * (1 - D) := by
            simp [mul_assoc]
      _ = (↑U⁻¹ : V →L[ℝ] V) * (1 - D) := by
            rw [hR0B0, mul_one]
      _ = (↑U⁻¹ : V →L[ℝ] V) * (↑U : V →L[ℝ] V) := by
            rw [hUval]
      _ = 1 := by simp
  have hBR : B * R = 1 := by
    rw [hBfactor]
    dsimp [R]
    calc
      (B0 * (1 - D)) * ((↑U⁻¹ : V →L[ℝ] V) * R0) =
          B0 * ((1 - D) * (↑U⁻¹ : V →L[ℝ] V)) * R0 := by
            simp [mul_assoc]
      _ = B0 * ((↑U : V →L[ℝ] V) * (↑U⁻¹ : V →L[ℝ] V)) * R0 := by
            rw [hUval]
      _ = B0 * R0 := by simp
      _ = 1 := hB0R0
  let BU : (V →L[ℝ] V)ˣ :=
    { val := B
      inv := R
      val_inv := hBR
      inv_val := hRB }
  have hBunit : IsUnit B := ⟨BU, rfl⟩
  have hInvEq : Ring.inverse B = R := by
    have hInvMul : Ring.inverse B * B = 1 := ringInverse_mul_of_isUnit hBunit
    calc
      Ring.inverse B = Ring.inverse B * 1 := by simp
      _ = Ring.inverse B * (B * R) := by rw [hBR]
      _ = (Ring.inverse B * B) * R := by rw [mul_assoc]
      _ = R := by rw [hInvMul, one_mul]
  have hgeom : ‖Ring.inverse (1 - D)‖ ≤ (1 - ‖D‖)⁻¹ := by
    have hs := tsum_geometric_le_of_norm_lt_one D hD
    rw [show Ring.inverse (1 - D) = ∑' n : ℕ, D ^ n by
      exact NormedRing.inverse_one_sub D hD]
    exact hs
  have hden : (1 - ‖D‖)⁻¹ ≤ (2 : ℝ) :=
    inv_le_of_inv_le₀ (by norm_num) (by linarith)
  have hUinvNorm : ‖(↑U⁻¹ : V →L[ℝ] V)‖ ≤ 2 := by
    have hEq : Ring.inverse (1 - D) = (↑U⁻¹ : V →L[ℝ] V) := by
      simpa [U] using NormedRing.inverse_one_sub D hD
    rw [← hEq]
    exact hgeom.trans hden
  have hRnorm : ‖R‖ ≤ 2 * ‖R0‖ := by
    dsimp [R]
    calc
      ‖(↑U⁻¹ : V →L[ℝ] V) * R0‖ ≤
          ‖(↑U⁻¹ : V →L[ℝ] V)‖ * ‖R0‖ := norm_mul_le _ _
      _ ≤ 2 * ‖R0‖ :=
        mul_le_mul_of_nonneg_right hUinvNorm (norm_nonneg R0)
  have hUprod : (↑U⁻¹ : V →L[ℝ] V) * (1 - D) = 1 := by
    rw [← hUval]
    simp
  have hUdiff : (↑U⁻¹ : V →L[ℝ] V) - 1 =
      (↑U⁻¹ : V →L[ℝ] V) * D := by
    rw [← hUprod]
    noncomm_ring
  have hRdiff : R - R0 =
      ((↑U⁻¹ : V →L[ℝ] V) * D) * R0 := by
    dsimp [R]
    rw [← hUdiff]
    noncomm_ring
  have hDnorm : ‖D‖ ≤ ‖R0‖ * ‖B - B0‖ := by
    dsimp [D]
    calc
      ‖R0 * (B0 - B)‖ ≤ ‖R0‖ * ‖B0 - B‖ := norm_mul_le _ _
      _ = ‖R0‖ * ‖B - B0‖ := by rw [norm_sub_rev]
  have hRdiffNorm : ‖R - R0‖ ≤ 2 * ‖R0‖ ^ 2 * ‖B - B0‖ := by
    rw [hRdiff]
    calc
      ‖((↑U⁻¹ : V →L[ℝ] V) * D) * R0‖ ≤
          (‖(↑U⁻¹ : V →L[ℝ] V)‖ * ‖D‖) * ‖R0‖ := by
            exact (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg R0))
      _ ≤ (2 * (‖R0‖ * ‖B - B0‖)) * ‖R0‖ := by
            gcongr
      _ = 2 * ‖R0‖ ^ 2 * ‖B - B0‖ := by ring
  refine ⟨hBunit, ?_, ?_⟩
  · simpa [hInvEq] using hRnorm
  · simpa [hInvEq] using hRdiffNorm

/-- Uniform operator convergence plus a positive continuum determinant margin
and a uniform continuum inverse bound yield eventual unit stability, a uniform
approximating resolvent bound, and operator-norm convergence of the true real
resolvents.  No compactness of the real parameter set is needed once the
inverse bound is supplied explicitly. -/
theorem finiteDimensional_realResolvent_eventually_stable
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (A : α → ι → (V →L[ℝ] V)) (A0 : ι → (V →L[ℝ] V))
    (hA : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖A a i - A0 i‖ < eta)
    (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ i ∈ s, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant (A0 i) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ i ∈ s, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (A0 i) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s, ∀ z ∈ Z,
        IsUnit (continuousLinearMapRealShift (A a i) z) ∧
        continuousLinearMapRealResolventNorm (A a i) z ≤ 2 * (M + 1) ∧
        ‖continuousLinearMapRealResolvent (A a i) z -
          continuousLinearMapRealResolvent (A0 i) z‖ < epsilon := by
  intro epsilon hepsilon
  let C : ℝ := M + 1
  have hC : 0 < C := by dsimp [C]; linarith
  let eta : ℝ := min ((4 * C)⁻¹) (epsilon * (4 * C ^ 2)⁻¹)
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min (inv_pos.mpr (by positivity))
      (mul_pos hepsilon (inv_pos.mpr (by positivity)))
  have hApprox := hA eta heta
  filter_upwards [hApprox] with a ha
  intro i hi z hz
  let B0 : V →L[ℝ] V := continuousLinearMapRealShift (A0 i) z
  let B : V →L[ℝ] V := continuousLinearMapRealShift (A a i) z
  let R0 : V →L[ℝ] V := continuousLinearMapRealResolvent (A0 i) z
  have hdet0 : continuousLinearMapCharacteristicDeterminant (A0 i) z ≠ 0 := by
    exact abs_pos.mp (lt_of_lt_of_le hmargin (hlimitMargin i hi z hz))
  have hR0B0 : R0 * B0 = 1 := by
    exact continuousLinearMapRealResolvent_mul_shift (A0 i) z hdet0
  have hB0R0 : B0 * R0 = 1 := by
    exact continuousLinearMapRealShift_mul_resolvent (A0 i) z hdet0
  have hR0norm : ‖R0‖ ≤ M := hlimitResolventNorm i hi z hz
  have hR0normC : ‖R0‖ ≤ C := by dsimp [C]; linarith
  have hB0subB : B0 - B = A a i - A0 i := by
    dsimp [B0, B, continuousLinearMapRealShift]
    abel
  have hBsubB0Norm : ‖B - B0‖ = ‖A a i - A0 i‖ := by
    have hEq : B - B0 = A0 i - A a i := by
      dsimp [B0, B, continuousLinearMapRealShift]
      abel
    rw [hEq, norm_sub_rev]
  have hetaLeft : eta ≤ (4 * C)⁻¹ := min_le_left _ _
  have hCeta : C * eta ≤ (1 : ℝ) / 4 := by
    calc
      C * eta ≤ C * (4 * C)⁻¹ := by gcongr
      _ = (1 : ℝ) / 4 := by field_simp; ring
  have hsmall : ‖R0 * (B0 - B)‖ < (1 : ℝ) / 2 := by
    calc
      ‖R0 * (B0 - B)‖ ≤ ‖R0‖ * ‖B0 - B‖ := norm_mul_le _ _
      _ = ‖R0‖ * ‖A a i - A0 i‖ := by rw [hB0subB]
      _ ≤ C * ‖A a i - A0 i‖ := by gcongr
      _ < C * eta := by gcongr; exact ha i hi
      _ ≤ (1 : ℝ) / 4 := hCeta
      _ < (1 : ℝ) / 2 := by norm_num
  rcases continuousLinearMap_ringInverse_neumann_stability
      B0 B R0 hR0B0 hB0R0 hsmall with ⟨hunit, hnorm, hdiff⟩
  have hetaRight : eta ≤ epsilon * (4 * C ^ 2)⁻¹ := min_le_right _ _
  have hdiffStrict : ‖Ring.inverse B - R0‖ < epsilon := by
    calc
      ‖Ring.inverse B - R0‖ ≤ 2 * ‖R0‖ ^ 2 * ‖B - B0‖ := hdiff
      _ = 2 * ‖R0‖ ^ 2 * ‖A a i - A0 i‖ := by rw [hBsubB0Norm]
      _ ≤ 2 * C ^ 2 * ‖A a i - A0 i‖ := by gcongr
      _ < 2 * C ^ 2 * eta := by gcongr; exact ha i hi
      _ ≤ 2 * C ^ 2 * (epsilon * (4 * C ^ 2)⁻¹) := by gcongr
      _ = epsilon / 2 := by field_simp; ring
      _ < epsilon := by linarith
  refine ⟨hunit, ?_, ?_⟩
  · dsimp [continuousLinearMapRealResolventNorm,
      continuousLinearMapRealResolvent, B]
    exact hnorm.trans (by gcongr)
  · simpa [continuousLinearMapRealResolvent, B, R0] using hdiffStrict

/-- Compact-free uniform convergence theorem for the operator-valued real
resolvent. -/
theorem finiteDimensional_realResolvent_tendsto_uniformOn_set
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (A : α → ι → (V →L[ℝ] V)) (A0 : ι → (V →L[ℝ] V))
    (hA : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖A a i - A0 i‖ < eta)
    (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ i ∈ s, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant (A0 i) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ i ∈ s, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (A0 i) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s, ∀ z ∈ Z,
        ‖continuousLinearMapRealResolvent (A a i) z -
          continuousLinearMapRealResolvent (A0 i) z‖ < epsilon := by
  intro epsilon hepsilon
  have h := finiteDimensional_realResolvent_eventually_stable
    A A0 hA Z margin hmargin hlimitMargin M hM hlimitResolventNorm
    epsilon hepsilon
  filter_upwards [h] with a ha
  exact fun i hi z hz => (ha i hi z hz).2.2

/-- Eventual uniform real resolvent-set inclusion. -/
theorem finiteDimensional_eventually_mem_real_resolventSet
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (A : α → ι → (V →L[ℝ] V)) (A0 : ι → (V →L[ℝ] V))
    (hA : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖A a i - A0 i‖ < eta)
    (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ i ∈ s, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant (A0 i) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ i ∈ s, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (A0 i) z ≤ M) :
    ∀ᶠ a in l, ∀ i ∈ s, ∀ z ∈ Z,
      z ∈ resolventSet ℝ (A a i) := by
  have h := finiteDimensional_realResolvent_eventually_stable
    A A0 hA Z margin hmargin hlimitMargin M hM hlimitResolventNorm
    1 zero_lt_one
  filter_upwards [h] with a ha
  intro i hi z hz
  exact continuousLinearMap_mem_real_resolventSet_of_isUnit
    (A a i) z (ha i hi z hz).1

/-- Eventual exclusion from the real operator-norm pseudospectrum at the
uniform level `2 (M + 1)`. -/
theorem finiteDimensional_eventually_not_mem_realPseudospectrum
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (A : α → ι → (V →L[ℝ] V)) (A0 : ι → (V →L[ℝ] V))
    (hA : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖A a i - A0 i‖ < eta)
    (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ i ∈ s, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant (A0 i) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ i ∈ s, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (A0 i) z ≤ M) :
    ∀ᶠ a in l, ∀ i ∈ s, ∀ z ∈ Z,
      z ∉ continuousLinearMapRealPseudospectrum (2 * (M + 1)) (A a i) := by
  have h := finiteDimensional_realResolvent_eventually_stable
    A A0 hA Z margin hmargin hlimitMargin M hM hlimitResolventNorm
    1 zero_lt_one
  filter_upwards [h] with a ha
  intro i hi z hz
  exact continuousLinearMap_not_mem_realPseudospectrum_of_isUnit_of_norm_le
    (ha i hi z hz).1 (ha i hi z hz).2.1

end MathlibAnalytic
end MGAP4D
