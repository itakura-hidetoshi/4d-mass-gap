import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterResponse
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterMultilinearJetBanachCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterMultilinearJetDirectionFamilyCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- A finite ambient-Taylor-level by consecutive-remainder-order rectangle.
The second coordinate `j` represents the true remainder of order
`baseOrder + j`. -/
abbrev ContinuousLinearMapJointTaylorDysonRemainderTailRectangularJet
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (taylorOrder tailOrder : ℕ) :=
  Fin (taylorOrder + 1) → Fin (tailOrder + 1) → (V →L[ℝ] V)

/-- Banach-valued observations of a finite remainder-tail rectangle. -/
abbrev ContinuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet
    (W : Type*) (taylorOrder tailOrder : ℕ) :=
  Fin (taylorOrder + 1) → Fin (tailOrder + 1) → W

noncomputable instance continuousLinearMapJointTaylorDysonRemainderTailRectangularJetCompleteSpace
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (taylorOrder tailOrder : ℕ) :
    CompleteSpace
      (ContinuousLinearMapJointTaylorDysonRemainderTailRectangularJet
        V taylorOrder tailOrder) :=
  inferInstance

noncomputable instance continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetCompleteSpace
    (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (taylorOrder tailOrder : ℕ) :
    CompleteSpace
      (ContinuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet
        W taylorOrder tailOrder) :=
  inferInstance

/-- The synthesized operator increment for a simultaneous spectral and
operator displacement. -/
def continuousLinearMapJointSpectralOperatorRemainderIncrement
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (H : Fin m → (V →L[ℝ] V))
    (ds : ℝ) (h : Fin m → ℝ) : V →L[ℝ] V :=
  continuousLinearMapFiniteParameterOperatorIncrement m H h -
    ds • (1 : V →L[ℝ] V)

/-- The joint increment varies continuously in the complete finite operator
direction family. -/
theorem continuous_continuousLinearMapJointSpectralOperatorRemainderIncrement
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (ds : ℝ) (h : Fin m → ℝ) :
    Continuous (fun H : Fin m → (V →L[ℝ] V) =>
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h) := by
  have hsynth : Continuous (fun H : Fin m → (V →L[ℝ] V) =>
      continuousLinearMapFiniteParameterOperatorIncrement m H h) := by
    simpa [continuousLinearMapFiniteParameterOperatorIncrement] using
      (continuousLinearMapFiniteParameterDirectionSynthesisFamily
        (V := V) m).continuous.clm_apply continuous_const
  exact hsynth.sub continuous_const

/-- One consecutive tail of exact Taylor-Dyson remainders, expressed only in
terms of the base resolvent, the endpoint resolvent, and the synthesized joint
increment. -/
def continuousLinearMapJointTaylorDysonRemainderTailFromResolventPair
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (baseOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : V →L[ℝ] V) : Fin (tailOrder + 1) → (V →L[ℝ] V) :=
  fun j =>
    (Rbase * continuousLinearMapJointSpectralOperatorRemainderIncrement
      m H ds h) ^ (baseOrder + j.1) * Rend

/-- The complete finite ambient-order by remainder-tail rectangle assembled
from base and endpoint resolvent families. -/
def continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V)) :
    ContinuousLinearMapJointTaylorDysonRemainderTailRectangularJet
      V taylorOrder tailOrder :=
  fun k =>
    continuousLinearMapJointTaylorDysonRemainderTailFromResolventPair
      baseOrder tailOrder m H ds h (Rbase k) (Rend k)

/-- Apply an arbitrary continuous-linear Banach-valued observation to every
component of a remainder-tail rectangle. -/
def continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V)) :
    ContinuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet
      W taylorOrder tailOrder :=
  fun k j => φ
    (continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend k j)

/-- Basis-independent traces of the complete finite remainder-tail rectangle. -/
def continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V)) :
    ContinuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet
      ℝ taylorOrder tailOrder :=
  continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
    (continuousLinearMapTrace (V := V)) baseOrder taylorOrder tailOrder m
      H ds h Rbase Rend

/-- The resolvent-pair representation is exactly the established true joint
Taylor-Dyson remainder at the joint origin. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailFromResolventPair_eq_jointRemainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (baseOrder tailOrder m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z ds : ℝ) (h : Fin m → ℝ) (j : Fin (tailOrder + 1)) :
    continuousLinearMapJointTaylorDysonRemainderTailFromResolventPair
        baseOrder tailOrder m H ds h
        (continuousLinearMapRealResolvent A z)
        (continuousLinearMapRealResolvent
          (A + continuousLinearMapJointSpectralOperatorRemainderIncrement
            m H ds h) z) j =
      continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonRemainder
        (baseOrder + j.1) m A H z 0 ds 0 h := by
  unfold continuousLinearMapJointTaylorDysonRemainderTailFromResolventPair
  unfold continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonRemainder
  unfold continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainder
  rw [continuousLinearMapJointSpectralOperatorIncrement_eq]
  unfold continuousLinearMapRealResolventOperatorDysonRemainder
  simp [continuousLinearMapJointSpectralOperatorRemainderIncrement,
    continuousLinearMapFiniteParameterOperatorChart]

/-- Under the usual local resolvent hypotheses, every component of the new
Banach rectangle is the exact endpoint defect of the genuine joint Fréchet
Taylor polynomial. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventChart_sub_frechetTaylor_eq_remainderTail
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (baseOrder tailOrder m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z ds : ℝ) (h : Fin m → ℝ) (j : Fin (tailOrder + 1))
    (hunit : IsUnit (continuousLinearMapRealShift A z))
    (hsmall : ‖continuousLinearMapRealResolvent A z *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ < 1) :
    continuousLinearMapJointSpectralOperatorRealResolventChart m A H z
        (continuousLinearMapJointSpectralOperatorParameter m ds h) -
      continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorPartialSum
        (baseOrder + j.1) m A H z 0 ds 0 h =
      continuousLinearMapJointTaylorDysonRemainderTailFromResolventPair
        baseOrder tailOrder m H ds h
        (continuousLinearMapRealResolvent A z)
        (continuousLinearMapRealResolvent
          (A + continuousLinearMapJointSpectralOperatorRemainderIncrement
            m H ds h) z) j := by
  have hformula :=
    continuousLinearMapJointSpectralOperatorRealResolventChart_add_eq_frechetTaylor_add_remainder
      (baseOrder + j.1) m A H z 0 ds 0 h
      (by simpa [continuousLinearMapFiniteParameterOperatorChart] using hunit)
      (by simpa [continuousLinearMapFiniteParameterRealResolventChart,
          continuousLinearMapFiniteParameterOperatorChart,
          continuousLinearMapJointSpectralOperatorRemainderIncrement] using hsmall)
  have hformula' :
      continuousLinearMapJointSpectralOperatorRealResolventChart m A H z
          (continuousLinearMapJointSpectralOperatorParameter m ds h) =
        continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorPartialSum
            (baseOrder + j.1) m A H z 0 ds 0 h +
          continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonRemainder
            (baseOrder + j.1) m A H z 0 ds 0 h := by
    simpa using hformula
  rw [hformula',
    ← continuousLinearMapJointTaylorDysonRemainderTailFromResolventPair_eq_jointRemainder
      baseOrder tailOrder m A H z ds h j]
  abel

/-- The genuine iterated finite-product norm is below a positive threshold iff
every ambient-order/remainder-order component is. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_iff
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {taylorOrder tailOrder : ℕ}
    (A : ContinuousLinearMapJointTaylorDysonRemainderTailRectangularJet
      V taylorOrder tailOrder)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ‖A‖ < epsilon ↔ ∀ k j, ‖A k j‖ < epsilon := by
  constructor
  · intro h k j
    exact (pi_norm_lt_iff hepsilon).1 ((pi_norm_lt_iff hepsilon).1 h k) j
  · intro h
    apply (pi_norm_lt_iff hepsilon).2
    intro k
    apply (pi_norm_lt_iff hepsilon).2
    intro j
    exact h k j

/-- Norm distance between two remainder-tail rectangles is exactly controlled
componentwise. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_sub_norm_lt_iff
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {taylorOrder tailOrder : ℕ}
    (A B : ContinuousLinearMapJointTaylorDysonRemainderTailRectangularJet
      V taylorOrder tailOrder)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ‖A - B‖ < epsilon ↔ ∀ k j, ‖A k j - B k j‖ < epsilon := by
  simpa using
    (continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_iff
      (A - B) hepsilon)

/-- Componentwise geometric control of every exact remainder in the finite
tail rectangle. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailFromResolventPair_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (baseOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : V →L[ℝ] V) (q M : ℝ)
    (hq : 0 ≤ q) (hM : 0 ≤ M)
    (hperturb : ‖Rbase *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ‖Rend‖ ≤ M) (j : Fin (tailOrder + 1)) :
    ‖continuousLinearMapJointTaylorDysonRemainderTailFromResolventPair
        baseOrder tailOrder m H ds h Rbase Rend j‖ ≤
      q ^ (baseOrder + j.1) * M := by
  let X : V →L[ℝ] V :=
    Rbase * continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h
  have hpow : ‖X ^ (baseOrder + j.1)‖ ≤ q ^ (baseOrder + j.1) := by
    calc
      ‖X ^ (baseOrder + j.1)‖ ≤ ‖X‖ ^ (baseOrder + j.1) :=
        norm_pow_le X (baseOrder + j.1)
      _ ≤ q ^ (baseOrder + j.1) :=
        pow_le_pow_left₀ (norm_nonneg X) hperturb (baseOrder + j.1)
  unfold continuousLinearMapJointTaylorDysonRemainderTailFromResolventPair
  change ‖X ^ (baseOrder + j.1) * Rend‖ ≤
    q ^ (baseOrder + j.1) * M
  exact mul_le_mul (norm_mul_le _ _ |>.trans ?_) hend
    (norm_nonneg Rend) (pow_nonneg hq _)
  exact hpow

/-- Joint continuity of the complete exact remainder-tail carrier rectangle in
both resolvent families and the moving operator-direction family. -/
theorem continuous_continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (baseOrder taylorOrder tailOrder m : ℕ)
    (ds : ℝ) (h : Fin m → ℝ) :
    Continuous (fun p :
      ((Fin (taylorOrder + 1) → (V →L[ℝ] V)) ×
        (Fin (taylorOrder + 1) → (V →L[ℝ] V))) ×
          (Fin m → (V →L[ℝ] V)) =>
      continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
        baseOrder taylorOrder tailOrder m p.2 ds h p.1.1 p.1.2) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro j
  let hbase : Continuous (fun p :
      ((Fin (taylorOrder + 1) → (V →L[ℝ] V)) ×
        (Fin (taylorOrder + 1) → (V →L[ℝ] V))) ×
          (Fin m → (V →L[ℝ] V)) => p.1.1 k) :=
    (continuous_apply k).comp (continuous_fst.comp continuous_fst)
  let hend : Continuous (fun p :
      ((Fin (taylorOrder + 1) → (V →L[ℝ] V)) ×
        (Fin (taylorOrder + 1) → (V →L[ℝ] V))) ×
          (Fin m → (V →L[ℝ] V)) => p.1.2 k) :=
    (continuous_apply k).comp (continuous_snd.comp continuous_fst)
  let hinc : Continuous (fun p :
      ((Fin (taylorOrder + 1) → (V →L[ℝ] V)) ×
        (Fin (taylorOrder + 1) → (V →L[ℝ] V))) ×
          (Fin m → (V →L[ℝ] V)) =>
      continuousLinearMapJointSpectralOperatorRemainderIncrement m p.2 ds h) :=
    (continuous_continuousLinearMapJointSpectralOperatorRemainderIncrement
      (V := V) m ds h).comp continuous_snd
  simpa [continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies,
    continuousLinearMapJointTaylorDysonRemainderTailFromResolventPair] using
    ((hbase.mul hinc).pow (baseOrder + j.1)).mul hend

/-- Joint continuity of arbitrary Banach-valued observations of the complete
remainder-tail rectangle. -/
theorem continuous_continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (ds : ℝ) (h : Fin m → ℝ) :
    Continuous (fun p :
      ((Fin (taylorOrder + 1) → (V →L[ℝ] V)) ×
        (Fin (taylorOrder + 1) → (V →L[ℝ] V))) ×
          (Fin m → (V →L[ℝ] V)) =>
      continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        φ baseOrder taylorOrder tailOrder m p.2 ds h p.1.1 p.1.2) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro j
  have hcarrier :=
    continuous_continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
      (V := V) baseOrder taylorOrder tailOrder m ds h
  exact φ.continuous.comp
    ((continuous_apply j).comp ((continuous_apply k).comp hcarrier))

/-- Joint continuity of the complete basis-independent trace remainder-tail
rectangle. -/
theorem continuous_continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (baseOrder taylorOrder tailOrder m : ℕ)
    (ds : ℝ) (h : Fin m → ℝ) :
    Continuous (fun p :
      ((Fin (taylorOrder + 1) → (V →L[ℝ] V)) ×
        (Fin (taylorOrder + 1) → (V →L[ℝ] V))) ×
          (Fin m → (V →L[ℝ] V)) =>
      continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
        V baseOrder taylorOrder tailOrder m p.2 ds h p.1.1 p.1.2) := by
  simpa [continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies] using
    continuous_continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      (continuousLinearMapTrace (V := V)) baseOrder taylorOrder tailOrder m ds h

end MathlibAnalytic
end MGAP4D
