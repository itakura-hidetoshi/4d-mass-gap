import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachCore
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorSharpMinimalTruncationTheoryBundle
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- The sharp carrier base order for the geometric remainder envelope
`q ^ N * M`. -/
noncomputable def continuousLinearMapJointRemainderCarrierSharpOrder
    (q M epsilon : ℝ) : ℕ :=
  geometricDecaySharpTruncationOrder q M epsilon

/-- The sharp response base order obtained from the exact operator norm of the
continuous-linear observation. -/
noncomputable def continuousLinearMapJointRemainderResponseSharpOrder
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (q M epsilon : ℝ) : ℕ :=
  geometricDecaySharpTruncationOrder q (‖φ‖ * M) epsilon

/-- A universally positive response certificate.  It is available without a
nontriviality assumption on the observation. -/
noncomputable def continuousLinearMapJointRemainderResponseSafeOrder
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (q M epsilon : ℝ) : ℕ :=
  geometricDecaySharpTruncationOrder q ((‖φ‖ + 1) * M) epsilon

/-- The universally positive basis-independent trace certificate. -/
noncomputable def continuousLinearMapJointRemainderTraceSafeOrder
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (q M epsilon : ℝ) : ℕ :=
  continuousLinearMapJointRemainderResponseSafeOrder
    (continuousLinearMapTrace (V := V)) q M epsilon

/-- Finite dependent-product response norms are controlled componentwise. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_iff
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {taylorOrder tailOrder : ℕ}
    (A : ContinuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet
      W taylorOrder tailOrder)
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

/-- For `0 ≤ q ≤ 1`, every later member of a geometric tail is bounded by
its base-order envelope. -/
theorem geometricDecay_tailEnvelope_le_base
    {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hM : 0 ≤ M)
    (baseOrder tailIndex : ℕ) :
    q ^ (baseOrder + tailIndex) * M ≤ q ^ baseOrder * M := by
  have hqpow : ∀ n : ℕ, q ^ n ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          q ^ (n + 1) = q ^ n * q := by rw [pow_succ]
          _ ≤ 1 * 1 := mul_le_mul ih hq1 hq0 zero_le_one
          _ = 1 := by ring
  calc
    q ^ (baseOrder + tailIndex) * M =
        (q ^ baseOrder * q ^ tailIndex) * M := by rw [pow_add]
    _ ≤ (q ^ baseOrder * 1) * M :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hqpow tailIndex)
          (pow_nonneg hq0 baseOrder)) hM
    _ = q ^ baseOrder * M := by ring

/-- A geometric base-order envelope controls the norm of the complete finite
ambient-order by remainder-tail rectangle. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_geometricEnvelope
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (henvelope : q ^ baseOrder * M < epsilon)
    (hepsilon : 0 < epsilon) :
    ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
        baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  apply
    (continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_iff
      _ hepsilon).2
  intro k j
  have hcomponent :=
    continuousLinearMapJointTaylorDysonRemainderTailFromResolventPair_norm_le
      baseOrder tailOrder m H ds h (Rbase k) (Rend k) q M
      hq0 hM.le (hperturb k) (hend k) j
  exact lt_of_le_of_lt
    (hcomponent.trans
      (geometricDecay_tailEnvelope_le_base hq0 hq1.le hM.le
        baseOrder j.1))
    henvelope

/-- Every base order at or above the sharp carrier threshold controls the
complete finite remainder-tail rectangle. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_sharpOrder_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hbaseOrder : continuousLinearMapJointRemainderCarrierSharpOrder
      q M epsilon ≤ baseOrder)
    (hepsilon : 0 < epsilon) :
    ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
        baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  have henvelope : q ^ baseOrder * M < epsilon :=
    (geometricDecaySharpTruncationOrder_le_iff
      hq0 hq1 hM hepsilon baseOrder).1 hbaseOrder
  exact
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_geometricEnvelope
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend q M epsilon
      hq0 hq1 hM hperturb hend henvelope hepsilon

/-- The exact sharp carrier order controls the complete finite remainder tail. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_at_sharpOrder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hepsilon : 0 < epsilon) :
    ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
        (continuousLinearMapJointRemainderCarrierSharpOrder q M epsilon)
        taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  exact
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_sharpOrder_le
      (continuousLinearMapJointRemainderCarrierSharpOrder q M epsilon)
      taylorOrder tailOrder m H ds h Rbase Rend q M epsilon
      hq0 hq1 hM hperturb hend le_rfl hepsilon

/-- A geometric envelope transported through an arbitrary bounded observation
controls the complete Banach-valued response rectangle. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_geometricEnvelope
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (Cφ : ℝ)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hCφ : 0 ≤ Cφ) (hφ : ‖φ‖ ≤ Cφ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (henvelope : q ^ baseOrder * (Cφ * M) < epsilon)
    (hepsilon : 0 < epsilon) :
    ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        φ baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  apply
    (continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_iff
      _ hepsilon).2
  intro k j
  let R := continuousLinearMapJointTaylorDysonRemainderTailFromResolventPair
    baseOrder tailOrder m H ds h (Rbase k) (Rend k) j
  have hRcomponent : ‖R‖ ≤ q ^ (baseOrder + j.1) * M := by
    simpa [R] using
      continuousLinearMapJointTaylorDysonRemainderTailFromResolventPair_norm_le
        baseOrder tailOrder m H ds h (Rbase k) (Rend k) q M
        hq0 hM.le (hperturb k) (hend k) j
  have hRbase : ‖R‖ ≤ q ^ baseOrder * M :=
    hRcomponent.trans
      (geometricDecay_tailEnvelope_le_base hq0 hq1.le hM.le
        baseOrder j.1)
  change ‖φ R‖ < epsilon
  calc
    ‖φ R‖ ≤ ‖φ‖ * ‖R‖ := φ.le_opNorm R
    _ ≤ Cφ * (q ^ baseOrder * M) :=
      mul_le_mul hφ hRbase (norm_nonneg R) hCφ
    _ = q ^ baseOrder * (Cφ * M) := by ring
    _ < epsilon := henvelope

/-- Every order at or above the exact response threshold controls the complete
response rectangle, provided the observation has positive operator norm. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_sharpOrder_le
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hφpos : 0 < ‖φ‖)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hbaseOrder : continuousLinearMapJointRemainderResponseSharpOrder
      φ q M epsilon ≤ baseOrder)
    (hepsilon : 0 < epsilon) :
    ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        φ baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  have hconstant : 0 < ‖φ‖ * M := mul_pos hφpos hM
  have henvelope : q ^ baseOrder * (‖φ‖ * M) < epsilon :=
    (geometricDecaySharpTruncationOrder_le_iff
      hq0 hq1 hconstant hepsilon baseOrder).1 hbaseOrder
  exact
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_geometricEnvelope
      φ ‖φ‖ baseOrder taylorOrder tailOrder m H ds h Rbase Rend
      q M epsilon (norm_nonneg φ) le_rfl hq0 hq1 hM hperturb hend
      henvelope hepsilon

/-- A universally available response certificate, using `‖φ‖ + 1` as a
strictly positive dual-norm bound. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_at_safeOrder
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hepsilon : 0 < epsilon) :
    ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        φ (continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon)
        taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  have hC : 0 < ‖φ‖ + 1 := by linarith [norm_nonneg φ]
  have hconstant : 0 < (‖φ‖ + 1) * M := mul_pos hC hM
  have henvelope :
      q ^ continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon *
        ((‖φ‖ + 1) * M) < epsilon := by
    exact geometricDecay_at_sharpTruncationOrder_lt
      hq0 hq1 hconstant hepsilon
  exact
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_geometricEnvelope
      φ (‖φ‖ + 1)
      (continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon)
      taylorOrder tailOrder m H ds h Rbase Rend q M epsilon
      hC.le (by linarith) hq0 hq1 hM hperturb hend henvelope hepsilon

/-- Basis-independent trace tails admit a universal explicit safe order. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJet_norm_lt_at_safeOrder
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hepsilon : 0 < epsilon) :
    ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
        V (continuousLinearMapJointRemainderTraceSafeOrder V q M epsilon)
        taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  simpa [continuousLinearMapJointRemainderTraceSafeOrder,
    continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies] using
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_at_safeOrder
      (continuousLinearMapTrace (V := V)) taylorOrder tailOrder m
      H ds h Rbase Rend q M epsilon hq0 hq1 hM hperturb hend hepsilon

end MathlibAnalytic
end MGAP4D
