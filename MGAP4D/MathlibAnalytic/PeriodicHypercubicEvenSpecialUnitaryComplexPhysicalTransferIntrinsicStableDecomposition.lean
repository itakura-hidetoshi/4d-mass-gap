import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferIntrinsicAsymptoticProjection
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set Filter Topology
open scoped InnerProductSpace InnerProduct Ring Topology

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

/-- The intrinsic CFC asymptotic projection lands in the fixed sector of the
normalized complex Wilson transfer. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_fixed
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta f) =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta f := by
  exact
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_mem
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta f)).1
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_mem_topEigenspace
        H N hN beta hbeta f)

/-- A vector is fixed by the normalized complex Wilson transfer exactly when the
intrinsic asymptotic projection acts as the identity on that vector.  This is
rank-free: the fixed sector can have arbitrary multiplicity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_eq_self_iff_fixed
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta f = f ↔
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta f = f := by
  let P := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
    H N hN beta hbeta
  let S := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  constructor
  · intro hPf
    have hfixP : S (P f) = P f := by
      simpa [S, P] using
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_fixed
          H N hN beta hbeta f
    simpa [P, S, hPf] using hfixP
  · intro hfix
    have hfTop :
        f ∈ periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
          H N hN beta hbeta := by
      exact
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace_mem
          H N hN beta hbeta f).2 hfix
    have hfRange : f ∈ P.range := by
      rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_range]
      exact hfTop
    rcases hfRange with ⟨x, hx⟩
    have hPP : P * P = P := by
      simpa [P] using
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_self
          H N hN beta hbeta
    have hPPx : P (P x) = P x := by
      have h := congrArg
        (fun T : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
          PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N => T x) hPP
      simpa using h
    calc
      P f = P (P x) := by rw [← hx]
      _ = P x := hPPx
      _ = f := hx

/-- The intrinsic CFC top projection kills a vector exactly when its positive
Wilson-transfer orbit converges strongly to zero.  Thus the kernel of the
asymptotic projection is characterized dynamically, without reference to a
contour. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_eq_zero_iff_pow_succ_tendsto_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta f = 0 ↔
      Tendsto
        (fun n : ℕ =>
          ((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ (n + 1)) f)
        atTop (𝓝 0) := by
  constructor
  · intro hPf
    have htop :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_apply_tendsto_cfcTopProjection
        H N hN beta hbeta f
    simpa [hPf] using htop
  · intro hzero
    have htop :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_apply_tendsto_cfcTopProjection
        H N hN beta hbeta f
    have hunique :
        (0 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) =
          periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
            H N hN beta hbeta f :=
      tendsto_nhds_unique hzero htop
    exact hunique.symm

/-- Orthogonality to the entire fixed/top sector is equivalent to strong decay
to zero under positive normalized Wilson-transfer powers.  Hence the full
transient sector is exactly the top-sector orthogonal complement. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal_mem_iff_pow_succ_tendsto_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    f ∈
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
          H N hN beta hbeta)ᗮ ↔
      Tendsto
        (fun n : ℕ =>
          ((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ (n + 1)) f)
        atTop (𝓝 0) := by
  constructor
  · intro hf
    have htopZero :
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection
          H N hN beta hbeta f = 0 :=
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection_apply_eq_zero_iff
        H N hN beta hbeta f).2 hf
    have hcfcZero :
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta f = 0 := by
      rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_topSpectralProjection]
      exact htopZero
    exact
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_eq_zero_iff_pow_succ_tendsto_zero
        H N hN beta hbeta f).1 hcfcZero
  · intro hzero
    have hcfcZero :=
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_eq_zero_iff_pow_succ_tendsto_zero
        H N hN beta hbeta f).2 hzero
    rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_topSpectralProjection] at hcfcZero
    exact
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopSpectralProjection_apply_eq_zero_iff
        H N hN beta hbeta f).1 hcfcZero

/-- The canonical residual obtained by subtracting the intrinsic asymptotic top
component is transient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_apply_sub_cfcTop_tendsto_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    Tendsto
      (fun n : ℕ =>
        ((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ^ (n + 1))
          (f -
            periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
              H N hN beta hbeta f))
      atTop (𝓝 0) := by
  let P := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
    H N hN beta hbeta
  have hPP : P * P = P := by
    simpa [P] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_self
        H N hN beta hbeta
  have hPPf : P (P f) = P f := by
    have h := congrArg
      (fun T : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N => T f) hPP
    simpa using h
  have hzero : P (f - P f) = 0 := by
    rw [map_sub, hPPf, sub_self]
  exact
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_eq_zero_iff_pow_succ_tendsto_zero
      H N hN beta hbeta (f - P f)).1 hzero

/-- Any decomposition of a physical vector into a fixed Wilson-transfer part
and a transient part is forced to be the canonical CFC-top plus residual
decomposition. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixed_transient_decomposition_unique
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f u v : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N)
    (hdecomp : f = u + v)
    (hu :
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta u = u)
    (hv :
      Tendsto
        (fun n : ℕ =>
          ((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) ^ (n + 1)) v)
        atTop (𝓝 0)) :
    u =
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta f ∧
      v = f -
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta f := by
  let P := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
    H N hN beta hbeta
  have hPu : P u = u := by
    exact
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_eq_self_iff_fixed
        H N hN beta hbeta u).2 hu
  have hPv : P v = 0 := by
    exact
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_eq_zero_iff_pow_succ_tendsto_zero
        H N hN beta hbeta v).2 hv
  have hPf : P f = u := by
    rw [hdecomp, map_add, hPu, hPv, add_zero]
  constructor
  · exact hPf.symm
  · rw [hdecomp]
    change v = u + v - P (u + v)
    rw [map_add, hPu, hPv]
    abel

/-- Every genuine complex physical vector has a unique decomposition into the
full fixed/top sector and the strongly transient sector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_existsUnique_fixed_transient_decomposition
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    ∃! uv :
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N ×
          PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
      f = uv.1 + uv.2 ∧
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta uv.1 = uv.1 ∧
        Tendsto
          (fun n : ℕ =>
            ((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta) ^ (n + 1)) uv.2)
          atTop (𝓝 0) := by
  let P := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
    H N hN beta hbeta
  refine ⟨(P f, f - P f), ?_, ?_⟩
  · constructor
    · dsimp
      abel
    constructor
    · simpa [P] using
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_fixed
          H N hN beta hbeta f
    · simpa [P] using
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_apply_sub_cfcTop_tendsto_zero
          H N hN beta hbeta f
  · intro uv huv
    rcases huv with ⟨hdecomp, hfixed, htransient⟩
    have huniq :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixed_transient_decomposition_unique
        H N hN beta hbeta f uv.1 uv.2 hdecomp hfixed htransient
    apply Prod.ext
    · simpa [P] using huniq.1
    · simpa [P] using huniq.2

/-- Audit-visible intrinsic stable-decomposition package for the genuine
normalized complex Wilson transfer. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferIntrinsicStableDecompositionPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  fixedCharacterization :
    ∀ f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta f = f ↔
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta f = f
  transientCharacterization :
    ∀ f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
      f ∈
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspace
            H N hN beta hbeta)ᗮ ↔
        Tendsto
          (fun n : ℕ =>
            ((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
              H N hN beta hbeta) ^ (n + 1)) f)
          atTop (𝓝 0)
  uniqueDecomposition :
    ∀ f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
      ∃! uv :
          PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N ×
            PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N,
        f = uv.1 + uv.2 ∧
          periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta uv.1 = uv.1 ∧
          Tendsto
            (fun n : ℕ =>
              ((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
                H N hN beta hbeta) ^ (n + 1)) uv.2)
            atTop (𝓝 0)

/-- Construct the intrinsic fixed/transient decomposition package. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferIntrinsicStableDecompositionPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferIntrinsicStableDecompositionPackage
      H N hN beta hbeta :=
  { fixedCharacterization :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_apply_eq_self_iff_fixed
        H N hN beta hbeta
    transientCharacterization :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabTopEigenspaceOrthogonal_mem_iff_pow_succ_tendsto_zero
        H N hN beta hbeta
    uniqueDecomposition :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_existsUnique_fixed_transient_decomposition
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D
