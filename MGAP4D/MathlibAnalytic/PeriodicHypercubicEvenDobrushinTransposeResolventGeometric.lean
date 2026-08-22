import MGAP4D.MathlibAnalytic.FiniteDobrushinTransposeResolventComparison
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenDobrushinIterateKernelGeometricSupport
import Mathlib.Tactic

/-!
# Geometric transpose-Dobrushin resolvent bounds

The finite transpose-resolvent comparison leaves a low-degree Neumann part and
a degree-`D` residual.  The recursive-kernel support theorem now shows that the
entire low-degree part vanishes whenever the source variation is supported in a
set `S` and the evaluation link lies in a set `T` separated from `S` by at
least `D` plaquette-local steps.

Thus a transpose-subinvariant profile satisfies the sharp finite geometric
reduction

`w(e) ≤ c^D * ∑ i, w(i)`.

For the current periodic compact `SU(N)` Dobrushin matrix this becomes

`w(e) ≤ rho^D * ∑ i, w(i)`,  `rho = 18 * q(beta)`.

If a later random-scan argument supplies the uniform total bound
`∑ w ≤ (1-rho)⁻¹ ∑_{i∈S} v(i)`, the familiar geometric resolvent estimate
`rho^D / (1-rho)` follows immediately.  This file records that implication but
does not yet construct the random-scan averaged profile itself.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A finite transpose-subinvariant profile whose forcing is supported in `S`
has only the degree-`D` residual left at a point where every kernel coefficient
of degree `< D` from `S` vanishes. -/
theorem finiteInfluenceIterateKernel_subinvariant_le_pow_total_of_supported_source_and_kernel_zero
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (hInfluence : ∀ target source : α, 0 ≤ influence target source)
    (c : ℝ)
    (hc : 0 ≤ c)
    (hrow : ∀ target : α, ∑ source : α, influence target source ≤ c)
    (D : ℕ)
    (S : Finset α)
    (v w : α → ℝ)
    (hw : ∀ initial : α, 0 ≤ w initial)
    (hvSupport : ∀ initial : α, initial ∉ S → v initial = 0)
    (hSub : ∀ source : α,
      w source ≤ v source + ∑ target : α, influence target source * w target)
    (source : α)
    (hKernelZero :
      ∀ k : ℕ, k < D → ∀ initial : α, initial ∈ S →
        finiteInfluenceIterateKernel influence k initial source = 0) :
    w source ≤ c ^ D * ∑ initial : α, w initial := by
  have hBase :=
    finiteInfluenceIterateKernel_subinvariant_le_partial_resolvent_add_pow_residual
      influence hInfluence c hc hrow v w hw hSub D source
  have hPartial :
      (Finset.range D).sum
        (fun k => ∑ initial : α,
          finiteInfluenceIterateKernel influence k initial source * v initial) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkD : k < D := Finset.mem_range.mp hk
    apply Finset.sum_eq_zero
    intro initial _
    by_cases hi : initial ∈ S
    · rw [hKernelZero k hkD initial hi, zero_mul]
    · rw [hvSupport initial hi, mul_zero]
  simpa [hPartial] using hBase

private instance periodicHypercubicEvenSideLength_neZero_transposeResolventGeometric
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- For the current periodic compact `SU(N)` Dobrushin matrix, geometric support
removes every degree below the support separation and leaves only the
`rho^D` residual. -/
theorem periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_transposeSubinvariant_le_pow_total_of_supportsSeparatedBy
    (H N D : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T)
    (v w : PeriodicHypercubicEvenEdge H → ℝ)
    (hw : ∀ initial : PeriodicHypercubicEvenEdge H, 0 ≤ w initial)
    (hvSupport :
      ∀ initial : PeriodicHypercubicEvenEdge H,
        initial ∉ S → v initial = 0)
    (hSub :
      let Ddata :=
        periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
          (PeriodicHypercubicEvenSideLength H) N
          (by
            simp [PeriodicHypercubicEvenSideLength]
            omega)
          hN beta hBeta hThreshold
      ∀ source : PeriodicHypercubicEvenEdge H,
        w source ≤ v source +
          ∑ target : PeriodicHypercubicEvenEdge H,
            Ddata.influence target source * w target)
    (source : PeriodicHypercubicEvenEdge H)
    (hsource : source ∈ T) :
    w source ≤
      (18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D *
        ∑ initial : PeriodicHypercubicEvenEdge H, w initial := by
  let Ddata :=
    periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
      (PeriodicHypercubicEvenSideLength H) N
      (by
        simp [PeriodicHypercubicEvenSideLength]
        omega)
      hN beta hBeta hThreshold
  have hBound :
      w source ≤ Ddata.coefficient ^ D *
        ∑ initial : PeriodicHypercubicEvenEdge H, w initial := by
    exact
      finiteInfluenceIterateKernel_subinvariant_le_pow_total_of_supported_source_and_kernel_zero
        (α := PeriodicHypercubicEvenEdge H)
        Ddata.influence Ddata.influence_nonneg Ddata.coefficient Ddata.coefficient_nonneg
        Ddata.rowSum_le_coefficient D S v w hw hvSupport
        (by simpa [Ddata] using hSub)
        source
        (by
          intro k hk initial hi
          simpa [Ddata] using
            (periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_finiteInfluenceIterateKernel_eq_zero_of_supportsSeparatedBy
              H N D k hH hN beta hBeta hThreshold S T hsep hk
              initial hi source hsource))
  simpa [Ddata,
    periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold] using hBound

/-- Once a uniform total-mass estimate is available for the transpose
subinvariant profile, the exact geometric resolvent factor
`rho^D / (1-rho)` follows. -/
theorem periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_transposeSubinvariant_le_geometric_of_supportsSeparatedBy
    (H N D : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T)
    (v w : PeriodicHypercubicEvenEdge H → ℝ)
    (hw : ∀ initial : PeriodicHypercubicEvenEdge H, 0 ≤ w initial)
    (hvSupport :
      ∀ initial : PeriodicHypercubicEvenEdge H,
        initial ∉ S → v initial = 0)
    (hSub :
      let Ddata :=
        periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
          (PeriodicHypercubicEvenSideLength H) N
          (by
            simp [PeriodicHypercubicEvenSideLength]
            omega)
          hN beta hBeta hThreshold
      ∀ source : PeriodicHypercubicEvenEdge H,
        w source ≤ v source +
          ∑ target : PeriodicHypercubicEvenEdge H,
            Ddata.influence target source * w target)
    (hTotal :
      (∑ initial : PeriodicHypercubicEvenEdge H, w initial) ≤
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)⁻¹ *
          ∑ initial ∈ S, v initial)
    (source : PeriodicHypercubicEvenEdge H)
    (hsource : source ∈ T) :
    w source ≤
      ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
          ∑ initial ∈ S, v initial := by
  let Ddata :=
    periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
      (PeriodicHypercubicEvenSideLength H) N
      (by
        simp [PeriodicHypercubicEvenSideLength]
        omega)
      hN beta hBeta hThreshold
  let rho : ℝ := 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta
  have hRhoNonneg : 0 ≤ rho := by
    have hCoeff : 0 ≤ Ddata.coefficient := Ddata.coefficient_nonneg
    simpa [rho, Ddata,
      periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold] using hCoeff
  have hPow :=
    periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_transposeSubinvariant_le_pow_total_of_supportsSeparatedBy
      H N D hH hN beta hBeta hThreshold S T hsep v w hw hvSupport hSub
      source hsource
  change
    w source ≤ (rho ^ D / (1 - rho)) * ∑ initial ∈ S, v initial
  calc
    w source ≤ rho ^ D * ∑ initial : PeriodicHypercubicEvenEdge H, w initial := by
      simpa [rho] using hPow
    _ ≤ rho ^ D * ((1 - rho)⁻¹ * ∑ initial ∈ S, v initial) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [rho] using hTotal
      · exact pow_nonneg hRhoNonneg D
    _ = (rho ^ D / (1 - rho)) * ∑ initial ∈ S, v initial := by
      rw [div_eq_mul_inv]
      ring

end

end MathlibAnalytic
end MGAP4D
