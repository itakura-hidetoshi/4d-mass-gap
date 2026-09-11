import MGAP4D.MathlibAnalytic.FiniteDobrushinTransposeResolventComparison
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCurrentInfluenceChainPlaquettePath
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
# Geometric support of the recursive Dobrushin iterate kernel

The covariance-resolvent route uses the canonical recursive kernel
`finiteInfluenceIterateKernel`, whereas the preceding geometric layer is stated
in terms of proof-relevant chains of nonzero influence edges.  This file closes
that representation gap directly.

A nonzero degree-`d` recursive kernel coefficient produces an exact length-`d`
influence chain.  Consequently, whenever nonzero influence edges are actual
Wilson-plaquette-local steps, a support separation lower bound `D` forces

`finiteInfluenceIterateKernel influence d e f = 0`

for every `d < D`, `e` in the left support, and `f` in the right support.

The result is then specialized to the current compact periodic `SU(N)`
Dobrushin matrix under its explicit finite-volume threshold.  No infinite
Neumann series, covariance decay, continuum threshold, or physical mass-gap
claim is made here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_recursiveKernelSupport
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- A nonzero coefficient of the canonical recursive influence iterate records
an exact-length chain of nonzero influence edges with the same orientation. -/
theorem periodicHypercubicEven_finiteInfluenceIterateKernel_ne_zero_imp_influenceChain
    (H : ℕ)
    (influence :
      PeriodicHypercubicEvenEdge H → PeriodicHypercubicEvenEdge H → ℝ) :
    ∀ d : ℕ, ∀ e f : PeriodicHypercubicEvenEdge H,
      finiteInfluenceIterateKernel influence d e f ≠ 0 →
        periodicHypercubicEvenInfluenceChain H d influence e f := by
  intro d
  induction d with
  | zero =>
      intro e f hNe
      have hef : e = f := by
        by_contra hneq
        apply hNe
        simp [finiteInfluenceIterateKernel, hneq]
      subst f
      refine ⟨fun _ => e, rfl, rfl, ?_⟩
      intro i
      exact Fin.elim0 i
  | succ d ih =>
      intro e f hNe
      have hTerm : ∃ mid : PeriodicHypercubicEvenEdge H,
          influence e mid *
            finiteInfluenceIterateKernel influence d mid f ≠ 0 := by
        by_contra hNone
        push_neg at hNone
        apply hNe
        change
          (∑ mid : PeriodicHypercubicEvenEdge H,
            influence e mid *
              finiteInfluenceIterateKernel influence d mid f) = 0
        exact Finset.sum_eq_zero (fun mid _ => hNone mid)
      rcases hTerm with ⟨mid, hProd⟩
      have hParts := mul_ne_zero_iff.mp hProd
      have hInfluence : influence e mid ≠ 0 := hParts.1
      have hRest :
          finiteInfluenceIterateKernel influence d mid f ≠ 0 := hParts.2
      rcases ih mid f hRest with ⟨γ, h0, hlast, hstep⟩
      refine ⟨Fin.cons e γ, ?_, ?_, ?_⟩
      · simp
      · simpa [hlast] using (Fin.cons_last e γ)
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [h0] using hInfluence
        · simpa using hstep j

/-- If every nonzero influence edge is plaquette-local, actual support
separation kills every coefficient of the canonical recursive iterate kernel
strictly below the support distance. -/
theorem periodicHypercubicEven_finiteInfluenceIterateKernel_eq_zero_of_supportsSeparatedBy
    (H D d : ℕ)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (influence :
      PeriodicHypercubicEvenEdge H → PeriodicHypercubicEvenEdge H → ℝ)
    (hLocal :
      ∀ target source : PeriodicHypercubicEvenEdge H,
        influence target source ≠ 0 →
          periodicHypercubicEvenPlaquetteLocal H target source)
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T)
    (hd : d < D)
    (e : PeriodicHypercubicEvenEdge H)
    (he : e ∈ S)
    (f : PeriodicHypercubicEvenEdge H)
    (hf : f ∈ T) :
    finiteInfluenceIterateKernel influence d e f = 0 := by
  by_contra hNe
  exact
    (periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy_no_short_influenceChain
      H D d S T influence hLocal hsep hd e he f hf)
      (periodicHypercubicEven_finiteInfluenceIterateKernel_ne_zero_imp_influenceChain
        H influence d e f hNe)

/-- Under the current explicit finite-volume compact `SU(N)` Dobrushin
threshold, the recursive kernel used by the transpose resolvent has exact
geometric support: all degrees below a certified plaquette-local support
separation vanish. -/
theorem periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_finiteInfluenceIterateKernel_eq_zero_of_supportsSeparatedBy
    (H N D d : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T)
    (hd : d < D)
    (e : PeriodicHypercubicEvenEdge H)
    (he : e ∈ S)
    (f : PeriodicHypercubicEvenEdge H)
    (hf : f ∈ T) :
    finiteInfluenceIterateKernel
        (periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
          (PeriodicHypercubicEvenSideLength H) N
          (by
            simp [PeriodicHypercubicEvenSideLength]
            omega)
          hN beta hBeta hThreshold).influence
        d e f = 0 := by
  apply
    periodicHypercubicEven_finiteInfluenceIterateKernel_eq_zero_of_supportsSeparatedBy
      H D d S T
      (periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
        (PeriodicHypercubicEvenSideLength H) N
        (by
          simp [PeriodicHypercubicEvenSideLength]
          omega)
        hN beta hBeta hThreshold).influence
  · intro target source hNe
    exact
      periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_plaquetteLocal_of_influence_ne_zero
        H N hH hN beta hBeta hThreshold target source hNe
  · exact hsep
  · exact hd
  · exact he
  · exact hf

end

end MathlibAnalytic
end MGAP4D
