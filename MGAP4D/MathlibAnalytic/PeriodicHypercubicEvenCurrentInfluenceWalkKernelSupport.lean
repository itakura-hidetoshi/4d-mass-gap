import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCurrentInfluenceChainPlaquettePath
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

/-!
# Support of finite current influence-walk kernels

The preceding layer proves that every chain of nonzero current influence edges
is an actual Wilson-plaquette-local path of the same length.  Here we pass from
the proof-relevant chain carrier to the finite algebraic walk weights that will
be needed by a later static clustering argument.

For a sequence of `d+1` physical links, its length-`d` influence weight is the
product of the `d` consecutive influence coefficients.  A nonzero weight gives
a nonzero influence chain, so any actual support separation lower bound `D`
forces every walk of length `< D` connecting the two supports to have weight
exactly zero.

We then sum those weights over the finite set of all endpoint-constrained walks.
Thus the corresponding finite walk kernel itself vanishes exactly below the
actual plaquette-local support distance.  The current sparse periodic `SU(N)`
influence inherits this statement for arbitrary coupling, and the same-root
scaling theorem makes every fixed sub-distance kernel eventually vanish between
the literal midpoint supports.

Under the explicit finite-volume Dobrushin threshold, the current compact
`DobrushinMatrixData.influence` kernel has the same support property.

This file proves finite walk-kernel support only.  It does not identify this
kernel with a covariance, does not sum an infinite Neumann series, does not
assert the high-temperature threshold along the factorial continuum sequence,
and does not identify update time with physical OS Euclidean time.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_walkKernel
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- Product weight of one length-`d` influence walk. -/
def periodicHypercubicEvenInfluenceWalkWeight
    (H d : ℕ)
    (influence :
      PeriodicHypercubicEvenEdge H → PeriodicHypercubicEvenEdge H → ℝ)
    (γ : Fin (d + 1) → PeriodicHypercubicEvenEdge H) : ℝ :=
  ∏ i : Fin d, influence (γ i.castSucc) (γ i.succ)

/-- A nonzero finite walk weight records a genuine nonzero influence chain. -/
theorem periodicHypercubicEvenInfluenceWalkWeight_ne_zero_imp_chain
    (H d : ℕ)
    (influence :
      PeriodicHypercubicEvenEdge H → PeriodicHypercubicEvenEdge H → ℝ)
    (γ : Fin (d + 1) → PeriodicHypercubicEvenEdge H)
    (hNe : periodicHypercubicEvenInfluenceWalkWeight H d influence γ ≠ 0) :
    periodicHypercubicEvenInfluenceChain H d influence
      (γ 0) (γ (Fin.last d)) := by
  refine ⟨γ, rfl, rfl, ?_⟩
  intro i
  unfold periodicHypercubicEvenInfluenceWalkWeight at hNe
  have hAll := (Finset.prod_ne_zero_iff.mp hNe)
  exact hAll i (Finset.mem_univ i)

/-- If nonzero influence is plaquette-local, actual support separation forces
any endpoint-constrained walk shorter than the separation lower bound to have
zero product weight. -/
theorem periodicHypercubicEvenInfluenceWalkWeight_eq_zero_of_supportsSeparatedBy
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
    (γ : Fin (d + 1) → PeriodicHypercubicEvenEdge H)
    (hstart : γ 0 ∈ S)
    (hend : γ (Fin.last d) ∈ T) :
    periodicHypercubicEvenInfluenceWalkWeight H d influence γ = 0 := by
  by_contra hNe
  have hchain :=
    periodicHypercubicEvenInfluenceWalkWeight_ne_zero_imp_chain
      H d influence γ hNe
  exact
    (periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy_no_short_influenceChain
      H D d S T influence hLocal hsep hd
      (γ 0) hstart (γ (Fin.last d)) hend) hchain

/-- Finite endpoint-constrained sum of all length-`d` influence-walk weights. -/
noncomputable def periodicHypercubicEvenInfluenceWalkKernel
    (H d : ℕ)
    (influence :
      PeriodicHypercubicEvenEdge H → PeriodicHypercubicEvenEdge H → ℝ)
    (e f : PeriodicHypercubicEvenEdge H) : ℝ := by
  classical
  exact
    ∑ γ : Fin (d + 1) → PeriodicHypercubicEvenEdge H,
      if γ 0 = e ∧ γ (Fin.last d) = f then
        periodicHypercubicEvenInfluenceWalkWeight H d influence γ
      else 0

/-- Below the actual support distance, the complete finite influence-walk
kernel between any endpoint in the left support and any endpoint in the right
support is exactly zero. -/
theorem periodicHypercubicEvenInfluenceWalkKernel_eq_zero_of_supportsSeparatedBy
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
    periodicHypercubicEvenInfluenceWalkKernel H d influence e f = 0 := by
  classical
  unfold periodicHypercubicEvenInfluenceWalkKernel
  apply Finset.sum_eq_zero
  intro γ _hγ
  by_cases hEndpoints : γ 0 = e ∧ γ (Fin.last d) = f
  · rw [if_pos hEndpoints]
    apply
      periodicHypercubicEvenInfluenceWalkWeight_eq_zero_of_supportsSeparatedBy
        H D d S T influence hLocal hsep hd γ
    · rw [hEndpoints.1]
      exact he
    · rw [hEndpoints.2]
      exact hf
  · simp [hEndpoints]

/-- Sparse periodic `SU(N)` length-`d` walk kernel. -/
noncomputable def periodicHypercubicEvenSparseActiveTVInfluenceWalkKernel
    (H : ℕ)
    (beta : ℝ)
    (d : ℕ)
    (e f : PeriodicHypercubicEvenEdge H) : ℝ :=
  periodicHypercubicEvenInfluenceWalkKernel H d
    (fun target source =>
      periodicHypercubicSpecialUnitarySparseActiveTVInfluence
        (PeriodicHypercubicEvenSideLength H) beta target source)
    e f

/-- Actual support separation kills every sparse `SU(N)` walk kernel of degree
strictly below the separation lower bound. -/
theorem periodicHypercubicEvenSparseActiveTVInfluenceWalkKernel_eq_zero_of_supportsSeparatedBy
    (H D d : ℕ)
    (beta : ℝ)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T)
    (hd : d < D)
    (e : PeriodicHypercubicEvenEdge H)
    (he : e ∈ S)
    (f : PeriodicHypercubicEvenEdge H)
    (hf : f ∈ T) :
    periodicHypercubicEvenSparseActiveTVInfluenceWalkKernel H beta d e f = 0 := by
  unfold periodicHypercubicEvenSparseActiveTVInfluenceWalkKernel
  exact
    periodicHypercubicEvenInfluenceWalkKernel_eq_zero_of_supportsSeparatedBy
      H D d S T
      (fun target source =>
        periodicHypercubicSpecialUnitarySparseActiveTVInfluence
          (PeriodicHypercubicEvenSideLength H) beta target source)
      (fun target source hNe =>
        periodicHypercubicEvenPlaquetteLocal_of_sparseActiveTVInfluence_ne_zero
          H beta target source hNe)
      hsep hd e he f hf

/-- Same-root scaling makes every fixed sub-distance sparse influence-walk
kernel eventually vanish between the literal reflected-left and translated-right
midpoint supports.  The coupling sequence is arbitrary. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupports_eventually_sparseActiveTVInfluenceWalkKernel_eq_zero_of_scaling
    (H : ℕ → ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing)
        atTop atTop)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 < r)
    (beta : ℕ → ℝ)
    (D : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ d : ℕ, d < D →
        ∀ e : PeriodicHypercubicEvenEdge (H n),
          e ∈
            periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
              (H n) latticeSpacing n J →
          ∀ f : PeriodicHypercubicEvenEdge (H n),
            f ∈
              periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
                (H n) latticeSpacing n J r →
            periodicHypercubicEvenSparseActiveTVInfluenceWalkKernel
              (H n) (beta n) d e f = 0 := by
  have hsep :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupports_eventually_plaquetteLocalSeparatedBy_of_scaling
      H latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero hreach
      J hJ r hr D
  filter_upwards [hsep] with n hsep_n
  intro d hd e he f hf
  exact
    periodicHypercubicEvenSparseActiveTVInfluenceWalkKernel_eq_zero_of_supportsSeparatedBy
      (H n) D d (beta n)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
        (H n) latticeSpacing n J)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
        (H n) latticeSpacing n J r)
      hsep_n hd e he f hf

/-- Under the explicit finite-volume threshold, every current compact `SU(N)`
Dobrushin walk kernel below the actual support distance vanishes exactly. -/
theorem periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_influenceWalkKernel_eq_zero_of_supportsSeparatedBy
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
    periodicHypercubicEvenInfluenceWalkKernel H d
      (periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
        (PeriodicHypercubicEvenSideLength H) N
        (by
          simp [PeriodicHypercubicEvenSideLength]
          omega)
        hN beta hBeta hThreshold).influence
      e f = 0 := by
  apply
    periodicHypercubicEvenInfluenceWalkKernel_eq_zero_of_supportsSeparatedBy
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
