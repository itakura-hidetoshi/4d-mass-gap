import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCurrentSparseInfluencePlaquetteLocal
import Mathlib.Tactic

/-!
# Current influence chains are actual plaquette-local paths

The preceding layer identifies every nonzero edge of the current periodic
compact `SU(N)` sparse conditional-TV influence with one actual Wilson
plaquette-local physical-link step.  This file lifts that one-step statement to
finite chains.

A proof-relevant influence chain records a sequence of physical links whose
successive influence coefficients are all nonzero.  Whenever nonzero influence
implies actual plaquette locality, the same sequence is therefore an actual
plaquette-local path of the same length.  Consequently an actual support
separation lower bound `D` excludes every influence chain of length `< D`
between the two supports.

For the current sparse `SU(N)` influence this conclusion is unconditional in
the coupling.  Combining it with the scaling separation theorem shows that,
for each fixed natural `D` and strictly positive physical midpoint offset, all
sparse influence chains of length `< D` between the literal midpoint supports
are eventually absent.

Under the explicit finite-volume Dobrushin threshold, the same nonzero-edge
locality also holds for the influence field of the current compact
`DobrushinMatrixData` carrier.

This file proves influence-graph support propagation only.  It does not sum
chain weights, prove covariance decay, assert the high-temperature threshold
along the factorial continuum sequence, or identify update time with physical
OS Euclidean time.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_influenceChain
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- A chain of exactly `d` nonzero influence edges between two physical links.
The orientation is the same as the influence matrix: each consecutive pair is
read as `(target, source)`. -/
def periodicHypercubicEvenInfluenceChain
    (H d : ℕ)
    (influence :
      PeriodicHypercubicEvenEdge H → PeriodicHypercubicEvenEdge H → ℝ)
    (e f : PeriodicHypercubicEvenEdge H) : Prop :=
  ∃ γ : Fin (d + 1) → PeriodicHypercubicEvenEdge H,
    γ 0 = e ∧
      γ (Fin.last d) = f ∧
        ∀ i : Fin d,
          influence (γ i.castSucc) (γ i.succ) ≠ 0

/-- If every nonzero influence edge is actual Wilson-plaquette-local, every
influence chain is an actual plaquette-local path of the same length. -/
theorem periodicHypercubicEvenInfluenceChain_to_plaquetteLocalPath
    (H d : ℕ)
    (influence :
      PeriodicHypercubicEvenEdge H → PeriodicHypercubicEvenEdge H → ℝ)
    (hLocal :
      ∀ target source : PeriodicHypercubicEvenEdge H,
        influence target source ≠ 0 →
          periodicHypercubicEvenPlaquetteLocal H target source)
    (e f : PeriodicHypercubicEvenEdge H)
    (hchain : periodicHypercubicEvenInfluenceChain H d influence e f) :
    periodicHypercubicEvenPlaquetteLocalPath H d e f := by
  rcases hchain with ⟨γ, h0, hlast, hstep⟩
  refine ⟨γ, h0, hlast, ?_⟩
  intro i
  exact hLocal (γ i.castSucc) (γ i.succ) (hstep i)

/-- A support separation lower bound `D` excludes every influence chain of
length `< D` whenever nonzero influence is plaquette-local. -/
theorem periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy_no_short_influenceChain
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
    ¬ periodicHypercubicEvenInfluenceChain H d influence e f := by
  intro hchain
  exact
    hsep d hd e he f hf
      (periodicHypercubicEvenInfluenceChain_to_plaquetteLocalPath
        H d influence hLocal e f hchain)

/-- The current sparse periodic `SU(N)` influence chain. -/
def periodicHypercubicEvenSparseActiveTVInfluenceChain
    (H : ℕ)
    (beta : ℝ)
    (d : ℕ)
    (e f : PeriodicHypercubicEvenEdge H) : Prop :=
  periodicHypercubicEvenInfluenceChain H d
    (fun target source =>
      periodicHypercubicSpecialUnitarySparseActiveTVInfluence
        (PeriodicHypercubicEvenSideLength H) beta target source)
    e f

/-- Every current sparse `SU(N)` influence chain is an actual
Wilson-plaquette-local path of the same length. -/
theorem periodicHypercubicEvenSparseActiveTVInfluenceChain_to_plaquetteLocalPath
    (H : ℕ)
    (beta : ℝ)
    (d : ℕ)
    (e f : PeriodicHypercubicEvenEdge H)
    (hchain : periodicHypercubicEvenSparseActiveTVInfluenceChain H beta d e f) :
    periodicHypercubicEvenPlaquetteLocalPath H d e f := by
  apply
    periodicHypercubicEvenInfluenceChain_to_plaquetteLocalPath
      H d
      (fun target source =>
        periodicHypercubicSpecialUnitarySparseActiveTVInfluence
          (PeriodicHypercubicEvenSideLength H) beta target source)
  · intro target source hNe
    exact
      periodicHypercubicEvenPlaquetteLocal_of_sparseActiveTVInfluence_ne_zero
        H beta target source hNe
  · exact hchain

/-- Actual support separation `D` excludes all current sparse `SU(N)` influence
chains shorter than `D`. -/
theorem periodicHypercubicEvenSparseActiveTVInfluence_no_short_chain_of_supportsSeparatedBy
    (H D d : ℕ)
    (beta : ℝ)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T)
    (hd : d < D)
    (e : PeriodicHypercubicEvenEdge H)
    (he : e ∈ S)
    (f : PeriodicHypercubicEvenEdge H)
    (hf : f ∈ T) :
    ¬ periodicHypercubicEvenSparseActiveTVInfluenceChain H beta d e f := by
  exact
    periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy_no_short_influenceChain
      H D d S T
      (fun target source =>
        periodicHypercubicSpecialUnitarySparseActiveTVInfluence
          (PeriodicHypercubicEvenSideLength H) beta target source)
      (fun target source hNe =>
        periodicHypercubicEvenPlaquetteLocal_of_sparseActiveTVInfluence_ne_zero
          H beta target source hNe)
      hsep hd e he f hf

/-- Under the same-root scaling hypotheses, for every fixed distance `D` all
current sparse influence chains of length `< D` between the literal midpoint
supports are eventually absent.  No small-coupling threshold is used here. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupports_eventually_no_short_sparseActiveTVInfluenceChain_of_scaling
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
            ¬ periodicHypercubicEvenSparseActiveTVInfluenceChain
              (H n) (beta n) d e f := by
  have hsep :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupports_eventually_plaquetteLocalSeparatedBy_of_scaling
      H latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero hreach
      J hJ r hr D
  filter_upwards [hsep] with n hsep_n
  intro d hd e he f hf
  exact
    periodicHypercubicEvenSparseActiveTVInfluence_no_short_chain_of_supportsSeparatedBy
      (H n) D d (beta n)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
        (H n) latticeSpacing n J)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
        (H n) latticeSpacing n J r)
      hsep_n hd e he f hf

/-- Under the explicit finite-volume threshold, every nonzero edge of the
current compact `SU(N)` Dobrushin matrix data is also an actual
Wilson-plaquette-local step. -/
theorem periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_plaquetteLocal_of_influence_ne_zero
    (H N : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (target source : PeriodicHypercubicEvenEdge H)
    (hNe :
      (periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
        (PeriodicHypercubicEvenSideLength H) N
        (by
          simp [PeriodicHypercubicEvenSideLength]
          omega)
        hN beta hBeta hThreshold).influence target source ≠ 0) :
    periodicHypercubicEvenPlaquetteLocal H target source := by
  by_contra hNotLocal
  exact
    hNe
      (periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_influence_eq_zero_of_not_plaquetteLocal
        H N hH hN beta hBeta hThreshold target source hNotLocal)

/-- Hence actual support separation excludes every short influence chain built
from the current compact `SU(N)` Dobrushin matrix data whenever that data is
available under the explicit finite-volume threshold. -/
theorem periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_no_short_influenceChain_of_supportsSeparatedBy
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
    ¬ periodicHypercubicEvenInfluenceChain H d
      (periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
        (PeriodicHypercubicEvenSideLength H) N
        (by
          simp [PeriodicHypercubicEvenSideLength]
          omega)
        hN beta hBeta hThreshold).influence
      e f := by
  apply
    periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy_no_short_influenceChain
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
