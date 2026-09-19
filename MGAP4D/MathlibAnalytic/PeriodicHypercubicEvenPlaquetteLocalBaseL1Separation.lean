import MGAP4D.MathlibAnalytic.PeriodicHypercubicL1SpatialCovariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPlaquetteLocalPathSeparation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryExplicitDobrushin
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_plaquetteLocalBaseL1
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- One actual Wilson-plaquette-local step changes the periodic link-base
`L¹` distance by at most two. -/
theorem periodicHypercubicEvenPlaquetteLocal_edgeBaseL1Distance_le_two
    (H : ℕ)
    (target source : PeriodicHypercubicEvenEdge H)
    (hLocal : periodicHypercubicEvenPlaquetteLocal H target source) :
    periodicHypercubicEdgeBaseL1Distance
        (PeriodicHypercubicEvenSideLength H) target source ≤ 2 := by
  by_cases hEq : target = source
  · subst source
    simp
  · rcases hLocal with ⟨p, hTarget, hSource⟩
    have hTargetEdges :
        target ∈
          periodicHypercubicPlaquetteEdges
            (PeriodicHypercubicEvenSideLength H) p := by
      simpa [periodicHypercubicEvenPlaquetteEdgeSupport,
        periodicHypercubicPlaquetteEdges,
        periodicHypercubicPhysicalBoundaryEdge] using hTarget
    have hSourceEdges :
        source ∈
          periodicHypercubicPlaquetteEdges
            (PeriodicHypercubicEvenSideLength H) p := by
      simpa [periodicHypercubicEvenPlaquetteEdgeSupport,
        periodicHypercubicPlaquetteEdges,
        periodicHypercubicPhysicalBoundaryEdge] using hSource
    have hTargetTouch :
        periodicHypercubicPlaquetteTouchesEdge
          (PeriodicHypercubicEvenSideLength H) p target :=
      (periodicHypercubicPhysical_mem_plaquetteEdges_iff
        (PeriodicHypercubicEvenSideLength H) p target).mp hTargetEdges
    have hSourceTouch :
        periodicHypercubicPlaquetteTouchesEdge
          (PeriodicHypercubicEvenSideLength H) p source :=
      (periodicHypercubicPhysical_mem_plaquetteEdges_iff
        (PeriodicHypercubicEvenSideLength H) p source).mp hSourceEdges
    have hActive :
        source ∈
          periodicHypercubicActiveNeighbors
            (PeriodicHypercubicEvenSideLength H) target := by
      exact
        (periodicHypercubicPhysical_mem_activeNeighbors_iff
          (PeriodicHypercubicEvenSideLength H) target source).mpr
          ⟨⟨p, hTargetTouch, hSourceTouch⟩, Ne.symm hEq⟩
    have hCoordinate :
        source ∈
          periodicHypercubicCoordinateNeighbors
            (PeriodicHypercubicEvenSideLength H) target :=
      periodicHypercubicActiveNeighbors_subset_coordinateNeighbors
        (PeriodicHypercubicEvenSideLength H) target hActive
    exact
      periodicHypercubicEdgeBaseL1Distance_le_two_of_coordinateNeighbor
        (PeriodicHypercubicEvenSideLength H) target source hCoordinate

/-- Every chain of `d` actual Wilson-plaquette-local steps has endpoint
periodic link-base `L¹` distance at most `2d`. -/
theorem periodicHypercubicEvenPlaquetteLocalChain_edgeBaseL1Distance_le_two_mul
    (H : ℕ) :
    ∀ d : ℕ,
      ∀ γ : Fin (d + 1) → PeriodicHypercubicEvenEdge H,
        (∀ i : Fin d,
          periodicHypercubicEvenPlaquetteLocal H
            (γ i.castSucc) (γ i.succ)) →
          periodicHypercubicEdgeBaseL1Distance
              (PeriodicHypercubicEvenSideLength H)
              (γ 0) (γ (Fin.last d)) ≤ 2 * d := by
  intro d
  induction d with
  | zero =>
      intro γ _
      have hindex : (Fin.last 0 : Fin 1) = 0 := by rfl
      rw [hindex]
      simp
  | succ d ih =>
      intro γ hstep
      let γ' : Fin (d + 1) → PeriodicHypercubicEvenEdge H :=
        fun i => γ i.castSucc
      have hprefix :
          ∀ i : Fin d,
            periodicHypercubicEvenPlaquetteLocal H
              (γ' i.castSucc) (γ' i.succ) := by
        intro i
        simpa [γ'] using hstep i.castSucc
      have hih :
          periodicHypercubicEdgeBaseL1Distance
              (PeriodicHypercubicEvenSideLength H)
              (γ 0) (γ ((Fin.last d).castSucc)) ≤ 2 * d := by
        simpa [γ'] using ih γ' hprefix
      have hlastLocal :
          periodicHypercubicEvenPlaquetteLocal H
            (γ ((Fin.last d).castSucc)) (γ (Fin.last (d + 1))) := by
        simpa using hstep (Fin.last d)
      have hlast :
          periodicHypercubicEdgeBaseL1Distance
              (PeriodicHypercubicEvenSideLength H)
              (γ ((Fin.last d).castSucc)) (γ (Fin.last (d + 1))) ≤ 2 :=
        periodicHypercubicEvenPlaquetteLocal_edgeBaseL1Distance_le_two
          H _ _ hlastLocal
      have htri :=
        periodicHypercubicEdgeBaseL1Distance_triangle
          (PeriodicHypercubicEvenSideLength H)
          (γ 0) (γ ((Fin.last d).castSucc)) (γ (Fin.last (d + 1)))
      omega

/-- Every actual plaquette-local path of length `d` has endpoint periodic
link-base `L¹` distance at most `2d`. -/
theorem periodicHypercubicEvenPlaquetteLocalPath_edgeBaseL1Distance_le_two_mul
    (H d : ℕ)
    {target source : PeriodicHypercubicEvenEdge H}
    (hPath : periodicHypercubicEvenPlaquetteLocalPath H d target source) :
    periodicHypercubicEdgeBaseL1Distance
        (PeriodicHypercubicEvenSideLength H) target source ≤ 2 * d := by
  rcases hPath with ⟨γ, h0, hlast, hstep⟩
  have hChain :=
    periodicHypercubicEvenPlaquetteLocalChain_edgeBaseL1Distance_le_two_mul
      H d γ hstep
  simpa [h0, hlast] using hChain

/-- A periodic link-base `L¹` lower bound `2D` gives a genuine
plaquette-local path-separation lower bound `D` for singleton supports. -/
theorem periodicHypercubicEven_singletons_plaquetteLocalSeparatedBy_of_two_mul_le_edgeBaseL1Distance
    (H D : ℕ)
    (target source : PeriodicHypercubicEvenEdge H)
    (hDistance :
      2 * D ≤
        periodicHypercubicEdgeBaseL1Distance
          (PeriodicHypercubicEvenSideLength H) target source) :
    periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy
      H D {target} {source} := by
  intro d hd e he f hf hPath
  have heq : e = target := by simpa using he
  have hfeq : f = source := by simpa using hf
  subst e
  subst f
  have hUpper :=
    periodicHypercubicEvenPlaquetteLocalPath_edgeBaseL1Distance_le_two_mul
      H d hPath
  omega

end

end MathlibAnalytic
end MGAP4D
