import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalExponentialShellCertificate
import Mathlib.Data.Pi.Interval
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance spatialBaseL1PolynomialShellSpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance spatialBaseL1PolynomialShellSpatialDirectionFintype :
    Fintype PeriodicHypercubicEvenSpatialDirection :=
  Fintype.ofFinite _

/-- There are exactly three spatial coordinate directions. -/
theorem periodicHypercubicEvenSpatialDirection_card :
    Fintype.card PeriodicHypercubicEvenSpatialDirection = 3 := by
  native_decide

private def periodicHypercubicEvenSpatialPolynomialDirectionOne :
    PeriodicHypercubicEvenSpatialDirection :=
  ⟨1, by decide⟩

private def periodicHypercubicEvenSpatialPolynomialDirectionTwo :
    PeriodicHypercubicEvenSpatialDirection :=
  ⟨2, by decide⟩

private def periodicHypercubicEvenSpatialPolynomialDirectionThree :
    PeriodicHypercubicEvenSpatialDirection :=
  ⟨3, by decide⟩

/-- Canonical signed spatial displacement of one target base coordinate from a
fixed source base, using the shortest representative in the periodic torus. -/
def periodicHypercubicEvenSpatialSliceSignedBaseDisplacement
    (H : Nat)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (rho : PeriodicHypercubicEvenSpatialDirection) : Int :=
  (source.1.1 rho.1 - target.1.1 rho.1).valMinAbs

/-- A spatial link is encoded by its link direction together with the three
canonical signed base-coordinate displacements from a fixed source link. -/
def periodicHypercubicEvenSpatialSliceBaseDisplacementCode
    (H : Nat)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenSpatialDirection ×
      (PeriodicHypercubicEvenSpatialDirection → Int) :=
  (target.2,
    periodicHypercubicEvenSpatialSliceSignedBaseDisplacement H source target)

/-- For fixed source, the signed spatial base-displacement code loses no target
link information. The time coordinate is recovered from membership in the
time-zero spatial slice. -/
theorem periodicHypercubicEvenSpatialSliceBaseDisplacementCode_injective
    (H : Nat)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    Function.Injective
      (periodicHypercubicEvenSpatialSliceBaseDisplacementCode H source) := by
  intro target₁ target₂ hCode
  have hDirection : target₁.2 = target₂.2 :=
    congrArg Prod.fst hCode
  have hDisplacement :
      periodicHypercubicEvenSpatialSliceSignedBaseDisplacement H source target₁ =
        periodicHypercubicEvenSpatialSliceSignedBaseDisplacement H source target₂ :=
    congrArg Prod.snd hCode
  apply Prod.ext
  · apply Subtype.ext
    funext i
    fin_cases i
    · have h₁ := target₁.1.2
      have h₂ := target₂.1.2
      unfold periodicHypercubicEvenOnPrimaryReflectionPlane at h₁ h₂
      exact h₁.trans h₂.symm
    · let rho := periodicHypercubicEvenSpatialPolynomialDirectionOne
      have h := congrFun hDisplacement rho
      change
        (source.1.1 1 - target₁.1.1 1).valMinAbs =
          (source.1.1 1 - target₂.1.1 1).valMinAbs at h
      have hz :
          source.1.1 1 - target₁.1.1 1 =
            source.1.1 1 - target₂.1.1 1 :=
        ZMod.injective_valMinAbs h
      exact sub_right_injective hz
    · let rho := periodicHypercubicEvenSpatialPolynomialDirectionTwo
      have h := congrFun hDisplacement rho
      change
        (source.1.1 2 - target₁.1.1 2).valMinAbs =
          (source.1.1 2 - target₂.1.1 2).valMinAbs at h
      have hz :
          source.1.1 2 - target₁.1.1 2 =
            source.1.1 2 - target₂.1.1 2 :=
        ZMod.injective_valMinAbs h
      exact sub_right_injective hz
    · let rho := periodicHypercubicEvenSpatialPolynomialDirectionThree
      have h := congrFun hDisplacement rho
      change
        (source.1.1 3 - target₁.1.1 3).valMinAbs =
          (source.1.1 3 - target₂.1.1 3).valMinAbs at h
      have hz :
          source.1.1 3 - target₁.1.1 3 =
            source.1.1 3 - target₂.1.1 3 :=
        ZMod.injective_valMinAbs h
      exact sub_right_injective hz
  · exact hDirection

/-- The integer cube of spatial displacement functions whose three coordinates
all lie between -r and r. -/
noncomputable def periodicHypercubicEvenSpatialSliceBaseDisplacementBox
    (r : Nat) :
    Finset (PeriodicHypercubicEvenSpatialDirection → Int) :=
  Fintype.piFinset fun _ : PeriodicHypercubicEvenSpatialDirection =>
    Finset.Icc (-(r : Int)) (r : Int)

/-- Include the three possible link directions in the displacement box. -/
noncomputable def periodicHypercubicEvenSpatialSliceLinkBaseDisplacementBox
    (r : Nat) :
    Finset
      (PeriodicHypercubicEvenSpatialDirection ×
        (PeriodicHypercubicEvenSpatialDirection → Int)) :=
  (Finset.univ : Finset PeriodicHypercubicEvenSpatialDirection).product
    (periodicHypercubicEvenSpatialSliceBaseDisplacementBox r)

/-- The symmetric integer interval [-r,r] has exactly 2r+1 elements. -/
theorem periodicHypercubicEvenSpatialSliceSignedInterval_card
    (r : Nat) :
    (Finset.Icc (-(r : Int)) (r : Int)).card = 2 * r + 1 := by
  have h :=
    Int.card_Icc_of_le (a := -(r : Int)) (b := (r : Int)) (by omega)
  exact_mod_cast h

/-- The three-dimensional signed-displacement cube has cardinality
(2r+1)^3, uniformly in the periodic side length. -/
theorem periodicHypercubicEvenSpatialSliceBaseDisplacementBox_card
    (r : Nat) :
    (periodicHypercubicEvenSpatialSliceBaseDisplacementBox r).card =
      (2 * r + 1) ^ 3 := by
  classical
  rw [periodicHypercubicEvenSpatialSliceBaseDisplacementBox,
    Fintype.card_piFinset]
  simp [periodicHypercubicEvenSpatialSliceSignedInterval_card,
    periodicHypercubicEvenSpatialDirection_card]

/-- Including the three link orientations gives at most—and in fact exactly—
three copies of the spatial displacement cube. -/
theorem periodicHypercubicEvenSpatialSliceLinkBaseDisplacementBox_card
    (r : Nat) :
    (periodicHypercubicEvenSpatialSliceLinkBaseDisplacementBox r).card =
      3 * (2 * r + 1) ^ 3 := by
  classical
  simp [periodicHypercubicEvenSpatialSliceLinkBaseDisplacementBox,
    periodicHypercubicEvenSpatialDirection_card,
    periodicHypercubicEvenSpatialSliceBaseDisplacementBox_card]

/-- Every one-coordinate signed displacement is bounded by the full periodic
link-base L1 distance. -/
theorem periodicHypercubicEvenSpatialSliceSignedBaseDisplacement_natAbs_le_baseL1Distance
    (H : Nat)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (rho : PeriodicHypercubicEvenSpatialDirection) :
    (periodicHypercubicEvenSpatialSliceSignedBaseDisplacement
      H source target rho).natAbs ≤
      periodicHypercubicEdgeBaseL1Distance
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) := by
  classical
  unfold periodicHypercubicEvenSpatialSliceSignedBaseDisplacement
  unfold periodicHypercubicEdgeBaseL1Distance periodicHypercubicVertexL1Distance
  exact
    Finset.single_le_sum
      (fun i _hi => Nat.zero_le
        ((source.1.1 i - target.1.1 i).valMinAbs.natAbs))
      (Finset.mem_univ rho.1)

/-- Hence a target at base-L1 radius r has every signed spatial displacement
inside the cube [-r,r]^3. -/
theorem periodicHypercubicEvenSpatialSliceBaseDisplacementCode_mem_box_of_baseL1Distance_eq
    (H : Nat)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (r : Nat)
    (hDistance :
      periodicHypercubicEdgeBaseL1Distance
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) = r) :
    periodicHypercubicEvenSpatialSliceBaseDisplacementCode H source target ∈
      periodicHypercubicEvenSpatialSliceLinkBaseDisplacementBox r := by
  classical
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  apply Fintype.mem_piFinset.mpr
  intro rho
  apply Finset.mem_Icc.mpr
  let z :=
    periodicHypercubicEvenSpatialSliceSignedBaseDisplacement
      H source target rho
  have hNatAbs :
      z.natAbs ≤ r := by
    have h :=
      periodicHypercubicEvenSpatialSliceSignedBaseDisplacement_natAbs_le_baseL1Distance
        H source target rho
    simpa [z, hDistance] using h
  have hCast : (z.natAbs : Int) ≤ (r : Int) := by
    exact_mod_cast hNatAbs
  have hAbs : |z| ≤ (r : Int) := by
    simpa [Int.abs_eq_natAbs] using hCast
  exact (abs_le.mp hAbs)

/-- Uniform polynomial bound for every exact base-L1 shell of spatial links.
This is the three-dimensional torus geometry bound needed for terminal-shell
summability and is independent of H. -/
theorem periodicHypercubicEvenSpatialSliceBaseL1Shell_card_le_polynomial
    (H : Nat)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (r : Nat) :
    ((Finset.univ.filter fun target : PeriodicHypercubicEvenSpatialSliceLink H =>
        periodicHypercubicEdgeBaseL1Distance
            (PeriodicHypercubicEvenSideLength H)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) = r).card) ≤
      3 * (2 * r + 1) ^ 3 := by
  classical
  let shell :=
    Finset.univ.filter fun target : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEdgeBaseL1Distance
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) = r
  let code :=
    periodicHypercubicEvenSpatialSliceBaseDisplacementCode H source
  have hImageCard : (shell.image code).card = shell.card :=
    Finset.card_image_of_injective shell
      (periodicHypercubicEvenSpatialSliceBaseDisplacementCode_injective H source)
  have hSubset :
      shell.image code ⊆
        periodicHypercubicEvenSpatialSliceLinkBaseDisplacementBox r := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨target, hTarget, rfl⟩
    have hDistance :
        periodicHypercubicEdgeBaseL1Distance
            (PeriodicHypercubicEvenSideLength H)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) = r :=
      (Finset.mem_filter.mp hTarget).2
    exact
      periodicHypercubicEvenSpatialSliceBaseDisplacementCode_mem_box_of_baseL1Distance_eq
        H source target r hDistance
  have hCard :=
    Finset.card_le_card hSubset
  rw [hImageCard,
    periodicHypercubicEvenSpatialSliceLinkBaseDisplacementBox_card] at hCard
  simpa [shell] using hCard

/-- The current terminal base-L1 shell, after restricting to the source-aligned
remote target set, inherits the same volume-independent polynomial bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalRemoteSpatialBaseL1Shell_card_le_polynomial
    (H : Nat)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (r : Nat) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source source).filter
        (fun target =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
            H target source = r)).card ≤
      3 * (2 * r + 1) ^ 3 := by
  classical
  apply le_trans
    (Finset.card_le_card (by
      intro target hTarget
      have hRadius := (Finset.mem_filter.mp hTarget).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance] using
        hRadius))
    (periodicHypercubicEvenSpatialSliceBaseL1Shell_card_le_polynomial
      H source r)

end

end MathlibAnalytic
end MGAP4D
