import MGAP4D.R3.Theorem.R3HardeningPass
import MGAP4D.R4.Theorem.LowerBoundHardeningPass
import MGAP4D.R5.Theorem.SpectrumInfimumHardeningPass
import MGAP4D.R6.Theorem.IntervalExclusionHardeningPass
import MGAP4D.R7.Theorem.AtomExactHardeningPass

namespace MGAP4D

structure R3R7HardeningPassSeriesReview where
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  r3HardeningPassGreen : Prop
  r4HardeningPassGreen : Prop
  r5HardeningPassGreen : Prop
  r6HardeningPassGreen : Prop
  r7HardeningPassGreen : Prop
  allPassSurfacesVisible : Prop
  theoremCompletionNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def R3R7HardeningPassSeriesReview.ready (S : R3R7HardeningPassSeriesReview) : Prop :=
  S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧
  S.r3HardeningPassGreen ∧ S.r4HardeningPassGreen ∧
  S.r5HardeningPassGreen ∧ S.r6HardeningPassGreen ∧ S.r7HardeningPassGreen ∧
  S.allPassSurfacesVisible ∧ S.theoremCompletionNotClaimed ∧
  S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld

theorem r3_r7_hardening_pass_series_review_pack (S : R3R7HardeningPassSeriesReview) :
    S.ready ↔ S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧
      S.r3HardeningPassGreen ∧ S.r4HardeningPassGreen ∧
      S.r5HardeningPassGreen ∧ S.r6HardeningPassGreen ∧ S.r7HardeningPassGreen ∧
      S.allPassSurfacesVisible ∧ S.theoremCompletionNotClaimed ∧
      S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld := by
  rfl

end MGAP4D
