import MGAP4D.MathlibAnalytic.FiniteUniformAverageComplementMixedDifferenceWitness
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGroundLiftedConnectedSecondOrderPackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Number of spatial temporal plaquettes whose unfixed temporal holonomy is the
nontrivial Z₂ element.  This Nat-valued statistic separates the finite
combinatorics from the two physical energy values. -/
def finiteEvenFourTorusZ2CrossingNontrivialCount
    (H : ℕ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℕ :=
  ∑ e : FiniteEvenFourTorusSpatialLink H,
    if finiteEvenFourTorusZ2UnfixedTemporalPlaquetteHolonomy H U A B e = 1
    then 0 else 1

/-- Identity boundary used by the minimal side-two crossing-covariance witness. -/
def finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity :
    FiniteEvenFourTorusZ2SliceConfiguration 0 :=
  finiteEvenFourTorusZ2IdentitySlice 0

/-- Single distinguished-link excitation used by the minimal side-two
crossing-covariance witness. -/
def finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation :
    FiniteEvenFourTorusZ2SliceConfiguration 0 :=
  finiteEvenFourTorusZ2SingleLinkExcitation 0
    (finiteEvenFourTorusZ2AllVolumeWitnessLink 0)

/-- At the smallest even spatial torus (`H=0`, side two), there are exactly 256
Z₂ temporal-link fields. -/
theorem finiteEvenFourTorusZ2TemporalLinkField_card_zero :
    Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField 0) = 256 := by
  native_decide

/-- The four boundary pairs of the side-two witness have zero mixed defect in
the first nontrivial-count moment.  This is the finite combinatorial shadow of
the boundary-independent first crossing mean. -/
set_option maxRecDepth 100000 in
theorem finiteEvenFourTorusZ2CrossingNontrivialCount_sum_mixed_balance_zero :
    (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
        finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity) +
      (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
        finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation) =
    (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
        finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation) +
      (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
        finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity) := by
  native_decide

/-- The corresponding mixed defect in the squared nontrivial-count moment is
exactly twice the temporal-field cardinality.  Equivalently, after uniform
averaging, the mixed second-moment defect is exactly `2` before restoring the
energy gap factor. -/
set_option maxRecDepth 100000 in
theorem finiteEvenFourTorusZ2CrossingNontrivialCount_sq_sum_mixed_excess_zero :
    (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
        (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity) ^ 2) +
      (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
        (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation) ^ 2) =
    (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
        (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation) ^ 2) +
      (∑ U : FiniteEvenFourTorusZ2TemporalLinkField 0,
        (finiteEvenFourTorusZ2CrossingNontrivialCount 0 U
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
          finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity) ^ 2) +
      2 * Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField 0) := by
  native_decide

end

end MathlibAnalytic
end MGAP4D
