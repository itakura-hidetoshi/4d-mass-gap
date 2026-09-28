import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSourceSet
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairTargetLawL2Decomposition
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceUpdateBackwardLawResponseTransposed
import Mathlib.Tactic

/-!
# Cyclic between-visits source-update semantics

PR #4899 identifies every member of the exact cyclic between-visits list

  suffix ++ pre

with an off-diagonal same-color source.  This file feeds that geometry directly
into the already-closed source-update semantic API.

For every actual cyclic source and distinguished target we obtain, without any
reordering or symmetry assumption:

* the exact Hilbert source-pair decomposition
    fullDifferenceL2 = directDifferenceL2 + responseL2;
* the pointwise backward source-law response identity
    backwardLawResponse = - transposedCanonicalTargetLawResponse.

The second identity keeps the established transposed orientation: the
geometric source remains the response source and the distinguished cyclic
target remains the response target before the pre-existing theorem performs
its source/target transposition internally.

No finite-cardinality estimate, factor two, positive-beta commutativity,
response symmetry, or new quantitative coefficient is introduced.
-/

namespace MGAP4D.MathlibAnalytic

noncomputable section

local instance cyclicSourceUpdateSemanticsSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- An actual cyclic between-visits source automatically satisfies the
off-diagonal hypothesis of the exact source-pair Hilbert decomposition. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointCyclicSourcePairCanonicalTargetLawFullDifferenceL2_eq_directDifferenceL2_add_responseL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (target source :
      PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ target :: suffix)
    (hFresh : target ∉ pre)
    (hsource : source ∈ suffix ++ pre)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
        H N hN beta hbeta B distinguishedSource source.1 target.1 k g₂
        F hF bound hbound left center =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
          H N hN beta hbeta B distinguishedSource source.1 target.1 k g₂
          F hF bound hbound left center +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
          H N hN beta hbeta B distinguishedSource source.1 target.1 k g₂
          F hF bound hbound left center := by
  have hneSourceTarget : source.1 ≠ target.1 :=
    periodicHypercubicEvenFixedSpatialColorLink_cyclicBetweenVisits_source_ne_target
      H color pre suffix target source hSplit hFresh hsource
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_eq_directDifferenceL2_add_responseL2_of_ne
      H N hN beta hbeta B distinguishedSource source.1 target.1
      hneSourceTarget.symm k g₂ F hF bound hbound left center

/-- Along the actual cyclic between-visits list, the backward source-law
response is exactly the negative transposed canonical target-law response.
The off-diagonal premise is discharged by PR #4899 rather than assumed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointCyclicSourceUpdateBackwardLawResponse_currentValue_targetUpdate_eq_neg_transposedCanonicalTargetLawResponse_of_bounded
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (target source :
      PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ target :: suffix)
    (hFresh : target ∉ pre)
    (hsource : source ∈ suffix ++ pre)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
        H N hN beta hbeta source.1 F C C distinguishedSource
        (C distinguishedSource) (C source.1)
        (A, Function.update A target.1 g) =
      -periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponse
        H N hN beta hbeta source.1 target.1 F C C A distinguishedSource
        (C distinguishedSource) (C target.1) g (A target.1) 0 := by
  have hneSourceTarget : source.1 ≠ target.1 :=
    periodicHypercubicEvenFixedSpatialColorLink_cyclicBetweenVisits_source_ne_target
      H color pre suffix target source hSplit hFresh hsource
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse_currentValue_targetUpdate_eq_neg_transposedCanonicalTargetLawResponse_of_bounded
      H N hN beta hbeta C A distinguishedSource source.1 target.1
      hneSourceTarget F hF bound hbound g

end

end MGAP4D.MathlibAnalytic
