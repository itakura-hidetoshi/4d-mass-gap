import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedDirectCancellation

namespace MGAP4D.MathlibAnalytic

#check periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_sourceUpdate_eq_of_sourceInvariant
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean_eq_firstMean_of_sourceInvariant
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2_eq_zero_of_sourceInvariant
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_eq_responseL2_of_sourceInvariant
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_exists_bounded_representative_directCancellation

-- One fixed representative works for two source replacements at the same target value.
example (H N : ℕ) (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hInvariant : ∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
      F (left, Function.update right source value) = F (left, right))
    (left A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (u v g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target (Function.update A source u)) g =
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target (Function.update A source v)) g := by
  exact
    (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_sourceUpdate_eq_of_sourceInvariant
      H N target source hne F hInvariant left A u g).trans
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_sourceUpdate_eq_of_sourceInvariant
        H N target source hne F hInvariant left A v g).symm

-- The physical existence API is instantiated before target/background selection.
example (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
      H N hN beta hbeta) :
    Nonempty {F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ //
      ∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
        F (left, Function.update right source value) = F (left, right)} := by
  obtain ⟨F, _hF, _bound, _hbound, _hRep, hInvariant, _hCancellation⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_exists_bounded_representative_directCancellation
      H N hN beta hbeta source f hf
  exact ⟨⟨F, hInvariant⟩⟩

end MGAP4D.MathlibAnalytic
