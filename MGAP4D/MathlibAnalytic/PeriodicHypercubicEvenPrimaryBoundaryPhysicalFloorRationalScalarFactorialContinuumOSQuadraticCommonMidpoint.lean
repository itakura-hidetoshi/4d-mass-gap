import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialContinuumOSCommonSectorMidpoint

/-!
# Factorial continuum OS quadratic midpoint identity in one common finite sector

The preceding layer proves the bilinear common-sector midpoint identity for arbitrary fixed-slot
observables `F` and `G`.  This file records its diagonal specialization, which is the form needed for
null-space preservation.

For a finite nonnegative rational slot set `J` and `t ≥ 0`, the OS quadratic form of the translated
observable `T_t F` on `J+t` equals the mixed common-sector OS form between the original observable
`F` on `J` and its `2t` translate on `J+2t`, after both are included into
`K = J ∪ (J+2t)`.

No null-space preservation, quotient descent, contraction estimate, semigroup, Hamiltonian,
spectral statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Diagonal specialization of the factorial continuum common-sector midpoint identity. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_continuum_fixedSlotOSBilinForm_timeTranslate_self_eq_common_midpoint
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (t : ℚ) (ht : 0 ≤ t)
    (F : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J) :
    L.fixedSlotOSBilinForm H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate t J)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          J t F)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
          J t F) =
      L.fixedSlotOSBilinForm H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet J t)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          J
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet J t)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_left_subset
            J t)
          F)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
            (t + t) J)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet J t)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarOSMidpointCommonSlotSet_future_subset
            J t)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
            J (t + t) F)) := by
  exact
    L.factorial_continuum_fixedSlotOSBilinForm_timeTranslate_eq_common_midpoint
      H N hN beta hbeta J hJ t ht F F

end

end MathlibAnalytic
end MGAP4D
