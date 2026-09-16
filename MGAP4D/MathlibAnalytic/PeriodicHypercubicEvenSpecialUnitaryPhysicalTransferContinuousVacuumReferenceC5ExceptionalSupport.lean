import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSliceActiveNeighborBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRemoteCrossRatioIsolation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The only background fibers not covered by the exact remote C5
cross-ratio isolation theorem are the resampled fiber itself, the distinguished
right-target fiber, and the direct spatial Wilson active neighbors of the
resampled fiber. -/
noncomputable def periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
    (H : ℕ)
    (fiber target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact insert fiber
    (insert target (periodicHypercubicEvenSpatialSliceActiveNeighbors H fiber))

/-- The C5 geometric exceptional set has at most twenty spatial links,
uniformly in the periodic volume: at most eighteen direct plaquette neighbors,
plus the resampled fiber and the distinguished right target. -/
theorem periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers_card_le_twenty
    (H : ℕ)
    (fiber target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
      H fiber target).card ≤ 20 := by
  classical
  let s := periodicHypercubicEvenSpatialSliceActiveNeighbors H fiber
  have hActive : s.card ≤ 18 := by
    simpa [s] using
      periodicHypercubicEvenSpatialSliceActiveNeighbors_card_le_eighteen H fiber
  have hTarget : (insert target s).card ≤ s.card + 1 :=
    Finset.card_insert_le target s
  have hFiber : (insert fiber (insert target s)).card ≤
      (insert target s).card + 1 :=
    Finset.card_insert_le fiber (insert target s)
  unfold periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
  change (insert fiber (insert target s)).card ≤ 20
  omega

/-- Outside the C5 exceptional set, a background fiber is distinct from the
resampled fiber and right target and shares no spatial Wilson plaquette with
the resampled fiber.  These are exactly the three geometric hypotheses needed
by the remote full-reference cross-ratio isolation theorem. -/
theorem periodicHypercubicEvenSpatialSlice_not_mem_C5ExceptionalBackgroundFibers
    (H : ℕ)
    (fiber target backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRemote : backgroundFiber ∉
      periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
        H fiber target) :
    fiber ≠ backgroundFiber ∧
      backgroundFiber ≠ target ∧
        ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
          H backgroundFiber fiber := by
  classical
  have hBackgroundFiber : backgroundFiber ≠ fiber := by
    intro hEq
    apply hRemote
    subst backgroundFiber
    simp [periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers]
  have hFiberBackground : fiber ≠ backgroundFiber := Ne.symm hBackgroundFiber
  have hBackgroundTarget : backgroundFiber ≠ target := by
    intro hEq
    apply hRemote
    subst backgroundFiber
    simp [periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers]
  have hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
        H backgroundFiber fiber := by
    intro hShare
    have hShareForward :
        periodicHypercubicEvenSpatialSliceLinksSharePlaquette
          H fiber backgroundFiber := by
      rcases hShare with ⟨p, hBackgroundTouches, hFiberTouches⟩
      exact ⟨p, hFiberTouches, hBackgroundTouches⟩
    have hActive :
        backgroundFiber ∈
          periodicHypercubicEvenSpatialSliceActiveNeighbors H fiber :=
      (periodicHypercubicEvenSpatialSlice_mem_activeNeighbors_iff
        H fiber backgroundFiber).mpr
        ⟨hBackgroundFiber, hShareForward⟩
    apply hRemote
    simp [periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers,
      hActive]
  exact ⟨hFiberBackground, hBackgroundTarget, hNoShare⟩

/-- Outside a volume-independent exceptional set of at most twenty background
fibers, the full literal C5 reference-weight four-point multiplicative defect
is exactly the canonical continuous-vacuum defect.  Thus every geometrically
remote contribution of the local Wilson factors has been cancelled before any
estimate on the vacuum residual is imposed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_remote_background_crossRatio_isolates_vacuum_of_not_mem_exceptional
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRemote : backgroundFiber ∉
      periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
        H fiber target)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (u v g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let Cug := Function.update (Function.update A fiber u) backgroundFiber g
    let Cvh := Function.update (Function.update A fiber v) backgroundFiber h
    let Cuh := Function.update (Function.update A fiber u) backgroundFiber h
    let Cvg := Function.update (Function.update A fiber v) backgroundFiber g
    let Omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂ Cug *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂ Cvh) *
      (Omega Cuh * Omega Cvg) =
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂ Cuh *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂ Cvg) *
      (Omega Cug * Omega Cvh) := by
  rcases
    periodicHypercubicEvenSpatialSlice_not_mem_C5ExceptionalBackgroundFibers
      H fiber target backgroundFiber hRemote with
    ⟨hFiberBackground, hBackgroundTarget, hNoShare⟩
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_remote_background_crossRatio_isolates_vacuum
      H N hN beta hbeta B target source fiber backgroundFiber
      hFiberBackground hBackgroundTarget hNoShare k g₂ A u v g h

end

end MathlibAnalytic
end MGAP4D