import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNTwoModeFiniteOSVacuumPairFixedSeam
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonPositiveHalfCanonicalSign
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryMarginalVacuumNormalization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryVacuumL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryVacuumMomentGaugeInvariance
import Mathlib.Tactic

/-!
# Canonical-sign finite OS vacuum as the concrete gauge-fixed boundary vacuum

The coherent positive-half pullback has only a scale-wise sign freedom on the
unit observable.  The existing canonical sign normalization removes that
freedom without changing the reflected quadratic pullback.

This file records the exact consequences needed by the SU(N) two-mode H1-D
lane:

* the completed finite OS vacuum boundary image for Q.vacuumNormalized is
  exactly the concrete Wilson boundary-vacuum L2 vector;
* that concrete vector is fixed by every full finite-lattice boundary gauge
  pullback;
* after exact boundary-to-pair transport, the explicit OS vacuum pair used by
  the two-mode route is therefore the pair-coordinate image of this concrete
  gauge-fixed Wilson vacuum.

No transfer compatibility, spectral input, gap estimate, or pair-carrier
membership is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance vacuumNormalizedBoundaryGaugeFixedTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance vacuumNormalizedBoundaryGaugeFixedCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance vacuumNormalizedBoundaryGaugeFixedSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance vacuumNormalizedBoundaryGaugeFixedMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance vacuumNormalizedBoundaryGaugeFixedBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Haar-L2 pullback by the actual full boundary gauge transformation. -/
noncomputable def periodicHypercubicEvenBoundaryGaugePullbackLinearIsometry
    (H N : ℕ)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
      PeriodicHypercubicEvenBoundaryHaarL2 H N :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
    (periodicHypercubicEvenBoundaryGaugeTransform H N gamma)
    (periodicHypercubicEvenBoundaryGaugeTransform_measurePreserving H N gamma)

/-- The boundary gauge pullback has the expected almost-everywhere
representative. -/
theorem periodicHypercubicEvenBoundaryGaugePullbackLinearIsometry_coeFn
    (H N : ℕ)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenBoundaryGaugePullbackLinearIsometry H N gamma f =ᵐ[
      periodicHypercubicEvenBoundaryHaarMeasure H N]
      fun b => f (periodicHypercubicEvenBoundaryGaugeTransform H N gamma b) := by
  simpa [periodicHypercubicEvenBoundaryGaugePullbackLinearIsometry,
    Function.comp_def] using
    (MeasureTheory.Lp.coeFn_compMeasurePreserving f
      (periodicHypercubicEvenBoundaryGaugeTransform_measurePreserving H N gamma))

/-- The concrete finite Wilson boundary-vacuum L2 vector is fixed by every
actual full boundary gauge pullback. -/
theorem periodicHypercubicEvenBoundaryVacuumL2_gaugeFixed
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenBoundaryGaugePullbackLinearIsometry H N gamma
        (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) =
      periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta := by
  apply Lp.ext
  let vac :=
    periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta
  let T :=
    periodicHypercubicEvenBoundaryGaugeTransform H N gamma
  have hPull :=
    periodicHypercubicEvenBoundaryGaugePullbackLinearIsometry_coeFn
      H N gamma vac
  have hVac :=
    periodicHypercubicEvenBoundaryVacuumL2_coeFn
      H N hN beta hbeta
  have hVacPull :=
    (periodicHypercubicEvenBoundaryGaugeTransform_measurePreserving
      H N gamma).quasiMeasurePreserving.ae_eq hVac
  filter_upwards [hPull, hVacPull, hVac] with b hPullB hVacTB hVacB
  rw [hPullB]
  change vac (T b) = vac b
  calc
    vac (T b) =
        periodicHypercubicEvenBoundaryVacuumMoment
          H N hN beta hbeta (T b) := by
      simpa [T, Function.comp_def] using hVacTB
    _ =
        periodicHypercubicEvenBoundaryVacuumMoment
          H N hN beta hbeta b := by
      exact
        periodicHypercubicEvenBoundaryVacuumMoment_gaugeInvariant
          H N hN beta hbeta gamma b
    _ = vac b := hVacB.symm

section VacuumNormalizedOSBoundary

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))

/-- For the canonical-sign coherent bridge, the completed finite OS vacuum
boundary image is exactly the concrete Wilson boundary-vacuum L2 vector. -/
theorem physicalYangMillsVacuumNormalizedOSVacuumBoundaryL2_eq_boundaryVacuumL2
    (n : ℕ) :
    let Qn := Q.vacuumNormalized
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Qn.toWeakStarBridge hInvariant n
    Qn.physicalHilbertBoundaryMomentLinearIsometry hInvariant n Pn.vacuum =
      periodicHypercubicEvenBoundaryVacuumL2
        (halfExtent n) N hN (beta n) (hbeta n) := by
  dsimp only
  let Qn := Q.vacuumNormalized
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Qn.toWeakStarBridge hInvariant n
  let U := Q.vacuumNormalizedUnitCompatibility hInvariant
  change
    Qn.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (Pn.physicalState Pn.vacuumObservable) =
      periodicHypercubicEvenBoundaryVacuumL2
        (halfExtent n) N hN (beta n) (hbeta n)
  rw [Qn.physicalHilbertBoundaryMomentLinearIsometry_physicalState]
  apply Lp.ext
  exact
    (U.canonicalBoundaryMomentL2_vacuum_coeFn n).trans
      (periodicHypercubicEvenBoundaryVacuumL2_coeFn
        (halfExtent n) N hN (beta n) (hbeta n)).symm

/-- Hence the canonical-sign finite OS vacuum boundary image is itself fixed by
every full boundary gauge pullback. -/
theorem physicalYangMillsVacuumNormalizedOSVacuumBoundaryL2_gaugeFixed
    (n : ℕ)
    (gamma : PeriodicHypercubicEvenVertex (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let Qn := Q.vacuumNormalized
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Qn.toWeakStarBridge hInvariant n
    periodicHypercubicEvenBoundaryGaugePullbackLinearIsometry
        (halfExtent n) N gamma
        (Qn.physicalHilbertBoundaryMomentLinearIsometry hInvariant n Pn.vacuum) =
      Qn.physicalHilbertBoundaryMomentLinearIsometry hInvariant n Pn.vacuum := by
  dsimp only
  rw [
    physicalYangMillsVacuumNormalizedOSVacuumBoundaryL2_eq_boundaryVacuumL2
      Q hInvariant n]
  exact
    periodicHypercubicEvenBoundaryVacuumL2_gaugeFixed
      (halfExtent n) N hN (beta n) (hbeta n) gamma

/-- Pair-coordinate version of the preceding concrete-vacuum identification. -/
theorem physicalYangMillsVacuumNormalizedSUNTwoModeExplicitOSVacuumBoundaryPairL2_eq_boundaryVacuumPair
    (hN2 : 2 ≤ N)
    (n : ℕ) :
    physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n =
      periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
        (halfExtent n) N
        (periodicHypercubicEvenBoundaryVacuumL2
          (halfExtent n) N hN (beta n) (hbeta n)) := by
  let Qn := Q.vacuumNormalized
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Qn.toWeakStarBridge hInvariant n
  change
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
        (halfExtent n) N
        (Qn.physicalHilbertBoundaryMomentLinearIsometry hInvariant n Pn.vacuum) =
      periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
        (halfExtent n) N
        (periodicHypercubicEvenBoundaryVacuumL2
          (halfExtent n) N hN (beta n) (hbeta n))
  rw [
    physicalYangMillsVacuumNormalizedOSVacuumBoundaryL2_eq_boundaryVacuumL2
      Q hInvariant n]

end VacuumNormalizedOSBoundary

end

end MathlibAnalytic
end MGAP4D
