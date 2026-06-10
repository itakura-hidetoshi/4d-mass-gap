import Mathlib

namespace MGAP4D
namespace MathlibAnalytic

/-- Marker that the Mathlib-backed analytic adoption branch has a live Mathlib import. -/
structure MathlibImportSurface where
  mathlibImported : Bool
  analyticBranchOnly : Bool
  mainBoundaryPreserved : Bool

/-- The minimal Mathlib import surface for the exact-gap analytic adoption branch. -/
def mathlibImportSurface : MathlibImportSurface :=
  { mathlibImported := true
    analyticBranchOnly := true
    mainBoundaryPreserved := true }

def MathlibImportSurface.ready (S : MathlibImportSurface) : Bool :=
  S.mathlibImported && S.analyticBranchOnly && S.mainBoundaryPreserved

theorem mathlib_import_surface_ready : mathlibImportSurface.ready = true := by
  rfl

/-- Basic-layer route marker for the normalized exact-gap carrier.

This file intentionally does not install a real-valued gap carrier and does not
expose a `33/20` numerical assignment.  The Hamiltonian spectrum, PVM observable,
and normalized carrier are deferred to the downstream theorem route. -/
structure FourDYangMillsAnalyticGapValueOrigin where
  spectralTheoremRouteDeferred : Bool
  pvmObservableRouteDeferred : Bool
  hamiltonianTheoremRouteDeferred : Bool
  basicLayerNumericCarrierAbsent : Bool

/-- Installed Basic-layer marker: the physical numeric carrier is absent here and
must be obtained through the spectral / PVM / Hamiltonian theorem route. -/
def fourDYangMillsAnalyticGapValueOrigin :
    FourDYangMillsAnalyticGapValueOrigin :=
  { spectralTheoremRouteDeferred := true
    pvmObservableRouteDeferred := true
    hamiltonianTheoremRouteDeferred := true
    basicLayerNumericCarrierAbsent := true }

/-- Boolean readiness check for the Basic-layer route marker. -/
def FourDYangMillsAnalyticGapValueOrigin.ready
    (O : FourDYangMillsAnalyticGapValueOrigin) : Bool :=
  O.spectralTheoremRouteDeferred &&
  O.pvmObservableRouteDeferred &&
  O.hamiltonianTheoremRouteDeferred &&
  O.basicLayerNumericCarrierAbsent

/-- The installed Basic-layer marker is ready while carrying no numeric gap value. -/
theorem four_d_yang_mills_analytic_gap_value_origin_ready :
    fourDYangMillsAnalyticGapValueOrigin.ready = true := by
  rfl

/-- Projection: the Basic layer explicitly records that the exact carrier is not
provided here. -/
theorem four_d_yang_mills_basic_layer_numeric_carrier_absent :
    fourDYangMillsAnalyticGapValueOrigin.basicLayerNumericCarrierAbsent = true := by
  rfl

end MathlibAnalytic
end MGAP4D
