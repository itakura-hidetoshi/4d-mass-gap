import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2InfiniteLatticePlaquetteClusteringReceiptSurface
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

/-- A public result package for compact infinite-lattice `Z₂` plaquette
clustering.

The result stores a public receipt, a concrete construction package extracted
from the receipt, the two explicit plaquette-observable identities, and the
exponential connected-correlation bound for the selected Prokhorov weak limit.

This is still a theorem package inside the compact infinite-lattice binary
carrier.  It does not construct continuum `ℝ⁴` gauge fields, a DLR state,
reflection positivity, OS reconstruction, a transfer matrix, a Hamiltonian
spectral gap, a physical mass gap, or an unconditional proof of the
four-dimensional Yang--Mills mass gap problem. -/
structure PublicPlaquetteClusteringResult
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) where
  receipt : AllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette
  construction :
    z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction
      beta hBeta distance sourcePlaquette targetPlaquette
  sourceObservable_eq :
    construction.sourceObservable = z2InfiniteHypercubicPlaquetteObservable sourcePlaquette
  targetObservable_eq :
    construction.targetObservable = z2InfiniteHypercubicPlaquetteObservable targetPlaquette
  connectedCorrelation_abs_le :
    abs (construction.prokhorovLimit.toWeakLimit.continuumConnectedCorrelation
        construction.sourceObservable construction.targetObservable) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ))

namespace PublicPlaquetteClusteringResult

/-- Build a public result package from a receipt. -/
noncomputable def ofReceipt
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (R : AllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette) :
    PublicPlaquetteClusteringResult beta hBeta distance sourcePlaquette targetPlaquette :=
  let C := Classical.choose R.existsPackageConnectedCorrelation_abs_le
  let hC := Classical.choose_spec R.existsPackageConnectedCorrelation_abs_le
  { receipt := R
    construction := C
    sourceObservable_eq := hC.1
    targetObservable_eq := hC.2.1
    connectedCorrelation_abs_le := hC.2.2 }

/-- A public receipt surface yields a public result package. -/
theorem nonempty_of_existsAllSurfaceReceipt
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    ExistsAllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette →
      Nonempty
        (PublicPlaquetteClusteringResult beta hBeta distance sourcePlaquette targetPlaquette) := by
  rintro ⟨R⟩
  exact ⟨ofReceipt beta hBeta distance sourcePlaquette targetPlaquette R⟩

/-- A public result package yields the public receipt surface. -/
theorem existsAllSurfaceReceipt_of_nonempty
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    Nonempty
        (PublicPlaquetteClusteringResult beta hBeta distance sourcePlaquette targetPlaquette) →
      ExistsAllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette := by
  rintro ⟨R⟩
  exact ⟨R.receipt⟩

/-- Public result packages are equivalent to the public receipt surface. -/
theorem nonempty_iff_existsAllSurfaceReceipt
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette) :
    Nonempty
        (PublicPlaquetteClusteringResult beta hBeta distance sourcePlaquette targetPlaquette) ↔
      ExistsAllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette := by
  constructor
  · exact existsAllSurfaceReceipt_of_nonempty beta hBeta distance sourcePlaquette targetPlaquette
  · exact nonempty_of_existsAllSurfaceReceipt beta hBeta distance sourcePlaquette targetPlaquette

/-- Explicit façade data produce a public result package. -/
noncomputable def ofData
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance sourcePlaquette targetPlaquette)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    PublicPlaquetteClusteringResult beta hBeta distance sourcePlaquette targetPlaquette :=
  ofReceipt beta hBeta distance sourcePlaquette targetPlaquette
    (AllSurfaceReceipt.ofData beta hBeta distance sourcePlaquette targetPlaquette
      hDistance K)

/-- Explicit façade data produce a nonempty public result package. -/
theorem nonempty_ofData
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance sourcePlaquette targetPlaquette)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    Nonempty
      (PublicPlaquetteClusteringResult beta hBeta distance sourcePlaquette targetPlaquette) :=
  ⟨ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K⟩

/-- The explicit façade-data public result has the canonical receipt. -/
theorem ofData_receipt_eq
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance sourcePlaquette targetPlaquette)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).receipt =
      AllSurfaceReceipt.ofData beta hBeta distance sourcePlaquette targetPlaquette
        hDistance K :=
  rfl

/-- The explicit façade-data public result uses the source plaquette observable. -/
theorem ofData_sourceObservable_eq
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance sourcePlaquette targetPlaquette)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).construction.sourceObservable =
      z2InfiniteHypercubicPlaquetteObservable sourcePlaquette :=
  (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).sourceObservable_eq

/-- The explicit façade-data public result uses the target plaquette observable. -/
theorem ofData_targetObservable_eq
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance sourcePlaquette targetPlaquette)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).construction.targetObservable =
      z2InfiniteHypercubicPlaquetteObservable targetPlaquette :=
  (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).targetObservable_eq

/-- The explicit façade-data public result carries the exponential connected-
correlation bound. -/
theorem ofData_connectedCorrelation_abs_le
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance sourcePlaquette targetPlaquette)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    abs ((ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).construction.prokhorovLimit.toWeakLimit.continuumConnectedCorrelation
        (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).construction.sourceObservable
        (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).construction.targetObservable) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) :=
  (ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K).connectedCorrelation_abs_le

/-- Final public extraction theorem from the explicit compact-carrier façade data.

The theorem returns a public result package containing a receipt, a concrete
construction package, source/target plaquette-observable identities, and the
exponential connected-correlation bound for the selected Prokhorov weak limit.
It keeps the all-volume plaquette distance hypothesis and the finite-volume
clustering certificate as hypotheses and does not assert a physical mass gap. -/
theorem exists_public_result_package_connectedCorrelation_abs_le_ofData
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ)
    (sourcePlaquette targetPlaquette : IntegerHypercubicPlaquette)
    (hDistance :
      z2PeriodicHypercubicInfiniteLatticePlaquetteDistanceHypothesis
        distance sourcePlaquette targetPlaquette)
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta) :
    ∃ (R : PublicPlaquetteClusteringResult beta hBeta distance sourcePlaquette targetPlaquette),
      R.construction.sourceObservable = z2InfiniteHypercubicPlaquetteObservable sourcePlaquette ∧
        R.construction.targetObservable = z2InfiniteHypercubicPlaquetteObservable targetPlaquette ∧
          abs (R.construction.prokhorovLimit.toWeakLimit.continuumConnectedCorrelation
              R.construction.sourceObservable R.construction.targetObservable) ≤
            z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
              Real.exp
                (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
                  (distance : ℝ)) := by
  refine
    ⟨ofData beta hBeta distance sourcePlaquette targetPlaquette hDistance K, ?_, ?_, ?_⟩
  · exact ofData_sourceObservable_eq beta hBeta distance sourcePlaquette targetPlaquette hDistance K
  · exact ofData_targetObservable_eq beta hBeta distance sourcePlaquette targetPlaquette hDistance K
  · exact ofData_connectedCorrelation_abs_le beta hBeta distance sourcePlaquette targetPlaquette hDistance K

end PublicPlaquetteClusteringResult

end z2PeriodicHypercubicInfiniteLatticePlaquetteClusteringConstruction

end

end MathlibAnalytic
end MGAP4D
