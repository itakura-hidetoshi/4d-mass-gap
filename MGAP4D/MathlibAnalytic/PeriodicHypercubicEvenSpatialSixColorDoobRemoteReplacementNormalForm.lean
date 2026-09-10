import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSixColorCompactConditionalLocality
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumFullSpatialOneLinkDoobBridge
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathCommutation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- If the raw one-link conditional law is unchanged by replacing a distinct
source link, then the corresponding Doob law has an exact normal form on the
same raw reference measure.  The only surviving dependence on the remote
replacement is the vacuum weight evaluated after both link replacements.

This theorem deliberately does not assert Doob locality: it exposes exactly the
additional weight-level obstruction that remains after raw Wilson locality. -/
theorem continuous_compact_oriented_singleLinkDoobConditionalMeasure_remote_replace_normal_form
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (Omega : C.base.Configuration → ℝ≥0∞)
    (A : C.base.Configuration)
    {target source : C.base.geometry.Edge}
    (hNe : source ≠ target)
    (hRaw : ∀ h : C.base.Gauge,
      C.singleLinkConditionalMeasure (C.base.replaceLink A source h) target =
        C.singleLinkConditionalMeasure A target)
    (h : C.base.Gauge) :
    C.singleLinkDoobConditionalMeasure Omega
        (C.base.replaceLink A source h) target =
      doobWeightedMeasure
        (C.singleLinkConditionalMeasure A target)
        (fun g =>
          Omega (C.base.replaceLink
            (C.base.replaceLink A target g) source h)) := by
  rw [continuous_compact_oriented_singleLinkDoobConditionalMeasure_eq]
  rw [hRaw h]
  apply congrArg (doobWeightedMeasure (C.singleLinkConditionalMeasure A target))
  funext g
  exact congrArg Omega
    (compact_oriented_replaceLink_commute_of_ne C.base A hNe g h)

local instance periodicHypercubicEvenSpatialSixColorDoobRemoteSideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance periodicHypercubicEvenSpatialSixColorDoobRemoteIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance periodicHypercubicEvenSpatialSixColorDoobRemoteCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance periodicHypercubicEvenSpatialSixColorDoobRemoteSecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance periodicHypercubicEvenSpatialSixColorDoobRemoteMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance periodicHypercubicEvenSpatialSixColorDoobRemoteBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- On the actual even-periodic compact `SU(N)` Wilson carrier, same-color
geometry removes every remote-replacement dependence from the raw one-link
measure.  Therefore the full continuous-vacuum Doob law after changing a
remote same-color link is exactly the original raw one-link measure reweighted
by the vacuum on the two-link replacement square.

No same-color Doob independence, commutation, or factorization is assumed or
concluded here. -/
theorem
    periodicHypercubicEvenSpatialSliceLink_sameColor_continuousVacuumFullSpatialLinkDoobMeasure_remote_replace_normal_form
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    {e f : PeriodicHypercubicEvenSpatialSliceLink H}
    (hColor : periodicHypercubicEvenSpatialSliceLinkColor H e =
      periodicHypercubicEvenSpatialSliceLinkColor H f)
    (hne : e ≠ f)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (v : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let C := periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
    let Omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
        H N hN beta hbeta
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoobMeasure
        H N hN beta hbeta
        (C.base.replaceLink A
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H f) v) e =
      doobWeightedMeasure
        (C.singleLinkConditionalMeasure A
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H e))
        (fun g =>
          Omega (C.base.replaceLink
            (C.base.replaceLink A
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) g)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H f) v)) := by
  dsimp only
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
      H N hN beta hbeta
  have hNeEmbed :
      periodicHypercubicEvenSpatialSliceLinkEmbedding H f ≠
        periodicHypercubicEvenSpatialSliceLinkEmbedding H e := by
    intro hEq
    apply hne
    exact periodicHypercubicEvenSpatialSliceLinkEmbedding_injective H hEq.symm
  have hRaw : ∀ h : Matrix.specialUnitaryGroup (Fin N) ℂ,
      C.singleLinkConditionalMeasure
          (C.base.replaceLink A
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H f) h)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) =
        C.singleLinkConditionalMeasure A
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) := by
    intro h
    exact
      periodicHypercubicEvenSpatialSliceLink_sameColor_singleLinkConditionalMeasure_replaceLink_eq
        H N hN beta hbeta hColor hne A h
  have hNormal :=
    continuous_compact_oriented_singleLinkDoobConditionalMeasure_remote_replace_normal_form
      C Omega A hNeEmbed hRaw v
  simpa [C, Omega,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoobMeasure]
    using hNormal

end

end MathlibAnalytic
end MGAP4D
