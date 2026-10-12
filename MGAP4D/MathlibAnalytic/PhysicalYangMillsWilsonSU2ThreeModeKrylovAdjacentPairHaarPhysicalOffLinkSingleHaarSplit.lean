import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalOffCoordinateProductSplit
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# P4-Q2-CY: genuine physical off-link Haar product times one SU(N) Haar

CX proved that the ORIGINAL physical spatial left/right pair-Haar law
splits as the off-i finite product Haar law times the honest complement-i
finite Pi Haar law, and CR's retained sigma algebra pulls back from that
first factor.

The complementary index type is ACTUALLY a singleton containing i.
We identify its Pi configuration measurably with ONE SU(N) coordinate,
use the genuine mathlib singleton Pi Haar measure preservation theorem,
and compose with CX. Thus the original physical law is EXACTLY the
retained off-link product Haar times the selected normalized SU(N) Haar,
on the SAME original physical joint configuration space.

This supplies the precise two-factor product law (alpha = off-link,
beta = G) needed to transport CV, without inserting artificial Wilson
conditionals. The literal Haar-fiber average / Hilbert-L² projection
identification and the unconditional full-L² commutation remain pending.
No positive-beta Wilson or continuum Yang--Mills mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

/-- The exact complement to the off-i coordinates is a SINGLE physical
coordinate, not a new or approximate gauge configuration space. -/
private instance p4Q2CY_actualComplementIndexUnique
    (H : ℕ)
    (i : PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H) :
    Unique ({j : PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H //
      ¬(j ≠ i)}) where
  default := ⟨i, by simp⟩
  uniq j := by
    apply Subtype.ext
    exact not_ne_iff.mp j.2

section ActualPairHaar
variable (H N : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "I" =>
  PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "muH" => normalizedCompactHaar G

/-- True original joint coordinates as off-i Haar links and ONE genuine
normalized Haar SU(N) link.  The first component is literally the same
off-coordinate restriction used by CR. -/
noncomputable def p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv
    (i : I) :
    Joint ≃ᵐ (({j : I // j ≠ i} → G) × G) := by
  classical
  exact
    (p4Q2CX_actualPairHaarOffCoordinateSplit H N i).trans
      ((MeasurableEquiv.refl ({j : I // j ≠ i} → G)).prodCongr
        (MeasurableEquiv.piUnique
          (fun _ : {j : I // ¬(j ≠ i)} => G)))

/-- The actual physical left/right pair-Haar law is exactly off-i Haar
finite Pi times the selected SU(N) Haar, under the concrete canonical
measurable equivalence, for EVERY actual left/right spatial link i. -/
theorem p4Q2CY_actualPairHaarOffLinkSingleHaar_measurePreserving
    (i : I) :
    MeasurePreserving (p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i)
      muPair
      ((Measure.pi (fun _ : {j : I // j ≠ i} => muH)).prod muH) := by
  classical
  let muOff : Measure ({j : I // j ≠ i} → G) :=
    Measure.pi (fun _ : {j : I // j ≠ i} => muH)
  let muOne : Measure ({j : I // ¬(j ≠ i)} → G) :=
    Measure.pi (fun _ : {j : I // ¬(j ≠ i)} => muH)
  have hSplit : MeasurePreserving
      (p4Q2CX_actualPairHaarOffCoordinateSplit H N i)
      muPair (muOff.prod muOne) := by
    simpa [muOff, muOne] using
      (p4Q2CX_actualPairHaarOffCoordinateSplit_measurePreserving H N i)
  have hOne : MeasurePreserving
      (MeasurableEquiv.piUnique
        (fun _ : {j : I // ¬(j ≠ i)} => G))
      muOne muH := by
    simpa [muOne] using
      (MeasureTheory.measurePreserving_piUnique
        (fun _ : {j : I // ¬(j ≠ i)} => muH))
  have hProd : MeasurePreserving
      ((MeasurableEquiv.refl ({j : I // j ≠ i} → G)).prodCongr
        (MeasurableEquiv.piUnique
          (fun _ : {j : I // ¬(j ≠ i)} => G)))
      (muOff.prod muOne) (muOff.prod muH) := by
    exact (MeasurePreserving.id muOff).prod hOne
  simpa [p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv, muOff] using
    hSplit.trans hProd

/-- The retained physical sigma algebra is EXACTLY the pullback of the
first factor of the genuine off-coordinate × SINGLE Haar probability. -/
theorem p4Q2CY_actualPairHaarOffCoordinateSigma_eq_splitFirst
    (i : I) :
    p4Q2CR_actualPairHaarOffCoordinateSigma H N i =
      MeasurableSpace.comap
        (Prod.fst ∘ p4Q2CY_actualPairHaarOffLinkSingleHaarEquiv H N i)
        (inferInstance : MeasurableSpace ({j : I // j ≠ i} → G)) := by
  rfl

end ActualPairHaar
end

end MathlibAnalytic
end MGAP4D
