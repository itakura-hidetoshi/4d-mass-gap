import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2CenteredPlaquetteHaarCovarianceV5_PZ37ZA
import MGAP4D.MathlibAnalytic.FiniteRealHilbertGramRowBesselBound
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAF — original local Wilson plaquette Haar Gram synthesis

The ORIGINAL SU(2) spatial Wilson plaquette energies are centered in
the original product-Haar reference L2 of the unchanged gauge model;
neither interacting Wilson posterior is replaced by Haar. PZ37ZA
proves true 4-link support, exact orthogonality for disjoint supports,
and a UNIFORM bound of 24 on every absolute Gram row of these original
centered Haar plaquette vectors.

The previously proved finite real Hilbert Schur/Bessel synthesis
theorem therefore gives, for EVERY real coefficient field a_p on all
actual original spatial plaquettes,
  || sum_p a_p V_p ||_Haar^2 <= 24 sum_p a_p^2.
In particular the original all-plaquette centered Haar action sum
has variance at most 24 times the genuine spatial plaquette count.

This is an EXACT original Haar-L2 covariance *UPPER* estimate,
NOT a positive lower Gram bound, NOT an estimate of the original
full-link two-interacting-posterior GL coercivity and NOT YET a
proven equality to the separate Gauss-law physical centered source.
Connecting these original presentations is a subsequent task.
It establishes no mass gap or all-volume fine interval.
No new axiom, sorry/admit/native_decide or gauge/posterior surrogate.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AAF_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAF_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAF_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAF_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAF_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Actual original SU(2) spatial-plaquette Haar-L2 centered linear
synthesis. The common underlying configuration and Haar are original. -/
noncomputable def p4Q2PZ37AAF_originalCenteredHaarPlaquetteSynthesis
    (H : ℕ)
    (a : PeriodicHypercubicEvenSpatialSlicePlaquette H → ℝ) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) :=
  ∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
    a p • p4Q2PZ37ZA_originalCenteredPlaquetteHaarSource H p

/-- ORIGINAL full spatial-plaquette Haar Gram 24-Bessel bound, with
one genuine link-support covariance row for each actual plaquette. -/
theorem p4Q2PZ37AAF_originalCenteredHaarPlaquetteSynthesis_sq_le
    (H : ℕ)
    (a : PeriodicHypercubicEvenSpatialSlicePlaquette H → ℝ) :
    ‖p4Q2PZ37AAF_originalCenteredHaarPlaquetteSynthesis H a‖^2 ≤
      24 * ∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H, (a p)^2 := by
  classical
  exact finiteRealHilbert_synthesis_sq_le_gram_row_bound
    (v := p4Q2PZ37ZA_originalCenteredPlaquetteHaarSource H)
    24
    (fun p => p4Q2PZ37ZA_centeredPlaquette_gram_row_le_twentyFour H p)
    a

/-- In particular the unit-weight ORIGINAL centered Wilson
plaquette Haar sum has squared norm controlled by 24 times the
literal finite spatial-plaquette count, not a thermodynamic proxy. -/
theorem p4Q2PZ37AAF_originalCenteredHaarPlaquetteUnitSum_sq_le_card
    (H : ℕ) :
    ‖p4Q2PZ37AAF_originalCenteredHaarPlaquetteSynthesis H
      (fun _ => (1 : ℝ))‖^2 ≤
      24 * (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) := by
  have h :=
    p4Q2PZ37AAF_originalCenteredHaarPlaquetteSynthesis_sq_le
      H (fun _ => (1 : ℝ))
  simpa using h

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAF_originalCenteredHaarPlaquetteSynthesis_sq_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAF_originalCenteredHaarPlaquetteUnitSum_sq_le_card
