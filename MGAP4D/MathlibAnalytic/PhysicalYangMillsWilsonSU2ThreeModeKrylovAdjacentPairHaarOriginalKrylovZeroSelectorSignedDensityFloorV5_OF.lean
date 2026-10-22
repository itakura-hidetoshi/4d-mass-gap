import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalSignedReceiverNonannihilationV5_OE
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualRightAllDepthZeroCoefficientPosteriorWitnessV5_GX
import Mathlib.Tactic

/-!
# P4-Q2-OF — exact genuine all-depth Krylov ZERO SELECTOR physical signed receiver floor

OE proved a nonuniform finite-volume ORIGINAL signed interacting-Wilson
two-posterior receiver floor for the SAME true Gauss-law constant unit U:
  (Q_GI/N_H)/(10*E_b²) <= L_D(e,z)(R_U(e,z))²
                         + L_D(e',z')(R_U(e',z'))²
at genuine selected two-context physical Wilson witnesses, with Q_GI>0.

The old GX theorem (not a new hypothesis) says that at every scale
n, every finite Krylov depth r, and EVERY nonnegative true FINE Wilson
coupling t=beta(n+1), the genuine physical source synthesized from
the canonical depth-r ZERO selector coefficient a0 is LITERALLY U:
  sum_(j:Fin(r+1)) a0(j) * RightFactor(n,j) = U
inside the ORIGINAL gauge-invariant physical Hilbert submodule.

OF transports OE's true finite-H density-scale positive signed
response floor to precisely that existing physical Krylov coefficient
source, retaining the ORIGINAL frozen b=beta(n), the distinct FINE
t=beta(n+1), the two original interacting posterior laws, actual
FF receiver fiber, and the original physical transfer/half-density.

This gives a single common physical source ACROSS ALL FINITE DEPTHS
at each fixed scale, not a result for arbitrary coefficient vectors
or an automatically compatible source BETWEEN SCALES. No uniform
bound over H/n/r, positive fine arbitrary-r injectivity, H1-C3,
semigroup, or 4d continuum Yang–Mills mass gap follows.
No Dobrushin, artificial physical source/rank, sorry/admit or axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OF_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OF_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OF_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OF_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OF_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section ActualRightZeroSelector
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette Hn
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "N" => (p4Q2LP_originalSpatialPlaquetteCount Hn : ℝ)
local notation "E" => p4Q2LW_originalHarnackContrastScale (beta n)
local notation "Q" => p4Q2LY_originalCompensatedLocalGISquareEnergy
  Hn (beta n) (hbeta n)
local notation "L" => p4Q2OD_originalTwoPosteriorContrastCLM
  Hn (beta n) (hbeta n)
local notation "Fiber" => p4Q2OD_originalPhysicalSignedReceiverFiber
  Hn (beta n) (hbeta n)

/-- This is a literal alias of the ACTUAL fine-right physical Krylov
coefficient sum; no artificial source is constructed. The fine beta
remains the given beta(n+1) inside the existing RightFactor definition. -/
noncomputable def p4Q2OF_actualRightZeroSelectorSource (n r : ℕ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent (n + 1)) 2 :=
  ∑ j : Fin (r + 1),
    p4Q2GX_rightZeroCoefficient r j •
      physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ)

/-- GX's existing exact zero-selector identity, now explicitly tied
to OE's unmodified physical constant Gauss-law source U. Valid for
ALL finite r and all nonnegative genuine fine coupling. -/
theorem p4Q2OF_actualRightZeroSelectorSource_eq_unit (n r : ℕ) :
    p4Q2OF_actualRightZeroSelectorSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r =
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
      (halfExtent (n + 1)) 2 := by
  change (∑ j : Fin (r + 1),
    p4Q2GX_rightZeroCoefficient r j •
      physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ)) =
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
      (halfExtent (n + 1)) 2
  exact p4Q2GX_actualRightCoefficientSource_eq_physicalUnit
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- For any original link and context, the TRUE two-posterior
signed response of the existing arbitrary-depth zero-selector
physical source is EXACTLY the same FF source-weighted receiver
functional as for U. No new kernel-section-to-source surjection. -/
theorem p4Q2OF_actualRightZeroSelector_signedReceiver_eq_unit
    (n r : ℕ) (e : Link) (z : Cfg × Cfg) :
    L z.2 e
      (Fiber
        (p4Q2OF_actualRightZeroSelectorSource
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
        e z) =
    L z.2 e (Fiber U e z) := by
  rw [p4Q2OF_actualRightZeroSelectorSource_eq_unit]

/-- MAIN: for arbitrary finite Krylov depth r and nonnegative true
fine Wilson coupling beta(n+1), the ORIGINAL zero-selector physical
source from the actual right-Krylov coefficient family has the SAME
finite-volume positive GI mean-energy density floor that OE proved
for the true physical unit. Frozen beta(n)>0 is essential; no
uniformity over n,H,r or chosen contexts is asserted. -/
theorem p4Q2OF_actualRightZeroSelector_exists_signedEnergyDensityFloor
    (n r : ℕ) (hfrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      0 < N ∧
      0 < Q e e' z z' / N ∧
      (Q e e' z z' / N) / (10 * E^2) ≤
        (L z.2 e
          (Fiber
            (p4Q2OF_actualRightZeroSelectorSource
              (halfExtent := halfExtent) (beta := beta)
              (hbeta := hbeta) n r)
            e z))^2 +
        (L z'.2 e'
          (Fiber
            (p4Q2OF_actualRightZeroSelectorSource
              (halfExtent := halfExtent) (beta := beta)
              (hbeta := hbeta) n r)
            e' z'))^2 := by
  obtain ⟨z, z', hCount, hQ, hFloor⟩ :=
    p4Q2OE_originalPhysicalUnitReceiver_exists_meanEnergyDensityFloor
      Hn (beta n) (hbeta n) hfrozen e e' left₀ right₀
  refine ⟨z, z', hCount, hQ, ?_⟩
  rw [p4Q2OF_actualRightZeroSelectorSource_eq_unit]
  exact hFloor

/-- At each genuine physical link, the same actual all-depth right
Krylov zero-selector source has a NONZERO original two-interacting-
posterior GI gap at some finite original Wilson context. LB/HY/ID
already established a related zero-mode witness; this theorem records
the exact OE/GX signed-functional transport route and makes no
first-discovery claim for finite-volume source nonzero detection. -/
theorem p4Q2OF_actualRightZeroSelector_eachLink_originalGI_nonzero
    (n r : ℕ) (hfrozen : 0 < beta n)
    (e : Link) (left₀ right₀ : Cfg) :
    ∃ z : Cfg × Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n)
        (p4Q2OF_actualRightZeroSelectorSource
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
        e z ≠ 0 := by
  obtain ⟨z, hz⟩ :=
    p4Q2OE_originalPhysicalUnitGI_eachLink_exists_nonzero
      Hn (beta n) (hbeta n) hfrozen e left₀ right₀
  refine ⟨z, ?_⟩
  rw [p4Q2OF_actualRightZeroSelectorSource_eq_unit]
  exact hz

end ActualRightZeroSelector
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OF_actualRightZeroSelectorSource_eq_unit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OF_actualRightZeroSelector_signedReceiver_eq_unit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OF_actualRightZeroSelector_exists_signedEnergyDensityFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OF_actualRightZeroSelector_eachLink_originalGI_nonzero
