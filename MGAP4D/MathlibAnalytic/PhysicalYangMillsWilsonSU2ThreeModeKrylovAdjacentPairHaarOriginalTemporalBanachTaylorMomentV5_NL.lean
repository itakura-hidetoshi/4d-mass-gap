import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTemporalTwoPointGramV5_NK
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Tactic

/-!
# P4-Q2-NL — full-SU(2) Banach Taylor series of the genuine temporal Wilson kernel

NJ introduced the ORIGINAL temporal SU(2) Wilson exponential sections
  k_(b,x)(g) = exp(b * [1 - E_W(x⁻¹ g)])
as continuous real functions on the FULL compact SU(2). NI/JH/NG
preserve the original two interacting Wilson posterior densities,
right-spatial plaquette Boltzmann weight, and inverse genuine Perron
joint half-density inside rho_(H,b,e,z).

NK proved a strictly positive genuine two-point evaluation determinant
at all b>0; the fixed-b full real LINEAR SPAN density remains OPEN.

NL now formalizes an actual Banach-space analytical step, rather than
a merely pointwise formal identity. Define chi_x in C(SU2,R) from the
literal original Wilson real-trace character, then show:

 (1) k_(b,x) = NormedSpace.exp (b • chi_x) IN C(SU2,R).
 (2) HasSum_{C(SU2,R)} (n!⁻¹ • (b•chi_x)^n) k_(b,x).

This HasSum is convergence in the sup norm on the ACTUAL compact SU(2)
group, so the genuinely original bounded signed Haar functional from
NJ may be passed through it by mathlib HasSum.map:

 (3) HasSum_R [L_rho(n!⁻¹ • (b•chi_x)^n)] M_original(x),

where M_original(x)= ∫ k_(b,x)(g) rho(g) dHaar(g) is precisely the
unchanged NG moment of the authentic two interacting Wilson posteriors.
This is an exact convergent sequence of genuine physical signed moments,
NOT an unproved interchange of integral and divergent series.
 (4) For b>0 all scalar exponential Taylor weights b^n/n! are positive.

NL by itself does NOT prove sign noncancellation for the actual
infinite series, positivity of every SU2 irreducible Fourier
coefficient, density of fixed-b Wilson section span, Q_original>0,
nonzero Gauss-law GI covariance, H1-C3 or continuum mass gap.
No substitution, rank/injectivity assumption, Dobrushin or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NL_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NL_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NL_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NL_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NL_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- The ORIGINAL fundamental normalized real Wilson character as a
real continuous function on the ACTUAL compact SU(2), at source x. -/
noncomputable def p4Q2NL_originalTemporalCharacterContinuous
    (x : Gauge) : C(Gauge,ℝ) := by
  have hShift : Continuous (fun g : Gauge => x⁻¹ * g) :=
    continuous_const.mul continuous_id
  have hChi :
      Continuous (fun g : Gauge => p4Q2NG_originalSU2TemporalCharacter x g) := by
    unfold p4Q2NG_originalSU2TemporalCharacter
    exact continuous_const.sub
      ((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp hShift)
  exact ⟨fun g => p4Q2NG_originalSU2TemporalCharacter x g, hChi⟩

/-- Exact genuine temporal Wilson section equals the analytic Banach
exponential of its real normalized SU(2) trace in C(SU2,R).
This is an identity on ALL SU(2), not just on finite test points. -/
theorem p4Q2NL_originalWilsonTemporalSection_eq_BanachExp
    (b : ℝ) (x : Gauge) :
    p4Q2NJ_originalSU2WilsonTemporalSection b x =
      NormedSpace.exp (b • p4Q2NL_originalTemporalCharacterContinuous x) := by
  rw [NormedSpace.exp_continuousMap_eq]
  ext g
  change Real.exp (b * p4Q2NG_originalSU2TemporalCharacter x g) =
    Real.exp (b * p4Q2NG_originalSU2TemporalCharacter x g)
  rfl

/-- TRUE sup-norm convergent power-series representation of the
original temporal Wilson kernel as an element of C(SU2,R).
No pointwise-only manipulation or unproved harmonic convergence. -/
theorem p4Q2NL_originalWilsonTemporalSection_Banach_hasSum
    (b : ℝ) (x : Gauge) :
    HasSum
      (fun n : ℕ =>
        (n !⁻¹ : ℝ) •
          (b • p4Q2NL_originalTemporalCharacterContinuous x) ^ n)
      (p4Q2NJ_originalSU2WilsonTemporalSection b x) := by
  rw [p4Q2NL_originalWilsonTemporalSection_eq_BanachExp]
  exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ)
    (b • p4Q2NL_originalTemporalCharacterContinuous x)

/-- In particular these TRUE SU(2) Wilson polynomial-coefficient
sections are summable in the UNIFORM C(SU2,R) norm. -/
theorem p4Q2NL_originalWilsonTemporalSection_Banach_summable
    (b : ℝ) (x : Gauge) :
    Summable
      (fun n : ℕ =>
        (n !⁻¹ : ℝ) •
          (b • p4Q2NL_originalTemporalCharacterContinuous x) ^ n) :=
  (p4Q2NL_originalWilsonTemporalSection_Banach_hasSum b x).summable

/-- For every positive Wilson coupling, each SCALAR Taylor coefficient
b^n / n! is strictly positive. This does NOT infer nonzero signed
physical moment coefficients after pairing with rho. -/
theorem p4Q2NL_originalWilsonTemporalTaylorCoefficient_pos
    (b : ℝ) (hb : 0 < b) (n : ℕ) :
    0 < b ^ n / (n.factorial : ℝ) := by
  positivity

section AuthenticSignedMoments
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "mu" => normalizedCompactHaar Gauge
local notation "rho" => p4Q2NG_originalSpatialPerronSignedContrast H b hb
local notation "T" => p4Q2NG_originalTemporalSU2CharacterMoment H b hb
local notation "L" => p4Q2NJ_originalSignedHaarIntegralCLM H b hb
include hb

/-- The actual signed Wilson temporal character moment is EXACTLY the
already constructed ORIGINAL NJ bounded Haar functional evaluated on
the true Wilson exponential section, not a synthetic score. -/
theorem p4Q2NL_originalSignedMoment_eq_signedCLM_kernel
    (e : Link) (z : Cfg × Cfg) (x : Gauge) :
    T e z x = L e z (p4Q2NJ_originalSU2WilsonTemporalSection b x) := by
  change
    (∫ g : Gauge,
      Real.exp (b * p4Q2NG_originalSU2TemporalCharacter x g) *
        rho e z g ∂mu) =
      (∫ g : Gauge,
        Real.exp (b * p4Q2NG_originalSU2TemporalCharacter x g) *
          rho e z g ∂mu)
  rfl

/-- MAIN genuine original Wilson–Perron signed-moment Banach Taylor
identity: mathlib maps the sup-norm HasSum in C(SU2,R) through NJ's
bounded signed Haar functional. This rigorously justifies the complete
signed moment series without changing either interacting Wilson
posterior law, Perron factor or actual SU(2) integration. -/
theorem p4Q2NL_originalSignedTemporalMoment_BanachPower_hasSum
    (e : Link) (z : Cfg × Cfg) (x : Gauge) :
    HasSum
      (fun n : ℕ =>
        L e z
          ((n !⁻¹ : ℝ) •
            (b • p4Q2NL_originalTemporalCharacterContinuous x) ^ n))
      (T e z x) := by
  have hSeries :=
    p4Q2NL_originalWilsonTemporalSection_Banach_hasSum b x
  have hMapped :=
    hSeries.map (L e z) (L e z).continuous
  rw [p4Q2NL_originalSignedMoment_eq_signedCLM_kernel H b hb e z x]
  exact hMapped

/-- The same original signed Wilson moment has an actual convergent
real tsum of its genuine Banach polynomial power coefficients. -/
theorem p4Q2NL_originalSignedTemporalMoment_BanachPower_tsum
    (e : Link) (z : Cfg × Cfg) (x : Gauge) :
    T e z x =
      ∑' n : ℕ,
        L e z
          ((n !⁻¹ : ℝ) •
            (b • p4Q2NL_originalTemporalCharacterContinuous x) ^ n) := by
  exact (p4Q2NL_originalSignedTemporalMoment_BanachPower_hasSum
    H b hb e z x).tsum_eq.symm

end AuthenticSignedMoments
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NL_originalWilsonTemporalSection_eq_BanachExp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NL_originalWilsonTemporalSection_Banach_hasSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NL_originalWilsonTemporalSection_Banach_summable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NL_originalWilsonTemporalTaylorCoefficient_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NL_originalSignedMoment_eq_signedCLM_kernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NL_originalSignedTemporalMoment_BanachPower_hasSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NL_originalSignedTemporalMoment_BanachPower_tsum
