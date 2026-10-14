import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryCrossingRightTargetLinkEnergyVariation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetActionVariation
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonCrossingKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRepresentative
import Mathlib.Tactic

/-!
# P4-Q2-FO: exact original Wilson selected temporal-link factorization

Fix the true finite-volume SU(N) Wilson one-slab kernel K_beta(A,B), an
actual physical spatial link e, and an arbitrary updated right link g.

Let k_beta(A_e,g) be the ORIGINAL temporal crossing plaquette Wilson
relative kernel; let s_beta(B) be the ORIGINAL spatial half weight.
The exact one-slab action increment is

  T(A,B[e<-g]) - T(A,B)
    = E_W(A_e^{-1} g) - E_W(A_e^{-1} B_e)
        + (A_sp(B[e<-g]) - A_sp(B))/2.

Exponentiating gives, with NO approximation or conditional independence,

  K(A,B[e<-g]) * (k(A_e,B_e) * s(B))
    = K(A,B) * (k(A_e,g) * s(B[e<-g])).

Since every factor in the denominator is positive, define the genuine
off-link coefficient C(A,B,e) := K(A,B) / (k(A_e,B_e) * s(B)).
Then C is positive and INDEPENDENT of the inserted right link value g:

  K(A,B[e<-g]) = C(A,B,e) * k(A_e,g) * s(B[e<-g]).

Multiplying by the canonical continuous physical Perron vacuum yields
the exact product with the true right environment weight s(Bg)*Omega(Bg).
This directly prepares the genuine posterior left-link Haar translation
argument, without introducing a surrogate Wilson kernel, axiom, sorry,
spatial decay or a continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 700000

/-- The exact multiplicative four-term Wilson identity when ONLY the
selected original right spatial link is updated. Crucially the crossed
temporal Wilson factor k(A_e,g) is NOT bounded away or discarded. -/
theorem p4Q2FO_originalWilsonSelectedRightLink_crossMul_identity
    (H N : ℕ) (beta : ℝ)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
        left (Function.update right e g) *
      (specialUnitaryWilsonRelativeKernel N beta (left e) (right e) *
        periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta right) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
        left right *
      (specialUnitaryWilsonRelativeKernel N beta (left e) g *
        periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta
          (Function.update right e g)) := by
  let Bg := Function.update right e g
  let T := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N
  let S := periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
  let Eg : ℝ := specialUnitaryWilsonPlaquetteEnergy N ((left e)⁻¹ * g)
  let E0 : ℝ := specialUnitaryWilsonPlaquetteEnergy N ((left e)⁻¹ * right e)
  have hAction :
      T left Bg - T left right =
        (Eg - E0) + (1 / 2 : ℝ) * (S Bg - S right) := by
    calc
      T left Bg - T left right =
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
              H N left Bg -
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
              H N left right) +
          (1 / 2 : ℝ) * (S Bg - S right) :=
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_update_right_sub_eq
          H N left right e g
      _ = (Eg - E0) + (1 / 2 : ℝ) * (S Bg - S right) := by
        rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_update_right_sub_eq]
  have hActionScaled := congrArg (fun t : ℝ => beta * t) hAction
  have hExponent :
      (-beta * T left Bg) +
          ((-beta * E0) + (-(beta / 2) * S right)) =
        (-beta * T left right) +
          ((-beta * Eg) + (-(beta / 2) * S Bg)) := by
    nlinarith [hActionScaled]
  have hExp :
      Real.exp (-beta * T left Bg) *
          (Real.exp (-beta * E0) * Real.exp (-(beta / 2) * S right)) =
        Real.exp (-beta * T left right) *
          (Real.exp (-beta * Eg) * Real.exp (-(beta / 2) * S Bg)) := by
    calc
      Real.exp (-beta * T left Bg) *
          (Real.exp (-beta * E0) * Real.exp (-(beta / 2) * S right)) =
        Real.exp
          ((-beta * T left Bg) + ((-beta * E0) + (-(beta / 2) * S right))) := by
          rw [Real.exp_add, Real.exp_add]
      _ = Real.exp
          ((-beta * T left right) + ((-beta * Eg) + (-(beta / 2) * S Bg))) :=
        congrArg Real.exp hExponent
      _ = Real.exp (-beta * T left right) *
          (Real.exp (-beta * Eg) * Real.exp (-(beta / 2) * S Bg)) := by
          rw [Real.exp_add, Real.exp_add]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  change
    Real.exp (-beta * T left Bg) *
      (Real.exp (-beta * E0) * Real.exp (-(beta / 2) * S right)) =
    Real.exp (-beta * T left right) *
      (Real.exp (-beta * Eg) * Real.exp (-(beta / 2) * S Bg))
  exact hExp

/-- Exact strictly positive coefficient collecting ALL physical factors
of the one-slab Wilson kernel that are independent of the updated value
of the selected right link. NO new choice of law or normalization. -/
noncomputable def p4Q2FO_originalWilsonOffLinkKernelCoefficient
    (H N : ℕ) (beta : ℝ)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta left right /
    (specialUnitaryWilsonRelativeKernel N beta (left e) (right e) *
      periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta right)

theorem p4Q2FO_originalWilsonOffLinkKernelCoefficient_pos
    (H N : ℕ) (beta : ℝ)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 < p4Q2FO_originalWilsonOffLinkKernelCoefficient
      H N beta left right e := by
  unfold p4Q2FO_originalWilsonOffLinkKernelCoefficient
  have hK :
      0 < periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta left right :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta left right
  have hk :
      0 < specialUnitaryWilsonRelativeKernel N beta (left e) (right e) := by
    unfold specialUnitaryWilsonRelativeKernel
      specialUnitaryWilsonBoltzmannCentralFunction
    exact Real.exp_pos _
  have hs :
      0 < periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
        H N beta right :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos
      H N beta right
  exact div_pos hK (mul_pos hk hs)

/-- Literal selected-link factorization of the ACTUAL SU(N) one-slab
kernel. The coefficient does not depend on the newly inserted link g. -/
theorem p4Q2FO_originalWilsonSelectedRightLink_exactFactor
    (H N : ℕ) (beta : ℝ)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
        left (Function.update right e g) =
      p4Q2FO_originalWilsonOffLinkKernelCoefficient H N beta left right e *
        (specialUnitaryWilsonRelativeKernel N beta (left e) g *
          periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
            H N beta (Function.update right e g)) := by
  let Kb := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
    H N beta left right
  let Kg := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
    H N beta left (Function.update right e g)
  let k0 := specialUnitaryWilsonRelativeKernel N beta (left e) (right e)
  let kg := specialUnitaryWilsonRelativeKernel N beta (left e) g
  let sb := periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta right
  let sg := periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
    H N beta (Function.update right e g)
  have hden : k0 * sb ≠ 0 := by
    have hk : 0 < k0 := by
      unfold k0 specialUnitaryWilsonRelativeKernel
        specialUnitaryWilsonBoltzmannCentralFunction
      exact Real.exp_pos _
    have hs : 0 < sb := by
      exact periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos
        H N beta right
    exact (mul_pos hk hs).ne'
  have hCross : Kg * (k0 * sb) = Kb * (kg * sg) :=
    p4Q2FO_originalWilsonSelectedRightLink_crossMul_identity
      H N beta left right e g
  have hDiv : Kg = (Kb * (kg * sg)) / (k0 * sb) := by
    apply (eq_div_iff hden).2
    exact hCross
  calc
    Kg = (Kb * (kg * sg)) / (k0 * sb) := hDiv
    _ = (Kb / (k0 * sb)) * (kg * sg) := by ring
    _ = p4Q2FO_originalWilsonOffLinkKernelCoefficient
        H N beta left right e * (kg * sg) := rfl

/-- Multiplying the exact factorization by the ACTUAL continuous physical
Perron vacuum retains the original environment s_beta(Bg)*Omega_beta(Bg)
and the original temporal one-link Wilson kernel k_beta(Ae,g). -/
theorem p4Q2FO_originalWilsonSelectedRightLink_vacuumExactFactor
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
        left (Function.update right e g) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta (Function.update right e g) =
      p4Q2FO_originalWilsonOffLinkKernelCoefficient H N beta left right e *
        specialUnitaryWilsonRelativeKernel N beta (left e) g *
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
            H N beta (Function.update right e g) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta (Function.update right e g)) := by
  rw [p4Q2FO_originalWilsonSelectedRightLink_exactFactor]
  ring

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2FO_originalWilsonSelectedRightLink_crossMul_identity
#print axioms MGAP4D.MathlibAnalytic.p4Q2FO_originalWilsonOffLinkKernelCoefficient_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2FO_originalWilsonSelectedRightLink_exactFactor
#print axioms MGAP4D.MathlibAnalytic.p4Q2FO_originalWilsonSelectedRightLink_vacuumExactFactor
