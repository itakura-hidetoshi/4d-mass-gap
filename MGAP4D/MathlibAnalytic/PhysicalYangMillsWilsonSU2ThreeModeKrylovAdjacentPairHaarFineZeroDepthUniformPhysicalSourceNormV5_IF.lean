import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarDepthZeroPhysicalSourceNormCoercivityV5_IE
import Mathlib.Tactic

/-!
# P4-Q2-IF: all-depth original Wilson physical-source norm comparison at fine beta=0

IE proves the exact genuine Haar-L² source Gram quadratic identity
  aᵀ Qsrc a = ‖S(a)‖²
at arbitrary depth and any fine beta; and for physical Krylov depth
r=0, original two-interacting-Wilson-posterior GL mass is comparable
with the ORIGINAL physical source squared norm by positive finite-
volume constants 0<c<=C at positive FROZEN beta(n)>0.

HA (and the underlying actual fine-beta-zero transfer theorem) proves
that when the distinct FINE beta(n+1)=0, all physical fine-right
Krylov source modes equal the same true constant-unit source v0.
Consequently EVERY signed depth-r physical source is the exact
one-mode physical source whose sole coefficient is sum_j a_j.
This is an identity in the actual gauge-invariant Haar-L² submodule,
not a surrogate scalar source or an equality of distinct Grams.

Applying IE's depth-zero true physical-source-norm comparison to this
single shared source gives *THE SAME* positive constants c,C for
ALL FINITE Krylov DEPTHS r simultaneously at fixed n and true finite
Wilson model:
  c‖S_r(a)‖² <= Original GL mass(S_r(a)) <= C‖S_r(a)‖².
The lower bound is strictly positive for nonzero PHYSICAL sources,
but NOT for all nonzero coefficient vectors: sum(a)=0 is an actual
rank-collapse kernel.

This is a genuine depth-uniform PHYSICAL source-norm bound only at
fine beta(n+1)=0. It is neither uniform in physical volume, lattice
spacing, frozen beta, continuum scale, nor a result for positive fine
beta(n+1) with r>0. No Dobrushin assumption, independent Haar
conditional, H1-C3 or continuum 4D Yang--Mills gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 950000

local instance p4Q2IF_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IF_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IF_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IF_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IF_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2IF_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section TrueFineZero

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- At the actual fine-beta-zero endpoint, the full depth-r signed
gauge-invariant physical source is IDENTICAL to a depth-zero physical
source whose one coefficient is the true sum of all r+1 entries.
The right source lives in the original physical Haar-L² submodule. -/
theorem p4Q2IF_fineZero_actualRight_source_eq_oneMode_sum
    (hFineZero : beta (n + 1) = 0)
    (r : ℕ) (a : Fin (r + 1) → ℝ) :
    (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) =
      (∑ j : Fin (0 + 1),
        (fun _ : Fin (0 + 1) => ∑ k : Fin (r + 1), a k) j •
          RightFactor n (j : ℕ)) := by
  let t : ℝ := ∑ j : Fin (r + 1), a j
  have hCollapse :=
    p4Q2HA_fineZero_actualSource_eq_sum_smul
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFineZero a
  have hOne :
      (∑ j : Fin (0 + 1),
        (fun _ : Fin (0 + 1) => t) j • RightFactor n (j : ℕ)) =
          t • RightFactor n 0 := by
    change (∑ j : Fin 1,
      t • RightFactor n (j : ℕ)) = t • RightFactor n 0
    simp only [Fin.sum_univ_one, Fin.val_zero]
  calc
    (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) =
        t • RightFactor n 0 := hCollapse
    _ = (∑ j : Fin (0 + 1),
      (fun _ : Fin (0 + 1) => ∑ k : Fin (r + 1), a k) j •
        RightFactor n (j : ℕ)) := by
      simpa only [t] using hOne.symm

/-- The positive finite-model lower/upper constants obtained for the
genuine one-mode original Wilson GL mass apply AT ONCE to all
physical Krylov depths when the fine coupling is exactly zero.
This is an explicit quantifier-level depth-uniformity result, not a
coefficient-space lower frame or any continuum-uniform bound. -/
theorem p4Q2IF_fineZero_originalWilsonGLMass_depthUniform_physicalNorm
    (hFrozen : 0 < beta n) (hFineZero : beta (n + 1) = 0)
    (right : Cfg) (e : Link) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ (r : ℕ) (a : Fin (r + 1) → ℝ),
        c * ‖∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)‖ ^ 2 ≤
          p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
            Hn (beta n) (hbeta n)
            (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
            (Finset.univ : Finset Link) ∧
          p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
            Hn (beta n) (hbeta n)
            (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
            (Finset.univ : Finset Link) ≤
          C * ‖∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)‖ ^ 2 := by
  obtain ⟨c, C, hc, hcC, hDepthZero⟩ :=
    p4Q2IE_depthZero_originalWilsonGLMass_physicalSourceNorm_fixed_comparison
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  refine ⟨c, C, hc, hcC, ?_⟩
  intro r a
  let b : Fin (0 + 1) → ℝ :=
    fun _ => ∑ j : Fin (r + 1), a j
  have hSameSource :
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) =
        (∑ j : Fin (0 + 1), b j • RightFactor n (j : ℕ)) := by
    exact p4Q2IF_fineZero_actualRight_source_eq_oneMode_sum
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFineZero r a
  rw [hSameSource]
  exact hDepthZero b

end TrueFineZero
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IF_fineZero_actualRight_source_eq_oneMode_sum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IF_fineZero_originalWilsonGLMass_depthUniform_physicalNorm
