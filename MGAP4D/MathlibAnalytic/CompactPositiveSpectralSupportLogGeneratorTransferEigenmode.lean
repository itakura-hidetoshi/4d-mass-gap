import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGenerator
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace lp LinearPMap

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- The logarithmic energy separates the strictly-positive support eigenvalues.
This is the scalar rigidity behind the equivalence between a single mode of
`-log T` and a single mode of `T`. -/
theorem realHilbertZeroEigenspaceSupportLogEnergy_injective
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive) :
    Function.Injective (realHilbertZeroEigenspaceSupportLogEnergy T hPositive) := by
  intro mu nu hEnergy
  apply Subtype.ext
  calc
    (mu : ℝ) = Real.exp (- realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu) :=
      (realHilbertZeroEigenspaceSupportLogEnergy_exp_neg_eq T hPositive mu).symm
    _ = Real.exp (- realHilbertZeroEigenspaceSupportLogEnergy T hPositive nu) := by
      rw [hEnergy]
    _ = (nu : ℝ) :=
      realHilbertZeroEigenspaceSupportLogEnergy_exp_neg_eq T hPositive nu

/-- A genuine actual-domain eigenmode of the support logarithmic generator is
an eigenmode of the bounded support restriction of the original compact
positive transfer.  The eigenvalues are related by the exact exponential law
`tau = exp (-rho)`. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_domain_eigenmode_to_transfer_eigenmode
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (v : realHilbertZeroEigenspaceSupport T)
    (hv : v ≠ 0)
    (rho : ℝ)
    (x : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain)
    (hxv : (x : realHilbertZeroEigenspaceSupport T) = v)
    (hAx : realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x = rho • v) :
    realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric v =
      Real.exp (-rho) • v := by
  classical
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let A := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
  have hCoord :
      realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates T hCompact hPositive
          ⟨U (x : realHilbertZeroEigenspaceSupport T), x.property⟩ =
        rho • U v := by
    calc
      realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates T hCompact hPositive
          ⟨U (x : realHilbertZeroEigenspaceSupport T), x.property⟩ =
        U (A x) := by
          simpa [U, A] using
            (realHilbertCompactPositiveZeroSupportLogGenerator_coordinates
              T hCompact hPositive x).symm
      _ = U (rho • v) := by rw [hAx]
      _ = rho • U v := by exact U.map_smul rho v
  have hComponent : ∀ mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
      realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • (U v) mu =
        rho • (U v) mu := by
    intro mu
    have h := congrArg (fun y => y mu) hCoord
    simpa [
      realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_apply,
      hxv] using h
  have hEnergyOfNe : ∀ mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
      (U v) mu ≠ 0 →
        realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu = rho := by
    intro mu hmu
    exact smul_left_injective ℝ hmu (hComponent mu)
  have hUvNe : U v ≠ 0 := by
    intro hzero
    apply hv
    apply U.injective
    simpa using hzero
  have hExists : ∃ mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
      (U v) mu ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hUvNe
    apply lp.ext
    funext mu
    simpa using hnone mu
  rcases hExists with ⟨mu, hmu⟩
  have hEnergyMu : realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu = rho :=
    hEnergyOfNe mu hmu
  have hZeroAway : ∀ nu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
      nu ≠ mu → (U v) nu = 0 := by
    intro nu hne
    by_contra hnu
    have hEnergyNu := hEnergyOfNe nu hnu
    have hEq : nu = mu :=
      realHilbertZeroEigenspaceSupportLogEnergy_injective T hPositive
        (hEnergyNu.trans hEnergyMu.symm)
    exact hne hEq
  have hSingle : U v =
      lp.single
        (E := fun nu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
          eigenspace
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) nu)
        2 mu ((U v) mu) := by
    apply lp.ext
    funext nu
    by_cases hnu : nu = mu
    · subst nu
      exact
        (lp.single_apply_self
          (E := fun nu : Eigenvalues
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
            eigenspace
              (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                Module.End ℝ (realHilbertZeroEigenspaceSupport T)) nu)
          2 mu ((U v) mu)).symm
    · calc
        (U v) nu = 0 := hZeroAway nu hnu
        _ = (lp.single
          (E := fun eta : Eigenvalues
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
            eigenspace
              (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                Module.End ℝ (realHilbertZeroEigenspaceSupport T)) eta)
          2 mu ((U v) mu)) nu :=
            (lp.single_apply_ne
              (E := fun eta : Eigenvalues
                (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                  Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
                eigenspace
                  (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                    Module.End ℝ (realHilbertZeroEigenspaceSupport T)) eta)
              2 mu ((U v) mu) hnu).symm
  have hReconstruct :
      (((U v) mu : eigenspace
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu) :
        realHilbertZeroEigenspaceSupport T) = v := by
    calc
      (((U v) mu : eigenspace
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu) :
        realHilbertZeroEigenspaceSupport T) =
          U.symm
            (lp.single
              (E := fun nu : Eigenvalues
                (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                  Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
                eigenspace
                  (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                    Module.End ℝ (realHilbertZeroEigenspaceSupport T)) nu)
              2 mu ((U v) mu)) := by
            simpa [U] using
              (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv_symm_single
                T hCompact hPositive mu ((U v) mu)).symm
      _ = U.symm (U v) := congrArg U.symm hSingle.symm
      _ = v := U.symm_apply_apply v
  rw [← hReconstruct]
  calc
    realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric
        (((U v) mu : eigenspace
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu) :
          realHilbertZeroEigenspaceSupport T) =
      (mu : ℝ) • (((U v) mu : eigenspace
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu) :
        realHilbertZeroEigenspaceSupport T) :=
      mem_eigenspace_iff.mp ((U v) mu).property
    _ = Real.exp (- realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu) •
        (((U v) mu : eigenspace
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu) :
          realHilbertZeroEigenspaceSupport T) := by
      rw [realHilbertZeroEigenspaceSupportLogEnergy_exp_neg_eq T hPositive mu]
    _ = Real.exp (-rho) •
        (((U v) mu : eigenspace
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu) :
          realHilbertZeroEigenspaceSupport T) := by
      rw [hEnergyMu]

/-- Conversely, a nonzero eigenmode of the bounded support restriction is in
the true maximal domain of the support logarithmic generator and is an
actual-domain generator eigenmode.  Positivity of the transfer eigenvalue is
derived from the positive spectral-support construction, and the generator
eigenvalue is exactly `-log tau`. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_transfer_eigenmode_to_domain_eigenmode
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (v : realHilbertZeroEigenspaceSupport T)
    (hv : v ≠ 0)
    (tau : ℝ)
    (hTv : realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric v = tau • v) :
    0 < tau ∧
      ∃ x : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain,
        (x : realHilbertZeroEigenspaceSupport T) = v ∧
          realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x =
            (-Real.log tau) • v := by
  classical
  have hvEig : v ∈ eigenspace
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) tau := by
    exact mem_eigenspace_iff.mpr hTv
  have hvEigenvector : HasEigenvector
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) tau v := ⟨hvEig, hv⟩
  have hTauEigenvalue : HasEigenvalue
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) tau :=
    hasEigenvalue_of_hasEigenvector hvEigenvector
  let mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) :=
    ⟨tau, hTauEigenvalue⟩
  have hTauPos : 0 < tau := by
    simpa [mu] using
      (realHilbertZeroEigenspaceSupportRestriction_eigenvalue_pos T hPositive mu)
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let y : eigenspace
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu :=
    ⟨v, by simpa [mu] using hvEig⟩
  let s :=
    lp.single
      (E := fun nu : Eigenvalues
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
        eigenspace
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) nu)
      2 mu y
  have hSymmSingle : U.symm s = v := by
    simpa [U, s, y] using
      (realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv_symm_single
        T hCompact hPositive mu y)
  have hUv : U v = s := by
    rw [← hSymmSingle]
    exact U.apply_symm_apply _
  have hWeightedSingle :
      Memℓp
        (fun nu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
          realHilbertZeroEigenspaceSupportLogEnergy T hPositive nu • s nu)
        2 := by
    let z :=
      lp.single
        (E := fun nu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
          eigenspace
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) nu)
        2 mu (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • y)
    have hz : Memℓp (fun nu => z nu) 2 := z.property
    have hfun :
        (fun nu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
          realHilbertZeroEigenspaceSupportLogEnergy T hPositive nu • s nu) =
        (fun nu => z nu) := by
      funext nu
      by_cases hnu : nu = mu
      · subst nu
        simp only [s, z, lp.single_apply_self]
      · have hs0 : s nu = 0 := by
          dsimp [s]
          exact lp.single_apply_ne
            (E := fun eta : Eigenvalues
              (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
              eigenspace
                (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                  Module.End ℝ (realHilbertZeroEigenspaceSupport T)) eta)
            2 mu y hnu
        have hz0 : z nu = 0 := by
          dsimp [z]
          exact lp.single_apply_ne
            (E := fun eta : Eigenvalues
              (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
              eigenspace
                (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                  Module.End ℝ (realHilbertZeroEigenspaceSupport T)) eta)
            2 mu (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • y) hnu
        rw [hs0, hz0, smul_zero]
    rw [hfun]
    exact hz
  have hUvDomain :
      U v ∈
        (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
          T hCompact hPositive).domain := by
    exact
      (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_domain_mem_iff
        T hCompact hPositive (U v)).mpr
        (by simpa only [hUv] using hWeightedSingle)
  have hvDomain :
      v ∈ realHilbertCompactPositiveZeroSupportLogGeneratorDomain T hCompact hPositive := by
    exact
      (mem_realHilbertCompactPositiveZeroSupportLogGeneratorDomain
        T hCompact hPositive v).mpr (by simpa [U] using hUvDomain)
  let x : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain :=
    ⟨v, by simpa using hvDomain⟩
  have hCoordinateAction :
      realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates T hCompact hPositive
          ⟨U v, hUvDomain⟩ =
        realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • U v := by
    apply lp.ext
    funext nu
    rw [realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_apply]
    simp only [lp.coeFn_smul, Pi.smul_apply]
    by_cases hnu : nu = mu
    · subst nu
      rfl
    · have hs0 : s nu = 0 := by
        dsimp [s]
        exact lp.single_apply_ne
          (E := fun eta : Eigenvalues
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
            eigenspace
              (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                Module.End ℝ (realHilbertZeroEigenspaceSupport T)) eta)
          2 mu y hnu
      have huv0 : (U v) nu = 0 := by
        calc
          (U v) nu = s nu := congrArg (fun q => q nu) hUv
          _ = 0 := hs0
      simp only [huv0, smul_zero]
  have hAxEnergy :
      realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x =
        realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • v := by
    apply U.injective
    calc
      U (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x) =
          realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates T hCompact hPositive
            ⟨U (x : realHilbertZeroEigenspaceSupport T), x.property⟩ :=
        realHilbertCompactPositiveZeroSupportLogGenerator_coordinates
          T hCompact hPositive x
      _ = realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates T hCompact hPositive
            ⟨U v, hUvDomain⟩ := by rfl
      _ = realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • U v :=
        hCoordinateAction
      _ = U (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • v) := by
        rw [U.map_smul]
  refine ⟨hTauPos, x, rfl, ?_⟩
  simpa [realHilbertZeroEigenspaceSupportLogEnergy, mu] using hAxEnergy

/-- For a nonzero state on the strictly-positive support, being a genuine
actual-domain eigenmode of the logarithmic generator is equivalent to being a
strictly-positive eigenmode of the original bounded transfer restriction. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_domain_eigenmode_iff_transfer_eigenmode
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (v : realHilbertZeroEigenspaceSupport T)
    (hv : v ≠ 0) :
    (∃ rho : ℝ,
      ∃ x : (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive).domain,
        (x : realHilbertZeroEigenspaceSupport T) = v ∧
          realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive x = rho • v) ↔
    ∃ tau : ℝ, 0 < tau ∧
      realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric v = tau • v := by
  constructor
  · rintro ⟨rho, x, hxv, hAx⟩
    exact ⟨Real.exp (-rho), Real.exp_pos _,
      realHilbertCompactPositiveZeroSupportLogGenerator_domain_eigenmode_to_transfer_eigenmode
        T hCompact hPositive v hv rho x hxv hAx⟩
  · rintro ⟨tau, _, hTv⟩
    rcases
      realHilbertCompactPositiveZeroSupportLogGenerator_transfer_eigenmode_to_domain_eigenmode
        T hCompact hPositive v hv tau hTv with
      ⟨_, x, hxv, hAx⟩
    exact ⟨-Real.log tau, x, hxv, hAx⟩

end

end MathlibAnalytic
end MGAP4D