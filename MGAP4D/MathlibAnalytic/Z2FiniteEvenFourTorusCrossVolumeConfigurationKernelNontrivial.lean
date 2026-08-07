import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeBetaZeroFiberMultiplicityCriterion
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusAllVolumeGaugeOrbitWitness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The canonical doubled periodic coordinate projection cannot be injective:
its finite domain has exactly twice the cardinality of its target. -/
theorem finiteEvenFourTorusCoordinateCoarseHom_not_injective
    (H : ℕ) :
    ¬ Function.Injective (finiteEvenFourTorusCoordinateCoarseHom H) := by
  intro hInjective
  have hcard := Fintype.card_le_of_injective
    (finiteEvenFourTorusCoordinateCoarseHom H) hInjective
  simp only [ZMod.card] at hcard
  rw [finiteEvenFourTorusDoubleRefinement_side] at hcard
  omega

/-- Hence there are two distinct fine periodic coordinates with the same
coarse coordinate. -/
theorem finiteEvenFourTorusCoordinateCoarseHom_exists_collision
    (H : ℕ) :
    ∃ x y : ZMod ((2 * finiteEvenFourTorusDoubleRefinement H + 1) + 1),
      x ≠ y ∧ finiteEvenFourTorusCoordinateCoarseHom H x =
        finiteEvenFourTorusCoordinateCoarseHom H y := by
  by_contra hExists
  apply finiteEvenFourTorusCoordinateCoarseHom_not_injective H
  intro x y hxy
  by_contra hne
  exact hExists ⟨x, y, hne, hxy⟩

/-- A single fine-link excitation coarse-grains to the corresponding single
coarse-link excitation. -/
theorem finiteEvenFourTorusZ2SliceConfigurationCoarseMap_singleLinkExcitation
    (H : ℕ)
    (e₀ : FiniteEvenFourTorusSpatialLink
      (finiteEvenFourTorusDoubleRefinement H)) :
    finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
        (finiteEvenFourTorusZ2SingleLinkExcitation
          (finiteEvenFourTorusDoubleRefinement H) e₀) =
      finiteEvenFourTorusZ2SingleLinkExcitation H
        (finiteEvenFourTorusSpatialLinkCoarseMap H e₀) := by
  classical
  rcases e₀ with ⟨w₀, ν⟩
  funext e
  rcases e with ⟨v, μ⟩
  unfold finiteEvenFourTorusZ2SliceConfigurationCoarseMap
    finiteEvenFourTorusZ2SingleLinkExcitation
    finiteEvenFourTorusSpatialLinkCoarseMap
  by_cases hdir : μ = ν
  · subst μ
    by_cases hcv : finiteEvenFourTorusSpatialVertexCoarseMap H w₀ = v
    · rw [Fintype.prod_eq_single w₀]
      · simp [hcv]
      · intro w hw
        by_cases hwv : finiteEvenFourTorusSpatialVertexCoarseMap H w = v
        · have hww : w ≠ w₀ := hw
          simp [hwv, hww]
        · simp [hwv]
    · have hprod :
        (∏ w : FiniteEvenFourTorusSpatialVertex
            (finiteEvenFourTorusDoubleRefinement H),
          if finiteEvenFourTorusSpatialVertexCoarseMap H w = v then
            (if (w, ν) = (w₀, ν) then z2GaugeNontrivial else 1)
          else 1) = 1 := by
        apply Finset.prod_eq_one
        intro w _hw
        by_cases hwv : finiteEvenFourTorusSpatialVertexCoarseMap H w = v
        · have hww : w ≠ w₀ := by
            intro h
            subst w
            exact hcv hwv
          simp [hwv, hww]
        · simp [hwv]
      rw [hprod]
      have hlink :
          (v, ν) ≠
            (finiteEvenFourTorusSpatialVertexCoarseMap H w₀, ν) := by
        intro h
        exact hcv (congrArg Prod.fst h).symm
      rw [if_neg hlink]
  · have hprod :
      (∏ w : FiniteEvenFourTorusSpatialVertex
          (finiteEvenFourTorusDoubleRefinement H),
        if finiteEvenFourTorusSpatialVertexCoarseMap H w = v then
          (if (w, μ) = (w₀, ν) then z2GaugeNontrivial else 1)
        else 1) = 1 := by
      apply Finset.prod_eq_one
      intro w _hw
      by_cases hwv : finiteEvenFourTorusSpatialVertexCoarseMap H w = v
      · have hpair : (w, μ) ≠ (w₀, ν) := by
          intro h
          exact hdir (congrArg Prod.snd h)
        simp [hwv, hpair]
      · simp [hwv]
    rw [hprod]
    simp [hdir]

/-- The nontrivial element of `Z₂` squares to the identity. -/
theorem z2GaugeNontrivial_mul_self :
    z2GaugeNontrivial * z2GaugeNontrivial = (1 : Z2Gauge) := by
  native_decide

/-- The actual doubled-torus configuration coarse hom has a nontrivial kernel
at every finite side parameter. -/
noncomputable instance finiteEvenFourTorusZ2SliceConfigurationCoarseHomKerNontrivial
    (H : ℕ) :
    Nontrivial (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker := by
  classical
  rcases finiteEvenFourTorusCoordinateCoarseHom_exists_collision H with
    ⟨x, y, hxy, hmapxy⟩
  let ix : Fin 4 := 1
  let vx : FiniteEvenFourTorusSpatialVertex
      (finiteEvenFourTorusDoubleRefinement H) :=
    ⟨fun i => if i = ix then x else 0, by simp [ix]⟩
  let vy : FiniteEvenFourTorusSpatialVertex
      (finiteEvenFourTorusDoubleRefinement H) :=
    ⟨fun i => if i = ix then y else 0, by simp [ix]⟩
  have hvxy : vx ≠ vy := by
    intro h
    apply hxy
    have hcoord := congrArg
      (fun v : FiniteEvenFourTorusSpatialVertex
          (finiteEvenFourTorusDoubleRefinement H) => v.1 ix) h
    simpa [vx, vy] using hcoord
  have hvmap :
      finiteEvenFourTorusSpatialVertexCoarseMap H vx =
        finiteEvenFourTorusSpatialVertexCoarseMap H vy := by
    apply Subtype.ext
    funext i
    by_cases hi : i = ix
    · subst i
      simpa [finiteEvenFourTorusSpatialVertexCoarseMap_apply, vx, vy] using hmapxy
    · simp [finiteEvenFourTorusSpatialVertexCoarseMap_apply, vx, vy, hi]
  let μ := finiteEvenFourTorusZ2GaussWitnessDirectionOne
  let e₁ : FiniteEvenFourTorusSpatialLink
      (finiteEvenFourTorusDoubleRefinement H) := (vx, μ)
  let e₂ : FiniteEvenFourTorusSpatialLink
      (finiteEvenFourTorusDoubleRefinement H) := (vy, μ)
  have he12 : e₁ ≠ e₂ := by
    intro h
    apply hvxy
    exact congrArg Prod.fst h
  have hemap :
      finiteEvenFourTorusSpatialLinkCoarseMap H e₁ =
        finiteEvenFourTorusSpatialLinkCoarseMap H e₂ := by
    simp [e₁, e₂, hvmap]
  let A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H) :=
    finiteEvenFourTorusZ2SingleLinkExcitation
        (finiteEvenFourTorusDoubleRefinement H) e₁ *
      finiteEvenFourTorusZ2SingleLinkExcitation
        (finiteEvenFourTorusDoubleRefinement H) e₂
  have hAmap :
      finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A = 1 := by
    unfold A
    rw [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_mul]
    rw [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_singleLinkExcitation,
      finiteEvenFourTorusZ2SliceConfigurationCoarseMap_singleLinkExcitation,
      hemap]
    funext e
    unfold finiteEvenFourTorusZ2SingleLinkExcitation
    by_cases he : e = finiteEvenFourTorusSpatialLinkCoarseMap H e₂
    · simp [he, z2GaugeNontrivial_mul_self]
    · have he' :
          e ≠
            (finiteEvenFourTorusSpatialVertexCoarseMap H e₂.1, e₂.2) := by
        simpa [finiteEvenFourTorusSpatialLinkCoarseMap] using he
      rw [if_neg he', if_neg he']
  have hAne : A ≠ 1 := by
    intro h
    have heval := congrArg
      (fun B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H) => B e₁) h
    change
      finiteEvenFourTorusZ2SingleLinkExcitation
          (finiteEvenFourTorusDoubleRefinement H) e₁ e₁ *
        finiteEvenFourTorusZ2SingleLinkExcitation
          (finiteEvenFourTorusDoubleRefinement H) e₂ e₁ = 1 at heval
    simp [finiteEvenFourTorusZ2SingleLinkExcitation, he12] at heval
    exact (by native_decide : z2GaugeNontrivial ≠ (1 : Z2Gauge)) heval
  let k : (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker :=
    ⟨A, by simpa using hAmap⟩
  have hk : k ≠ 1 := by
    intro h
    apply hAne
    exact congrArg Subtype.val h
  exact ⟨⟨1, k, hk.symm⟩⟩

/-- Therefore the configuration coarse-hom kernel cardinality is strictly
larger than one at every finite side parameter. -/
theorem finiteEvenFourTorusZ2SliceConfigurationCoarseHom_card_ker_gt_one
    (H : ℕ) :
    1 < Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker := by
  exact Fintype.one_lt_card

/-- In particular, the actual configuration coarse hom never has singleton
kernel. -/
theorem finiteEvenFourTorusZ2SliceConfigurationCoarseHom_card_ker_ne_one
    (H : ℕ) :
    Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker ≠ 1 :=
  ne_of_gt (finiteEvenFourTorusZ2SliceConfigurationCoarseHom_card_ker_gt_one H)

/-- The `β = 0` one-step Boltzmann orbit-fibre balance is genuinely false at
every finite side parameter. -/
theorem finiteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance_beta_zero_false
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    ¬ FiniteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy := by
  intro hBalance
  have hker :=
    (finiteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance_beta_zero_iff_card_ker_eq_one
      H energyIdentity energyNontrivial hEnergy).1 hBalance
  exact finiteEvenFourTorusZ2SliceConfigurationCoarseHom_card_ker_ne_one H hker

/-- Main Package-K obstruction theorem: at `β = 0`, the actual one-step raw
cross-volume transfer residual is nonzero for every finite side parameter and
for every ordered pair of plaquette energies. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_beta_zero_ne_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy ≠ 0 := by
  intro hZero
  have hker :=
    (finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_beta_zero_eq_zero_iff_card_ker_eq_one
      H energyIdentity energyNontrivial hEnergy).1 hZero
  exact finiteEvenFourTorusZ2SliceConfigurationCoarseHom_card_ker_ne_one H hker

end

end MathlibAnalytic
end MGAP4D
