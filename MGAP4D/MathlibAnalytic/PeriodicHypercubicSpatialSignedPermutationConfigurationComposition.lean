import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpatialSignedPermutationConfiguration

/-!
# Composition law for signed-spatial gauge-configuration pullbacks

The generic signed-spatial configuration pullback is already defined by reading the inverse image of
a positive physical edge as a signed boundary step.  This file proves that these pullbacks compose in
the same order as the abstract signed-permutation group:

`C_{g h}(A) = C_g(C_h(A))`.

The only extra geometric ingredient needed is covariance of a negative unit step.  It is derived from
the already-canonical positive-step covariance together with `shift`/`unshift` cancellation.  The
proof then splits only on the two signs encountered successively along one spatial edge; no new
symmetry premise is introduced.

Finally the pullbacks are packaged as actual permutations of the gauge-configuration carrier and as
a monoid homomorphism from the abstract 48-element signed spatial permutation group.

Plaquette-holonomy covariance, cubic-channel projection, continuum-spin identification, and spectral
or glueball-mass claims remain separate downstream obligations.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The image axis of a product is obtained by successively applying the two spatial permutations. -/
@[simp]
theorem periodicHypercubicSpatialSignedPermutationAxis_mul
    (g h : SpatialSignedPermutationGroup)
    (k : Fin 3) :
    periodicHypercubicSpatialSignedPermutationAxis (g * h) k =
      periodicHypercubicSpatialSignedPermutationAxis g (h.right k) := by
  simp [periodicHypercubicSpatialSignedPermutationAxis, Equiv.Perm.mul_apply]

/-- The sign carried by the final image of `k` under a product is the product of the two successive
image signs. -/
theorem spatialSignedPermutation_mul_imageSign
    (g h : SpatialSignedPermutationGroup)
    (k : Fin 3) :
    (g * h).left ((g * h).right k) =
      g.left (g.right (h.right k)) * h.left (h.right k) := by
  simp [spatialAxisPermutationSignAction_apply, Equiv.Perm.mul_apply, mul_assoc]

/-- A negative spatial unit step remains negative when the image sign is positive. -/
theorem periodicHypercubicVertexSpatialSignedPermutation_unshift_spatial_of_pos
    (n : ℕ)
    (g : SpatialSignedPermutationGroup)
    (x : PeriodicHypercubicVertex n)
    (k : Fin 3)
    (hpos : g.left (g.right k) = 1) :
    periodicHypercubicVertexSpatialSignedPermutation n g
        (periodicHypercubicUnshift n x (Fin.succ k)) =
      periodicHypercubicUnshift n
        (periodicHypercubicVertexSpatialSignedPermutation n g x)
        (periodicHypercubicSpatialSignedPermutationAxis g k) := by
  have h :=
    periodicHypercubicVertexSpatialSignedPermutation_shift_spatial_of_pos
      n g (periodicHypercubicUnshift n x (Fin.succ k)) k hpos
  rw [periodicHypercubicShift_unshift] at h
  have h' := congrArg
    (fun y => periodicHypercubicUnshift n y
      (periodicHypercubicSpatialSignedPermutationAxis g k)) h
  simpa using h'.symm

/-- A negative spatial unit step becomes positive when the image sign is negative. -/
theorem periodicHypercubicVertexSpatialSignedPermutation_unshift_spatial_of_neg
    (n : ℕ)
    (g : SpatialSignedPermutationGroup)
    (x : PeriodicHypercubicVertex n)
    (k : Fin 3)
    (hneg : g.left (g.right k) = (-1 : ℤˣ)) :
    periodicHypercubicVertexSpatialSignedPermutation n g
        (periodicHypercubicUnshift n x (Fin.succ k)) =
      periodicHypercubicShift n
        (periodicHypercubicVertexSpatialSignedPermutation n g x)
        (periodicHypercubicSpatialSignedPermutationAxis g k) := by
  have h :=
    periodicHypercubicVertexSpatialSignedPermutation_shift_spatial_of_neg
      n g (periodicHypercubicUnshift n x (Fin.succ k)) k hneg
  rw [periodicHypercubicShift_unshift] at h
  have h' := congrArg
    (fun y => periodicHypercubicShift n y
      (periodicHypercubicSpatialSignedPermutationAxis g k)) h
  simpa using h'.symm

/-- Arbitrary signed-spatial configuration pullbacks satisfy the genuine left group-action
composition law. -/
theorem periodicHypercubicConfigurationSpatialSignedPermutation_mul
    {n : ℕ} {Gauge : Type} [Group Gauge]
    (g h : SpatialSignedPermutationGroup)
    (A : PeriodicHypercubicEdge n → Gauge) :
    periodicHypercubicConfigurationSpatialSignedPermutation (g * h) A =
      periodicHypercubicConfigurationSpatialSignedPermutation g
        (periodicHypercubicConfigurationSpatialSignedPermutation h A) := by
  funext e
  rcases e with ⟨x, μ⟩
  have hinv : (g * h)⁻¹ = h⁻¹ * g⁻¹ := by
    group
  refine Fin.cases ?_ (fun k => ?_) μ
  · simp [periodicHypercubicConfigurationSpatialSignedPermutation,
      periodicHypercubicStepValue, hinv,
      periodicHypercubicVertexSpatialSignedPermutation_mul]
  · simp only [periodicHypercubicConfigurationSpatialSignedPermutation]
    rw [hinv]
    generalize hgi : g⁻¹ = gi
    generalize hhi : h⁻¹ = hi
    by_cases hg : gi.left (gi.right k) = 1
    · by_cases hh : hi.left (hi.right (gi.right k)) = 1
      · have hprod :
            (hi * gi).left ((hi * gi).right k) = 1 := by
          rw [spatialSignedPermutation_mul_imageSign, hh, hg]
          simp
        simp [periodicHypercubicConfigurationSpatialSignedPermutation,
          periodicHypercubicStepValue, hhi, hg, hh, hprod,
          periodicHypercubicVertexSpatialSignedPermutation_mul]
      · have hhneg :
            hi.left (hi.right (gi.right k)) = (-1 : ℤˣ) :=
          (spatialSignedPermutation_imageSign_eq_one_or_neg_one
            hi (gi.right k)).resolve_left hh
        have hprod :
            (hi * gi).left ((hi * gi).right k) ≠ 1 := by
          rw [spatialSignedPermutation_mul_imageSign, hhneg, hg]
          native_decide
        simp [periodicHypercubicConfigurationSpatialSignedPermutation,
          periodicHypercubicStepValue, hhi, hg, hh, hhneg, hprod,
          periodicHypercubicVertexSpatialSignedPermutation_mul]
    · have hgneg :
          gi.left (gi.right k) = (-1 : ℤˣ) :=
        (spatialSignedPermutation_imageSign_eq_one_or_neg_one gi k).resolve_left hg
      by_cases hh : hi.left (hi.right (gi.right k)) = 1
      · have hprod :
            (hi * gi).left ((hi * gi).right k) ≠ 1 := by
          rw [spatialSignedPermutation_mul_imageSign, hh, hgneg]
          native_decide
        simp [periodicHypercubicConfigurationSpatialSignedPermutation,
          periodicHypercubicStepValue, hhi, hg, hgneg, hh, hprod,
          periodicHypercubicVertexSpatialSignedPermutation_mul,
          periodicHypercubicVertexSpatialSignedPermutation_unshift_spatial_of_pos]
      · have hhneg :
            hi.left (hi.right (gi.right k)) = (-1 : ℤˣ) :=
          (spatialSignedPermutation_imageSign_eq_one_or_neg_one
            hi (gi.right k)).resolve_left hh
        have hprod :
            (hi * gi).left ((hi * gi).right k) = 1 := by
          rw [spatialSignedPermutation_mul_imageSign, hhneg, hgneg]
          native_decide
        simp [periodicHypercubicConfigurationSpatialSignedPermutation,
          periodicHypercubicStepValue, hhi, hg, hgneg, hh, hhneg, hprod,
          periodicHypercubicVertexSpatialSignedPermutation_mul,
          periodicHypercubicVertexSpatialSignedPermutation_unshift_spatial_of_neg]

/-- Each abstract signed spatial permutation acts by an actual permutation of gauge configurations. -/
def periodicHypercubicConfigurationSpatialSignedPermutationEquiv
    (n : ℕ) {Gauge : Type} [Group Gauge]
    (g : SpatialSignedPermutationGroup) :
    (PeriodicHypercubicEdge n → Gauge) ≃ (PeriodicHypercubicEdge n → Gauge) where
  toFun := periodicHypercubicConfigurationSpatialSignedPermutation g
  invFun := periodicHypercubicConfigurationSpatialSignedPermutation g⁻¹
  left_inv A := by
    rw [← periodicHypercubicConfigurationSpatialSignedPermutation_mul (g := g⁻¹) (h := g)]
    simp
  right_inv A := by
    rw [← periodicHypercubicConfigurationSpatialSignedPermutation_mul (g := g) (h := g⁻¹)]
    simp

@[simp]
theorem periodicHypercubicConfigurationSpatialSignedPermutationEquiv_apply
    {n : ℕ} {Gauge : Type} [Group Gauge]
    (g : SpatialSignedPermutationGroup)
    (A : PeriodicHypercubicEdge n → Gauge) :
    periodicHypercubicConfigurationSpatialSignedPermutationEquiv n g A =
      periodicHypercubicConfigurationSpatialSignedPermutation g A :=
  rfl

/-- The full abstract signed spatial permutation group acts on the concrete gauge-configuration
carrier. -/
def periodicHypercubicConfigurationSpatialSignedPermutationActionHom
    (n : ℕ) {Gauge : Type} [Group Gauge] :
    SpatialSignedPermutationGroup →*
      Equiv.Perm (PeriodicHypercubicEdge n → Gauge) where
  toFun := periodicHypercubicConfigurationSpatialSignedPermutationEquiv n
  map_one' := by
    apply Equiv.ext
    intro A
    exact periodicHypercubicConfigurationSpatialSignedPermutation_one A
  map_mul' g h := by
    apply Equiv.ext
    intro A
    exact periodicHypercubicConfigurationSpatialSignedPermutation_mul g h A

end

end MathlibAnalytic
end MGAP4D