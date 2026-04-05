import Mathlib

open scoped DirectSum

variable {ι : Type*} [DecidableEq ι]

variable (A : ι → Type*)

variable [∀ i, AddCommMonoid (A i)] [AddMonoid ι] [GSemiring A]

private theorem mul_assoc (a b c : ⨁ i, A i) : a * b * c = a * (b * c) := by
  -- (`fun a b c => a * b * c` as a bundled hom) = (`fun a b c => a * (b * c)` as a bundled hom)
  suffices AddMonoidHom.mulLeft₃ = AddMonoidHom.mulRight₃ by
      simpa only [AddMonoidHom.mulLeft₃_apply, AddMonoidHom.mulRight₃_apply] using
        DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this a) b) c
  ext ai ax bi bx ci cx : 6
  dsimp only [coe_comp, Function.comp_apply, AddMonoidHom.mulLeft₃_apply,
    AddMonoidHom.mulRight₃_apply]
  simp_rw [DirectSum.of_mul_of]
  exact DirectSum.of_eq_of_gradedMonoid_eq (_root_.mul_assoc (GradedMonoid.mk ai ax) ⟨bi, bx⟩ ⟨ci, cx⟩)


theorem ofPow {i} (a : A i) (n : ℕ) :
    of _ i a ^ n = of _ (n • i) (GradedMonoid.GMonoid.gnpow _ a) := by
  induction n with
  | zero => exact DirectSum.of_eq_of_gradedMonoid_eq (pow_zero <| GradedMonoid.mk _ a).symm
  | succ n n_ih =>
    rw [pow_succ, n_ih, DirectSum.of_mul_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq (pow_succ (GradedMonoid.mk _ a) n).symm

