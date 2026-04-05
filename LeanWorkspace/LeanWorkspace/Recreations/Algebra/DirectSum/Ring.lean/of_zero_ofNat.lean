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


private theorem mul_comm (a b : ⨁ i, A i) : a * b = b * a := by
  suffices DirectSum.mulHom A = (DirectSum.mulHom A).flip by
    rw [← DirectSum.mulHom_apply, this, AddMonoidHom.flip_apply, DirectSum.mulHom_apply]
  apply addHom_ext; intro ai ax; apply addHom_ext; intro bi bx
  rw [AddMonoidHom.flip_apply, DirectSum.mulHom_of_of, DirectSum.mulHom_of_of]
  exact DirectSum.of_eq_of_gradedMonoid_eq (GCommSemiring.mul_comm ⟨ai, ax⟩ ⟨bi, bx⟩)


theorem of_zero_ofNat (n : ℕ) [n.AtLeastTwo] : of A 0 ofNat(n) = ofNat(n) := DirectSum.of_natCast A n

