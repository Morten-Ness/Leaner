import Mathlib

open scoped TensorProduct

variable {R A B : Type*}
  [CommSemiring R] [StarRing R]
  [AddCommMonoid A] [StarAddMonoid A] [Module R A] [StarModule R A]
  [AddCommMonoid B] [StarAddMonoid B] [Module R B] [StarModule R B]

theorem star_tmul (x : A) (y : B) : star (x ⊗ₜ[R] y) = star x ⊗ₜ[R] star y := rfl

noncomputable instance : InvolutiveStar (A ⊗[R] B) where
  star_involutive x := by
    simp_rw [star]
    rw [congr_congr]
    convert congr($congr_refl_refl x) <;> ext <;> simp

noncomputable instance : StarAddMonoid (A ⊗[R] B) where
  star_add := map_add _

