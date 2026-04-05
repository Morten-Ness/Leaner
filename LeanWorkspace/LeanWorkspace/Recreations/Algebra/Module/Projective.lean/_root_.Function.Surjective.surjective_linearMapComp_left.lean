import Mathlib

variable {R : Type*} [Semiring R] {P : Type*} [AddCommMonoid P] [Module R P] {M : Type*}
  [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]

theorem _root_.Function.Surjective.surjective_linearMapComp_left [Projective R P]
    {f : M →ₗ[R] P} (hf_surj : Function.Surjective f) : Function.Surjective (fun g : N →ₗ[R] M ↦ f.comp g) := surjective_comp_left_of_exists_rightInverse <|
    f.exists_rightInverse_of_surjective <| range_eq_top_of_surjective f hf_surj

