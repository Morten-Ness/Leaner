import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_comap_eq_self_of_surjective
    {f : A →ₐ[R] B} (hf : Function.Surjective f) (S : Subalgebra R B) : (S.comap f).map f = S := by
  ext b
  constructor
  · intro hb
    rcases hb with ⟨a, ha, rfl⟩
    exact ha
  · intro hb
    rcases hf b with ⟨a, rfl⟩
    exact ⟨a, hb, rfl⟩
