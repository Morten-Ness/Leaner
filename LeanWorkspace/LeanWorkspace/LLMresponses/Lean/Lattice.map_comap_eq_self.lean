import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_comap_eq_self
    {f : A →ₐ[R] B} {S : Subalgebra R B} (h : S ≤ f.range) : (S.comap f).map f = S := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    rcases h hx with ⟨y, rfl⟩
    exact ⟨y, hx, rfl⟩
