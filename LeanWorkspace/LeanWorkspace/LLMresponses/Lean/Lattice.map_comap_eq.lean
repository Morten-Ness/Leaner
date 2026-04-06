import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_comap_eq (f : A →ₐ[R] B) (S : Subalgebra R B) : (S.comap f).map f = S ⊓ f.range := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨hy, ⟨y, rfl⟩⟩
  · intro hx
    rcases hx with ⟨hxS, hxR⟩
    rcases hxR with ⟨y, rfl⟩
    exact ⟨y, hxS, rfl⟩
