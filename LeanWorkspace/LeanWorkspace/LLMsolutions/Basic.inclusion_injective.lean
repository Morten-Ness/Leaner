import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem inclusion_injective : Function.Injective (Subalgebra.inclusion h) := by
  intro x y hxy
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  change (⟨x, h hx⟩ : T) = ⟨y, h hy⟩ at hxy
  cases hxy
  rfl
