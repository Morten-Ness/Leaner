import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem prodAux_eq : ∀ l : List M, FreeMonoid.prodAux l = l.prod
  | [] => rfl
  | (_ :: xs) => by simp [FreeMonoid.prodAux, List.prod_eq_foldl]
