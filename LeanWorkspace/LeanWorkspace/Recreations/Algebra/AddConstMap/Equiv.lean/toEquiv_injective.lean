import Mathlib

open scoped AddConstMap

variable {G H K : Type*} [Add G] [Add H] [Add K] {a : G} {b : H} {c : K}

theorem toEquiv_injective : Function.Injective (AddConstEquiv.toEquiv : (G ≃+c[a, b] H) → G ≃ H)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
