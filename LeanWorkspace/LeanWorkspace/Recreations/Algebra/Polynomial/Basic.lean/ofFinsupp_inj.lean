import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem ofFinsupp_inj {a b} : (⟨a⟩ : R[X]) = ⟨b⟩ ↔ a = b := iff_of_eq (ofFinsupp.injEq _ _)

