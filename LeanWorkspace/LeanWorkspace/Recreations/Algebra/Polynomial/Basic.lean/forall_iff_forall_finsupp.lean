import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem forall_iff_forall_finsupp (P : R[X] → Prop) :
    (∀ p, P p) ↔ ∀ q : R[ℕ], P ⟨q⟩ := ⟨fun h q => h ⟨q⟩, fun h ⟨p⟩ => h p⟩

