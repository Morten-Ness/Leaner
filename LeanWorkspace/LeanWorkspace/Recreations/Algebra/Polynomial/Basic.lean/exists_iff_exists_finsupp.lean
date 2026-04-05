import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem exists_iff_exists_finsupp (P : R[X] → Prop) :
    (∃ p, P p) ↔ ∃ q : R[ℕ], P ⟨q⟩ := ⟨fun ⟨⟨p⟩, hp⟩ => ⟨p, hp⟩, fun ⟨q, hq⟩ => ⟨⟨q⟩, hq⟩⟩

