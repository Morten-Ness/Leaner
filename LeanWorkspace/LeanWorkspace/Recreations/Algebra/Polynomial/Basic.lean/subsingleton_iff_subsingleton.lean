import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem subsingleton_iff_subsingleton : Subsingleton R[X] ↔ Subsingleton R := ⟨@Function.Injective.subsingleton _ _ _ Polynomial.C_injective, by
    intro
    infer_instance⟩

