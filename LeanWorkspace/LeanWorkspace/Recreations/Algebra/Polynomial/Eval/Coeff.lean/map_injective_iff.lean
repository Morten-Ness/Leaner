import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem map_injective_iff : Function.Injective (map f) ↔ Function.Injective f := ⟨fun h r r' eq ↦ by simpa using h (a₁ := Polynomial.C r) (a₂ := Polynomial.C r') (by simpa), Polynomial.map_injective f⟩

