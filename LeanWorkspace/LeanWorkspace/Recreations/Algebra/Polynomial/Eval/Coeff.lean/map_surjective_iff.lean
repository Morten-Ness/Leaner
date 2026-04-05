import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem map_surjective_iff : Function.Surjective (map f) ↔ Function.Surjective f := ⟨fun h s ↦ let ⟨p, h⟩ := h (Polynomial.C s); ⟨p.coeff 0, by simpa using congr(coeff $h 0)⟩, Polynomial.map_surjective f⟩

