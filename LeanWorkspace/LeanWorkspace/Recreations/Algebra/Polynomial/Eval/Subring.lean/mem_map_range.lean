import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]} [Semiring S]

variable (f : R →+* S)

theorem mem_map_range {R S : Type*} [Ring R] [Ring S] (f : R →+* S) {p : S[X]} :
    p ∈ (mapRingHom f).range ↔ ∀ n, p.coeff n ∈ f.range := Polynomial.mem_map_rangeS f

