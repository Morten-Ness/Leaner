import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]} [Semiring S]

variable (f : R →+* S)

theorem notMem_map_rangeS {p : S[X]} : p ∉ (mapRingHom f).rangeS ↔ ∃ n, p.coeff n ∉ f.rangeS := (Polynomial.mem_map_rangeS f (p := p)).not.trans not_forall

