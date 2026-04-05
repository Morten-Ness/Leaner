import Mathlib

variable (R : Type*)

variable {R} [NonAssocSemiring R]

theorem charP_iff_prime_eq_zero [Nontrivial R] {p : ℕ} (hp : p.Prime) :
    CharP R p ↔ (p : R) = 0 := ⟨fun _ => cast_eq_zero R p,
   fun hp0 => (CharP.ringChar_of_prime_eq_zero hp hp0) ▸ inferInstance⟩

