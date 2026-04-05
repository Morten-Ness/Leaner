import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem mem_roots_map_of_injective [Semiring S] {p : S[X]} {f : S →+* R}
    (hf : Function.Injective f) {x : R} (hp : p ≠ 0) : x ∈ (p.map f).roots ↔ p.eval₂ f x = 0 := by
  rw [Polynomial.mem_roots ((Polynomial.map_ne_zero_iff hf).mpr hp), IsRoot, eval_map]

