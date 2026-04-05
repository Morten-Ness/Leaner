import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]} {x : R} [Semiring S] (f : R →+* S)

theorem eval₂_hom (x : R) : p.eval₂ f (f x) = f (p.eval x) := RingHom.comp_id f ▸ (Polynomial.hom_eval₂ p (RingHom.id R) f x).symm

