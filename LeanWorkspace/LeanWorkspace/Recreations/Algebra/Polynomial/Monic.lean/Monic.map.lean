import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem Monic.map [Semiring S] (f : R →+* S) (hp : Polynomial.Monic p) : Polynomial.Monic (p.map f) := subsingleton_or_nontrivial S |>.elim (·.elim ..) fun _ ↦
    f.map_one ▸ hp ▸ leadingCoeff_map_eq_of_isUnit_leadingCoeff _ <| isUnit_one

