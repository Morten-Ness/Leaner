import Mathlib

variable {M : Type*}

theorem Irreducible.dvd_comm [Monoid M] {p q : M} (hp : Irreducible p) (hq : Irreducible q) :
    p ∣ q ↔ q ∣ p := ⟨hp.dvd_symm hq, hq.dvd_symm hp⟩

