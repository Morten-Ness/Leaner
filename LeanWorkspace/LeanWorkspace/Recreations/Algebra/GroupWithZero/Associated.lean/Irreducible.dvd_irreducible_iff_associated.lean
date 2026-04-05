import Mathlib

variable {M : Type*}

theorem Irreducible.dvd_irreducible_iff_associated [Monoid M] {p q : M}
    (pp : Irreducible p) (qp : Irreducible q) : p ∣ q ↔ Associated p q := ⟨Irreducible.associated_of_dvd pp qp, Associated.dvd⟩

