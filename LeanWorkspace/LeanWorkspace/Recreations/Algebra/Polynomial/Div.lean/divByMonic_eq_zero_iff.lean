import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem divByMonic_eq_zero_iff [Nontrivial R] (hq : Polynomial.Monic q) : p /ₘ q = 0 ↔ degree p < degree q := ⟨fun h => by
    have := Polynomial.modByMonic_add_div p q
    rwa [h, mul_zero, add_zero, Polynomial.modByMonic_eq_self_iff hq] at this,
  fun h => by
    classical
    have : ¬degree q ≤ degree p := not_le_of_gt h
    unfold Polynomial.divByMonic Polynomial.divModByMonicAux; dsimp; rw [dif_pos hq, if_neg (mt And.left this)]⟩

