import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem modByMonic_eq_self_iff [Nontrivial R] (hq : Polynomial.Monic q) : p %ₘ q = p ↔ degree p < degree q := ⟨fun h => h ▸ Polynomial.degree_modByMonic_lt _ hq, fun h => by
    classical
    have : ¬degree q ≤ degree p := not_le_of_gt h
    unfold Polynomial.modByMonic Polynomial.divModByMonicAux; dsimp; rw [dif_pos hq, if_neg (mt And.left this)]⟩

