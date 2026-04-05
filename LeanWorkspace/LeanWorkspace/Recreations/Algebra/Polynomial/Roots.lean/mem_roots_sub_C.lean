import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem mem_roots_sub_C {p : R[X]} {a x : R} (hp0 : 0 < degree p) :
    x ∈ (p - C a).roots ↔ p.eval x = a := Polynomial.mem_roots_sub_C'.trans <| and_iff_right fun hp => hp0.not_ge <| hp.symm ▸ degree_C_le

