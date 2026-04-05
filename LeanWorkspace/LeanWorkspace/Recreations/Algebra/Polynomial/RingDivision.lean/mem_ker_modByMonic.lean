import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] {p q : R[X]}

theorem mem_ker_modByMonic (hq : q.Monic) {p : R[X]} :
    p ∈ LinearMap.ker (Polynomial.modByMonicHom q) ↔ q ∣ p := LinearMap.mem_ker.trans (modByMonic_eq_zero_iff_dvd hq)

