import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem FG.spanRank_le_iff {p : Submodule R M} (hp : p.FG) (n : ℕ) :
    p.spanRank ≤ n ↔ p.spanFinrank ≤ n := (Cardinal.toNat_le_iff_of_lt_aleph0 n (by simpa)).symm

