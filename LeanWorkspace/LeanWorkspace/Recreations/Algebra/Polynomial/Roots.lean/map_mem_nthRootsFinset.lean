import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem map_mem_nthRootsFinset {S F : Type*} [CommRing S] [IsDomain S] [FunLike F R S]
    [MonoidHomClass F R S] {a : R} {x : R} (hx : x ∈ Polynomial.nthRootsFinset n a) (f : F) :
    f x ∈ Polynomial.nthRootsFinset n (f a) := by
  by_cases hn : n = 0
  · simp [hn] at hx
  · rw [Polynomial.mem_nthRootsFinset <| Nat.pos_of_ne_zero hn, ← map_pow, (Polynomial.mem_nthRootsFinset
      (Nat.pos_of_ne_zero hn) a).1 hx]

