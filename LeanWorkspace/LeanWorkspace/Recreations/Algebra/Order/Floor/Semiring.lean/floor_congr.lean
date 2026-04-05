import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a : R}

variable {S : Type*} [Semiring S] [LinearOrder S] [FloorSemiring S] {b : S}

theorem floor_congr [IsStrictOrderedRing R] [IsStrictOrderedRing S]
    (h : ∀ n : ℕ, (n : R) ≤ a ↔ (n : S) ≤ b) : ⌊a⌋₊ = ⌊b⌋₊ := by
  have h₀ : 0 ≤ a ↔ 0 ≤ b := by simpa only [cast_zero] using h 0
  obtain ha | ha := lt_or_ge a 0
  · rw [Nat.floor_of_nonpos ha.le, Nat.floor_of_nonpos (le_of_not_ge <| h₀.not.mp ha.not_ge)]
  exact (le_floor <| (h _).1 <| Nat.floor_le ha).antisymm (le_floor <| (h _).2 <| Nat.floor_le <| h₀.1 ha)

