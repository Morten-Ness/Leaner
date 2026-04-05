import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem floor_eq_on_Ico (n : ℕ) : ∀ a ∈ (Set.Ico n (n + 1) : Set R), ⌊a⌋₊ = n := fun _ ⟨h₀, h₁⟩ =>
  (Nat.floor_eq_iff <| n.cast_nonneg.trans h₀).mpr ⟨h₀, h₁⟩

