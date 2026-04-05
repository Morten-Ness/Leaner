import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable {s t u : Set M}

theorem coe_sup {N : Type*} [CommMonoid N] (H K : Submonoid N) :
    ↑(H ⊔ K) = (H * K : Set N) := by
  ext x
  simp [mem_sup, Set.mem_mul]

