import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem odd_iff : Odd n ↔ n % 2 = 1 := ⟨fun ⟨m, hm⟩ ↦ by lia, fun h ↦ ⟨n / 2, by lia⟩⟩

