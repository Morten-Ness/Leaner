import Mathlib

variable {F α β : Type*}

variable {α : Type*} {f : α → α} {n : ℕ}

theorem iterate_eq_self (hf : Function.Involutive f) (hne : f ≠ id) : f^[n] = f ↔ Odd n := ⟨fun H ↦ not_even_iff_odd.1 fun hn ↦ hne <| by rwa [Function.Involutive.iterate_even hf hn, eq_comm] at H,
    Function.Involutive.iterate_odd hf⟩

