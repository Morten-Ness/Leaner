import Mathlib

variable {F α β : Type*}

variable {α : Type*} {f : α → α} {n : ℕ}

theorem iterate_eq_id (hf : Function.Involutive f) (hne : f ≠ id) : f^[n] = id ↔ Even n := ⟨fun H ↦ not_odd_iff_even.1 fun hn ↦ hne <| by rwa [Function.Involutive.iterate_odd hf hn] at H, Function.Involutive.iterate_even hf⟩

