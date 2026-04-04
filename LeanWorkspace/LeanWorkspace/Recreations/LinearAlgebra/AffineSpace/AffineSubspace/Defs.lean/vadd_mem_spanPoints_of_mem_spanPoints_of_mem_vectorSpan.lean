import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

variable (P) in

theorem vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan {s : Set P} {p : P} {v : V}
    (hp : p ∈ spanPoints k s) (hv : v ∈ vectorSpan k s) : v +ᵥ p ∈ spanPoints k s := by
  rcases hp with ⟨p₂, ⟨hp₂, ⟨v₂, ⟨hv₂, hv₂p⟩⟩⟩⟩
  rw [hv₂p, vadd_vadd]
  exact ⟨p₂, hp₂, v + v₂, (vectorSpan k s).add_mem hv hv₂, rfl⟩

