import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)
variable (P)
variable {k V P}
variable (k V) {p₁ p₂ : P}
variable (P) in
variable {P}

theorem direction_eq_top_iff_of_nonempty {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    s.direction = ⊤ ↔ s = ⊤ := by
  constructor
  · intro hs
    rcases h with ⟨p, hp⟩
    ext q
    constructor
    · intro hq
      simp
    · intro hq
      have hv : q -ᵥ p ∈ s.direction := by
        rw [hs]
        simp
      have hqp : (q -ᵥ p : V) +ᵥ p = q := by simp
      rw [← hqp]
      exact s.vadd_mem_of_mem_direction hv hp
  · intro hs
    rw [hs]
    simp
