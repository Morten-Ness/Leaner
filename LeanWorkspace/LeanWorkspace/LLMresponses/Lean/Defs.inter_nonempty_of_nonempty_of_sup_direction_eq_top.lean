FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in
-- keep the scoped variable command nonempty for style lint
example : True := by
  trivial

theorem inter_nonempty_of_nonempty_of_sup_direction_eq_top {s₁ s₂ : AffineSubspace k P}
    (h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty)
    (hd : s₁.direction ⊔ s₂.direction = ⊤) : ((s₁ : Set P) ∩ s₂).Nonempty := by
  rcases h1 with ⟨p1, hp1⟩
  rcases h2 with ⟨p2, hp2⟩
  have htop : p2 -ᵥ p1 ∈ s₁.direction ⊔ s₂.direction := by
    rw [hd]
    trivial
  rcases Submodule.mem_sup.mp htop with ⟨v1, hv1, v2, hv2, hsum⟩
  let p : P := v1 +ᵥ p1
  have hp_mem_s1 : p ∈ s₁ := s₁.vadd_mem_of_mem_direction hv1 hp1
  have hp_eq : p = (-v2) +ᵥ p2 := by
    apply vadd_left_cancel (v := v2)
    dsimp [p]
    rw [← vadd_assoc, add_left_neg, zero_vadd, ← hsum, add_comm, vadd_vadd]
  have hp_mem_s2 : p ∈ s₂ := by
    rw [hp_eq]
    exact s₂.vadd_mem_of_mem_direction (by simpa using s₂.direction.neg_mem hv2) hp2
  exact ⟨p, hp_mem_s1, hp_mem_s2⟩
