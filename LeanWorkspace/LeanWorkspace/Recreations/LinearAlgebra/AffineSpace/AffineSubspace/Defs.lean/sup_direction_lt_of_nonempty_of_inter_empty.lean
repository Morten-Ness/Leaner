import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem sup_direction_lt_of_nonempty_of_inter_empty {s₁ s₂ : AffineSubspace k P}
    (h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty) (he : (s₁ ∩ s₂ : Set P) = ∅) :
    s₁.direction ⊔ s₂.direction < (s₁ ⊔ s₂).direction := by
  obtain ⟨p₁, hp₁⟩ := h1
  obtain ⟨p₂, hp₂⟩ := h2
  rw [SetLike.lt_iff_le_and_exists]
  use AffineSubspace.sup_direction_le s₁ s₂, p₂ -ᵥ p₁,
    AffineSubspace.vsub_mem_direction ((le_sup_right : s₂ ≤ s₁ ⊔ s₂) hp₂) ((le_sup_left : s₁ ≤ s₁ ⊔ s₂) hp₁)
  intro h
  rw [Submodule.mem_sup] at h
  rcases h with ⟨v₁, hv₁, v₂, hv₂, hv₁v₂⟩
  rw [← sub_eq_zero, sub_eq_add_neg, neg_vsub_eq_vsub_rev, add_comm v₁, add_assoc, ←
    vadd_vsub_assoc, ← neg_neg v₂, add_comm, ← sub_eq_add_neg, ← vsub_vadd_eq_vsub_sub,
    vsub_eq_zero_iff_eq] at hv₁v₂
  refine Set.Nonempty.ne_empty ?_ he
  use v₁ +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction hv₁ hp₁
  rw [hv₁v₂]
  exact AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv₂) hp₂

