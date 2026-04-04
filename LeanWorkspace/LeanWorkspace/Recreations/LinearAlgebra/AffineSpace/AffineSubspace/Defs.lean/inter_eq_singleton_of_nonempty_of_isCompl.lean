import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem inter_eq_singleton_of_nonempty_of_isCompl {s₁ s₂ : AffineSubspace k P}
    (h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty)
    (hd : IsCompl s₁.direction s₂.direction) : ∃ p, (s₁ : Set P) ∩ s₂ = {p} := by
  obtain ⟨p, hp⟩ := AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top h1 h2 hd.sup_eq_top
  use p
  ext q
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hq1, hq2⟩
    have hqp : q -ᵥ p ∈ s₁.direction ⊓ s₂.direction :=
      ⟨AffineSubspace.vsub_mem_direction hq1 hp.1, AffineSubspace.vsub_mem_direction hq2 hp.2⟩
    rwa [hd.inf_eq_bot, Submodule.mem_bot, vsub_eq_zero_iff_eq] at hqp
  · exact fun h => h.symm ▸ hp

