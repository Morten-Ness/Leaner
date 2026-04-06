FAIL
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
  classical
  refine lt_of_le_of_ne ?_ ?_
  · exact le_direction_sup k s₁ s₂
  · intro hEq
    rcases Set.nonempty_iff_ne_empty.mp h1 with ⟨p1, hp1⟩
    rcases Set.nonempty_iff_ne_empty.mp h2 with ⟨p2, hp2⟩
    have hp : p2 ∈ s₁ ⊔ s₂ := by
      rw [AffineSubspace.mem_sup]
      exact Or.inr hp2
    rw [← hEq] at hp
    rw [Submodule.mem_sup] at hp
    rcases hp with ⟨v1, hv1, v2, hv2, hsum⟩
    have hp1' : p1 +ᵥ v1 ∈ s₁ := s₁.vadd_mem_of_mem_direction hp1 hv1
    have hp2' : p1 +ᵥ v2 ∈ s₂ := by
      have : p1 +ᵥ (p2 -ᵥ p1) = p2 := by simpa using vadd_vsub p2 p1
      have hv : p2 -ᵥ p1 ∈ s₂.direction := by
        rw [← hsum]
        exact s₂.vsub_mem_direction hp2 hp1
      exact by
        simpa [this] using s₂.vadd_mem_of_mem_direction hp1 hv2
    have hp12 : p1 +ᵥ v1 ∈ (s₁ ∩ s₂ : Set P) := ⟨hp1', by
      have : p1 +ᵥ (v1 + v2) = p2 := by
        simpa [hsum] using vadd_vsub p2 p1
      have hdir : v1 ∈ s₂.direction := by
        have htot : v1 + v2 ∈ s₂.direction := by
          simpa [hsum] using s₂.vsub_mem_direction hp2 hp1
        exact s₂.direction.add_mem (by simpa using htot) (s₂.direction.neg_mem hv2)
      simpa using s₂.vadd_mem_of_mem_direction hp1 hdir⟩
    have : (s₁ ∩ s₂ : Set P).Nonempty := ⟨_, hp12⟩
    simpa [Set.eq_empty_iff_forall_not_mem] using he
