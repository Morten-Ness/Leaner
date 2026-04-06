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

theorem inter_eq_singleton_of_nonempty_of_isCompl {s₁ s₂ : AffineSubspace k P}
    (h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty)
    (hd : IsCompl s₁.direction s₂.direction) : ∃ p, (s₁ : Set P) ∩ s₂ = {p} := by
  rcases h1 with ⟨p1, hp1⟩
  rcases h2 with ⟨p2, hp2⟩
  have htop : s₁.direction ⊔ s₂.direction = ⊤ := hd.sup_eq_top
  have hmemtop : p1 -ᵥ p2 ∈ s₁.direction ⊔ s₂.direction := by
    rw [htop]
    simp
  rw [Submodule.mem_sup] at hmemtop
  rcases hmemtop with ⟨v1, hv1, v2, hv2, hsum⟩
  let p : P := v2 +ᵥ p2
  have hp2' : p ∈ s₂ := s₂.vadd_mem_of_mem_direction hv2 hp2
  have hp1' : p ∈ s₁ := by
    have hv : v2 = -v1 + (p1 -ᵥ p2) := by
      rw [← hsum]
      abel
    rw [show p = (-v1 + (p1 -ᵥ p2)) +ᵥ p2 by simp [p, hv]]
    rw [vadd_vadd]
    have : (-v1 + (p1 -ᵥ p2)) +ᵥ p2 = (-v1) +ᵥ ((p1 -ᵥ p2) +ᵥ p2) := by
      simp [vadd_vadd]
    rw [this, vsub_vadd]
    exact s₁.vadd_mem_of_mem_direction (by simpa using neg_mem hv1) hp1
  refine ⟨p, ?_⟩
  ext q
  constructor
  · intro hq
    have hq1 : q ∈ s₁ := hq.1
    have hq2 : q ∈ s₂ := hq.2
    have hdir1 : q -ᵥ p ∈ s₁.direction := s₁.vsub_mem_direction hq1 hp1'
    have hdir2 : q -ᵥ p ∈ s₂.direction := s₂.vsub_mem_direction hq2 hp2'
    have hz : q -ᵥ p = 0 := by
      have hbot : s₁.direction ⊓ s₂.direction = ⊥ := hd.inf_eq_bot
      have hqp : q -ᵥ p ∈ s₁.direction ⊓ s₂.direction := ⟨hdir1, hdir2⟩
      rw [hbot, Submodule.mem_bot] at hqp
      exact hqp
    simp [Set.mem_singleton_iff, eq_of_vsub_eq_zero hz]
  · intro hq
    rcases Set.mem_singleton_iff.mp hq with rfl
    exact ⟨hp1', hp2'⟩
