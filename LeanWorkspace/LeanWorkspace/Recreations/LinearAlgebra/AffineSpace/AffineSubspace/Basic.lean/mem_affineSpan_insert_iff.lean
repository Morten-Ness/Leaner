import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

theorem mem_affineSpan_insert_iff {s : AffineSubspace k P} {p₁ : P} (hp₁ : p₁ ∈ s) (p₂ p : P) :
    p ∈ affineSpan k (insert p₂ (s : Set P)) ↔
      ∃ r : k, ∃ p0 ∈ s, p = r • (p₂ -ᵥ p₁ : V) +ᵥ p0 := by
  rw [← mem_coe] at hp₁
  rw [← AffineSubspace.vsub_right_mem_direction_iff_mem (mem_affineSpan k (Set.mem_insert_of_mem _ hp₁)),
    AffineSubspace.direction_affineSpan_insert hp₁, Submodule.mem_sup]
  constructor
  · rintro ⟨v₁, hv₁, v₂, hv₂, hp⟩
    rw [Submodule.mem_span_singleton] at hv₁
    rcases hv₁ with ⟨r, rfl⟩
    use r, v₂ +ᵥ p₁, vadd_mem_of_mem_direction hv₂ hp₁
    symm at hp
    rw [← sub_eq_zero, ← vsub_vadd_eq_vsub_sub, vsub_eq_zero_iff_eq] at hp
    rw [hp, vadd_vadd]
  · rintro ⟨r, p₃, hp₃, rfl⟩
    use r • (p₂ -ᵥ p₁), Submodule.mem_span_singleton.2 ⟨r, rfl⟩, p₃ -ᵥ p₁,
      vsub_mem_direction hp₃ hp₁
    rw [vadd_vsub_assoc]

