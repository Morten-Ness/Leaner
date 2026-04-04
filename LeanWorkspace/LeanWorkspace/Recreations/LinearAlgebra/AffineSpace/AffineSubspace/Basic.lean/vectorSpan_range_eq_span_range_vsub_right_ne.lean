import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

theorem vectorSpan_range_eq_span_range_vsub_right_ne (p : ι → P) (i₀ : ι) :
    vectorSpan k (Set.range p) =
      Submodule.span k (Set.range fun i : { x // x ≠ i₀ } => p i -ᵥ p i₀) := by
  rw [← Set.image_univ, vectorSpan_image_eq_span_vsub_set_right_ne k _ (Set.mem_univ i₀)]
  congr with v
  simp only [Set.mem_range, Set.mem_image, Set.mem_diff, Set.mem_singleton_iff, Subtype.exists]
  constructor
  · rintro ⟨x, ⟨i₁, ⟨⟨_, hi₁⟩, rfl⟩⟩, hv⟩
    exact ⟨i₁, hi₁, hv⟩
  · exact fun ⟨i₁, hi₁, hv⟩ => ⟨p i₁, ⟨i₁, ⟨Set.mem_univ _, hi₁⟩, rfl⟩, hv⟩

