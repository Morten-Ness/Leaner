import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

theorem collinear_iff_of_mem {s : Set P} {p₀ : P} (h : p₀ ∈ s) :
    Collinear k s ↔ ∃ v : V, ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ := by
  simp_rw [collinear_iff_rank_le_one, rank_submodule_le_one_iff', Submodule.le_span_singleton_iff]
  constructor
  · rintro ⟨v₀, hv⟩
    use v₀
    intro p hp
    obtain ⟨r, hr⟩ := hv (p -ᵥ p₀) (vsub_mem_vectorSpan k hp h)
    use r
    rw [eq_vadd_iff_vsub_eq]
    exact hr.symm
  · rintro ⟨v, hp₀v⟩
    use v
    intro w hw
    have hs : vectorSpan k s ≤ k ∙ v := by
      rw [vectorSpan_eq_span_vsub_set_right k h, Submodule.span_le, Set.subset_def]
      intro x hx
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      rw [Set.mem_image] at hx
      rcases hx with ⟨p, hp, rfl⟩
      rcases hp₀v p hp with ⟨r, rfl⟩
      use r
      simp
    have hw' := SetLike.le_def.1 hs hw
    rwa [Submodule.mem_span_singleton] at hw'

