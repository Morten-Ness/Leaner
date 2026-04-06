FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_unique_nonempty [Unique ι] (s : Finset ι) (f : ι → M) (h : s.Nonempty) :
    ∏ x ∈ s, f x = f default := by
  classical
  rcases h with ⟨x, hx⟩
  have hxd : x = default := Subsingleton.elim _ _
  subst hxd
  have hs : s = {default} := by
    apply Finset.Subsingleton.eq_singleton_of_nonempty
    · infer_instance
    · exact ⟨default, hx⟩
  simp [hs]
