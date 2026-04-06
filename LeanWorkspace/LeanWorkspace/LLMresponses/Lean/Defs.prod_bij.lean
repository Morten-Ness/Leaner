FAIL
import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

variable {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}

theorem prod_bij (i : ∀ a ∈ s, κ) (hi : ∀ a ha, i a ha ∈ t)
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, i a ha = b) (h : ∀ a ha, f a = g (i a ha)) :
    ∏ x ∈ s, f x = ∏ x ∈ t, g x := by
  classical
  simpa [Finset.prod_attach] using
    (Finset.prod_bij_ne_one
      (s := s.attach) (t := t)
      (f := fun x => f x.1) (g := g)
      (i := fun x _ => i x.1 x.2)
      (by
        intro x hx
        exact hi x.1 x.2)
      (by
        intro x hx
        exact h x.1 x.2)
      (by
        intro x₁ hx₁ x₂ hx₂ hEq
        apply Subtype.ext
        exact i_inj x₁.1 x₁.2 x₂.1 x₂.2 hEq)
      (by
        intro b hb
        rcases i_surj b hb with ⟨a, ha, hEq⟩
        refine ⟨⟨a, ha⟩, ?_, hEq⟩
        simp)
      (by
        intro b hb hbg
        rcases i_surj b hb with ⟨a, ha, hEq⟩
        exact hbg ⟨a, ha⟩ (by simp) hEq))
