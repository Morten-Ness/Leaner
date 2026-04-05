import Mathlib

variable {ι κ α β γ : Type*}

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

variable [CommMonoid β]

theorem prod_comm' {s : Finset γ} {t : γ → Finset α} {t' : Finset α} {s' : α → Finset γ}
    (h : ∀ x y, x ∈ s ∧ y ∈ t x ↔ x ∈ s' y ∧ y ∈ t') {f : γ → α → β} :
    (∏ x ∈ s, ∏ y ∈ t x, f x y) = ∏ y ∈ t', ∏ x ∈ s' y, f x y := by
  classical
    have : ∀ z : γ × α, (z ∈ s.biUnion fun x => (t x).map <| Function.Embedding.sectR x _) ↔
      z.1 ∈ s ∧ z.2 ∈ t z.1 := by
      rintro ⟨x, y⟩
      simp only [mem_biUnion, mem_map, Function.Embedding.sectR_apply, Prod.mk.injEq,
        exists_eq_right, ← and_assoc]
    exact
      (Finset.prod_finset_product' _ _ _ this).symm.trans
        ((Finset.prod_finset_product_right' _ _ _) fun ⟨x, y⟩ => (this _).trans ((h x y).trans and_comm))

