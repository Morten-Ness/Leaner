import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

theorem multiset_powerset_image_add [IsStrictOrderedRing R]
    {F α : Type*} [CommRing α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hf_na : IsNonarchimedean f) (s : Multiset α) (m : ℕ) :
    ∃ t : Multiset α, card t = card s - m ∧ (∀ x : α, x ∈ t → x ∈ s) ∧
      f (map prod (powersetCard (card s - m) s)).sum ≤ f t.prod := by
  set g := fun t : Multiset α ↦ t.prod
  obtain ⟨b, hb_in, hb_le⟩ := IsNonarchimedean.multiset_image_add hf_na g (powersetCard (card s - m) s)
  have hb : b ≤ s ∧ card b = card s - m := by
    rw [← mem_powersetCard]
    exact hb_in (card_pos.mp
      (card_powersetCard (s.card - m) s ▸ Nat.choose_pos ((card s).sub_le m)))
  exact ⟨b, hb.2, fun x hx ↦ mem_of_le hb.left hx, hb_le⟩

