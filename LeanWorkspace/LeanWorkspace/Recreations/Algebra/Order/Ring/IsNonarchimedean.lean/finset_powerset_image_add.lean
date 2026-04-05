import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

theorem finset_powerset_image_add [IsStrictOrderedRing R]
    {F α β : Type*} [CommRing α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hf_na : IsNonarchimedean f) (s : Finset β)
    (b : β → α) (m : ℕ) :
    ∃ u : powersetCard (s.card - m) s,
      f ((powersetCard (s.card - m) s).sum fun t : Finset β ↦
        t.prod fun i : β ↦ -b i) ≤ f (u.val.prod fun i : β ↦ -b i) := by
  set g := fun t : Finset β ↦ t.prod fun i : β ↦ - b i
  obtain ⟨b, hb_in, hb⟩ := IsNonarchimedean.finset_image_add hf_na g (powersetCard (s.card - m) s)
  exact ⟨⟨b, hb_in (powersetCard_nonempty.mpr (Nat.sub_le s.card m))⟩, hb⟩

