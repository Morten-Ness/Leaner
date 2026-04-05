import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem comap_map_eq (f : R →+* S) (s : Subring R) :
    (s.map f).comap f = s ⊔ Subring.closure (f ⁻¹' {0}) := by
  apply le_antisymm
  · intro x hx
    rw [Subring.mem_comap, Subring.mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    replace hxy : x - y ∈ f ⁻¹' {0} := by simp [hxy]
    rw [← Subring.closure_eq s, ← Subring.closure_union, ← add_sub_cancel y x]
    exact Subring.add_mem _ (Subring.subset_closure <| Or.inl hy) (Subring.subset_closure <| Or.inr hxy)
  · rw [← Subring.map_le_iff_le_comap, Subring.map_sup, RingHom.map_closure f]
    apply le_of_eq
    rw [sup_eq_left, Subring.closure_le]
    exact (Set.image_preimage_subset f {0}).trans (Set.singleton_subset_iff.2 (s.map f).zero_mem)

