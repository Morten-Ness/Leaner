import Mathlib

section

variable {ι K : Type*} [DivisionSemiring K]

theorem Finset.sum_div (s : Finset ι) (f : ι → K) (a : K) :
    (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a := by simp only [div_eq_mul_inv, sum_mul]

-- TODO: Move these to `Algebra.BigOperators.Group.Finset.Basic`, next to the corresponding `card`
-- lemmas, once `Finset.dens` doesn't depend on `Field` anymore.

end

section

variable {ι K : Type*} [DivisionSemiring K]

theorem Multiset.sum_map_div (s : Multiset ι) (f : ι → K) (a : K) :
    (s.map (fun x ↦ f x / a)).sum = (s.map f).sum / a := by
  simp only [div_eq_mul_inv, Multiset.sum_map_mul_right]

end

section

variable {ι K : Type*} [DivisionSemiring K]

variable {α β : Type*} [Fintype β]

variable {s : Finset α} {t : α → Finset β}

theorem dens_biUnion [DecidableEq β] (h : (s : Set α).PairwiseDisjoint t) :
    (s.biUnion t).dens = ∑ u ∈ s, (t u).dens := by
  simp [dens, card_biUnion h, sum_div]

end

section

variable {ι K : Type*} [DivisionSemiring K]

variable {α β : Type*} [Fintype β]

variable {s : Finset α} {t : α → Finset β}

theorem dens_biUnion_le [DecidableEq β] : (s.biUnion t).dens ≤ ∑ a ∈ s, (t a).dens := by
  simp only [dens, ← sum_div]
  gcongr
  exact mod_cast card_biUnion_le

end

section

variable {ι K : Type*} [DivisionSemiring K]

variable {α β : Type*} [Fintype β]

variable {s : Finset α} {t : α → Finset β}

theorem dens_eq_sum_dens_fiberwise [DecidableEq α] {f : β → α} {t : Finset β}
    (h : (t : Set β).MapsTo f s) : t.dens = ∑ a ∈ s, {b ∈ t | f b = a}.dens := by
  simp [dens, ← sum_div, card_eq_sum_card_fiberwise h]

end

section

variable {ι K : Type*} [DivisionSemiring K]

variable {α β : Type*} [Fintype β]

variable {s : Finset α} {t : α → Finset β}

theorem dens_eq_sum_dens_image [DecidableEq α] (f : β → α) (t : Finset β) :
    t.dens = ∑ a ∈ t.image f, {b ∈ t | f b = a}.dens := Finset.dens_eq_sum_dens_fiberwise fun _ ↦ mem_image_of_mem _

end
