import Mathlib

variable {ι : Type*}

theorem card_preimage_eq_sum_card_image_eq {M : Type*} {f : ι → M} {s : Finset M}
    (hb : ∀ b ∈ s, Set.Finite {a | f a = b}) :
    Nat.card (f ⁻¹' s) = ∑ b ∈ s, Nat.card {a // f a = b} := by
  classical
  -- `t = s ∩ Set.range f` as a `Finset`
  let t := (Set.finite_coe_iff.mp (Finite.Set.finite_inter_of_left ↑s (Set.range f))).toFinset
  rw [show Nat.card (f ⁻¹' s) = Nat.card (f ⁻¹' t) by simp [t]]
  rw [show ∑ b ∈ s, Nat.card {a //f a = b} = ∑ b ∈ t, Nat.card {a | f a = b} by
    exact (Finset.sum_subset (by simp [t]) (by aesop)).symm]
  have ht : Set.Finite (f ⁻¹' t) := Set.Finite.preimage' (finite_toSet t) (by aesop)
  rw [Nat.card_eq_card_finite_toFinset ht, Finset.card_eq_sum_card_image (f := f)]
  refine Finset.sum_congr ?_ fun m hm ↦ ?_
  · simpa [← Finset.coe_inj, t] using Set.image_preimage_eq_inter_range
  · rw [Nat.card_eq_card_finite_toFinset (hb _ (by aesop))]
    suffices {a | f a = m} ⊆ ht.toFinset from
      congr_arg (Finset.card ·) (Finset.ext_iff.mpr fun a ↦ by simpa using fun h ↦ this h)
    intro _ h
    simp_all

