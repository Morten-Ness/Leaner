import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem sum_eq_one_iff (d : α →₀ ℕ) : sum d (fun _ n ↦ n) = 1 ↔ ∃ a, d = single a 1 := by
  classical
  refine ⟨fun h1 ↦ ?_, ?_⟩
  · have hd0 : d ≠ 0 := (by simp [·] at h1)
    obtain ⟨a, ha⟩ := ne_iff.mp hd0
    obtain ⟨hda, hda'⟩ : d a = 1 ∧ ∀ i ≠ a, d i = 0 := by
      rw [← add_sum_erase' _ a _ (fun _ ↦ rfl), Nat.add_eq_one_iff, or_iff_not_imp_left] at h1
      simp_all +contextual [sum, support_erase, sum_eq_zero_iff, mem_erase, erase_ne]
    use a
    ext b
    by_cases hb : b = a
    · rw [hb, single_eq_same, hda]
    · simpa only [single_eq_of_ne hb] using hda' b hb
  · rintro ⟨a, rfl⟩
    rw [sum_eq_single a ?_ (fun _ ↦ rfl), single_eq_same]
    exact fun _ _ hba ↦ single_eq_of_ne hba

