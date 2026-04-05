import Mathlib

theorem BddAbove.range_comp_of_nonneg {α β γ : Type*} [Nonempty α] [Preorder β] [Zero β] [Preorder γ]
    {f : α → β} {g : β → γ} (hf : BddAbove (Set.range f)) (hf0 : 0 ≤ f)
    (hg : MonotoneOn g {x : β | 0 ≤ x}) : BddAbove (Set.range (fun x => g (f x))) := by
  suffices hg' : BddAbove (g '' Set.range f) by
    rwa [← Function.comp_def, Set.range_comp]
  apply hg.map_bddAbove (by rintro x ⟨a, rfl⟩; exact hf0 a)
  obtain ⟨b, hb⟩ := hf
  use b, hb
  simp only [mem_upperBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hb
  exact le_trans (hf0 Classical.ofNonempty) (hb Classical.ofNonempty)

