import Mathlib

variable {α : Type*} [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {β : Type*} {f : α → β} {k : α}

theorem range_add_eq_image_Ici : range (fun x ↦ f (x + k)) = f '' Ici k := Set.ext fun x ↦ ⟨fun ⟨y, hfy⟩ ↦ ⟨y + k, self_le_add_left k y, hfy⟩,
    fun ⟨y, hy, hfy⟩ ↦ ⟨y - k, by simpa [tsub_add_cancel_of_le hy] using hfy⟩⟩

