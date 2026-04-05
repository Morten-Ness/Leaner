import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem mem_closure_image_of (f : R →+* S) {s : Set R} {x : R} (hx : x ∈ Subring.closure s) :
    f x ∈ Subring.closure (f '' s) := by
  rw [← RingHom.map_closure f, Subring.mem_map]
  exact ⟨x, hx, rfl⟩

