import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable (g : S →+* T) (f : R →+* S)

theorem mem_range_self (f : R →+* S) (x : R) : f x ∈ f.range := RingHom.mem_range.mpr ⟨x, rfl⟩

