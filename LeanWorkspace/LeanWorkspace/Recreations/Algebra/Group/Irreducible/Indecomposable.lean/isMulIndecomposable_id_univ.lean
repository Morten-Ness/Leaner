import Mathlib

variable {ι M G S : Type*} [Monoid M] [CommGroup G] [LinearOrder S]

theorem isMulIndecomposable_id_univ [Subsingleton Mˣ] {x : M} (hx : x ≠ 1) :
    IsMulIndecomposable id Set.univ x ↔ Irreducible x := ⟨fun h ↦ ⟨by simpa, by simpa using h⟩, fun h ↦ by simpa using h.isUnit_or_isUnit⟩

