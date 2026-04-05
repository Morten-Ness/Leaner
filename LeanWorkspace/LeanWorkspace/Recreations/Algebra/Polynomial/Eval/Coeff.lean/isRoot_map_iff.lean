import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] [CommSemiring S] (f : R →+* S)

theorem isRoot_map_iff {R : Type*} [CommRing R] {f : R →+* S} {x : R} {p : R[X]}
    (hf : Function.Injective f) : IsRoot (p.map f) (f x) ↔ IsRoot p x := ⟨fun h => h.of_map hf, fun h => h.map⟩

