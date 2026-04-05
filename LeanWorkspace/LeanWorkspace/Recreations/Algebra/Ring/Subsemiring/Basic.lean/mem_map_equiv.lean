import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem mem_map_equiv {f : R ≃+* S} {K : Subsemiring R} {x : S} :
    x ∈ K.map (f : R →+* S) ↔ f.symm x ∈ K := by
  convert @Set.mem_image_equiv _ _ (↑K) f.toEquiv x using 1

