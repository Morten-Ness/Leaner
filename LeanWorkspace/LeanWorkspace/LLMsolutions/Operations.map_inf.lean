import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_inf (S T : Submonoid M) (f : F) (hf : Function.Injective f) :
    (S ⊓ T).map f = S.map f ⊓ T.map f := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy.1, rfl⟩, ⟨y, hy.2, rfl⟩⟩
  · intro hx
    rcases hx with ⟨hxS, hxT⟩
    rcases hxS with ⟨yS, hyS, hxyS⟩
    rcases hxT with ⟨yT, hyT, hxyT⟩
    have h : yS = yT := hf <| hxyS.trans hxyT.symm
    refine ⟨yS, ?_, hxyS⟩
    constructor
    · exact hyS
    · simpa [h] using hyT
