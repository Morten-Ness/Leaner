FAIL
import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem prod_bot_sup_bot_prod (s : Submonoid M) (t : Submonoid N) :
    (Submonoid.prod s ⊥) ⊔ (Submonoid.prod ⊥ t) = Submonoid.prod s t := by
  ext x
  constructor
  · intro hx
    exact hx.elim
      (fun hxst => ⟨hxst.1, by simpa using hxst.2⟩)
      (fun hxt => ⟨by simpa using hxt.1, hxt.2⟩)
  · intro hx
    rcases hx with ⟨hx1, hx2⟩
    apply le_sup_left
    exact ⟨hx1, by simpa using (show (x.2 : N) = 1 from Subsingleton.elim _ _) ▸ Submonoid.one_mem ⊥⟩
