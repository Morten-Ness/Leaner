import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem prod_toFinset {M : Type*} [DecidableEq ι] [CommMonoid M] (f : ι → M) :
    ∀ {l : List ι} (_hl : l.Nodup), l.toFinset.prod f = (l.map f).prod
  | [], _ => by simp
  | a :: l, hl => by
    let ⟨notMem, hl⟩ := List.nodup_cons.mp hl
    simp [List.toFinset_cons, notMem, prod_toFinset f hl]
