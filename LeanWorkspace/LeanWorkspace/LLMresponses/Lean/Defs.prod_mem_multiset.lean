FAIL
import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_mem_multiset [DecidableEq ι] (m : Multiset ι) (f : { x // x ∈ m } → M) (g : ι → M)
    (hfg : ∀ x, f x = g x) : ∏ x : { x // x ∈ m }, f x = ∏ x ∈ m.toFinset, g x := by
  classical
  let s : Finset { x // x ∈ m } := m.attach.toFinset
  have hs : s = Finset.univ := by
    ext x
    simp [s]
  calc
    ∏ x : { x // x ∈ m }, f x = ∏ x in s, f x := by
      rw [hs]
    _ = ∏ x in m.attach.toFinset, g x.1 := by
      unfold s
      refine Finset.prod_congr rfl ?_
      intro x hx
      exact hfg x
    _ = ∏ x in m.toFinset.attach, g x.1 := by
      rw [Multiset.toFinset_attach]
    _ = ∏ x in m.toFinset, g x := by
      exact Finset.prod_attach _ _
