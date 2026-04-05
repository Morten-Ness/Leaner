import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable [DecidableEq I]

theorem Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle {M : Type*} [CommMonoid M]
    {k l m n : I} {u v : M} (hu : u ≠ 1) (hv : v ≠ 1) :
    (mulSingle k u : I → M) * mulSingle l v = mulSingle m u * mulSingle n v ↔
      k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = n := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hk := congr_fun h k
    have hl := congr_fun h l
    have hm := congr_fun h m
    have hn := congr_fun h n
    grind [mul_one, one_mul, mul_apply]
  · aesop (add simp [mulSingle_apply])

