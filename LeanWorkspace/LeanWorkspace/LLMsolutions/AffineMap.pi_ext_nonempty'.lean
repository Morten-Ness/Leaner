FAIL
import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [Ring k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2] [AddTorsor V2 P2]

variable [AddCommGroup V3] [AddTorsor V3 P3] [Module k V1] [Module k V2] [Module k V3]

variable {ι : Type*} {φv φp : ι → Type*} [(i : ι) → AddCommGroup (φv i)]
  [(i : ι) → Module k (φv i)] [(i : ι) → AddTorsor (φv i) (φp i)]

variable (fp : (i : ι) → (P1 →ᵃ[k] φp i)) (fv : (i : ι) → (P1 →ᵃ[k] φv i))
  (f' : ι → P1 →ᵃ[k] P2)

variable [Finite ι] [DecidableEq ι] {f g : ((i : ι) → φv i) →ᵃ[k] P2}

theorem pi_ext_nonempty' [Nonempty ι] (h : ∀ i, f.comp (LinearMap.single _ _ i).toAffineMap =
    g.comp (LinearMap.single _ _ i).toAffineMap) : f = g := by
  let i0 : ι := Classical.choice ‹Nonempty ι›
  have hconst : f 0 = g 0 := by
    have h0 := congrArg (fun F => F 0) (h i0)
    simpa using h0
  have hlin : f.linear = g.linear := by
    ext x i
    have hi := congrArg (fun F => F (x i)) (h i)
    simpa [AffineMap.comp_apply] using hi
  ext x
  rw [show f x = f.linear x +ᵥ f 0 by
    simpa using (AffineMap.apply_eq_lineMap_vadd (f := f) x 0)]
  rw [show g x = g.linear x +ᵥ g 0 by
    simpa using (AffineMap.apply_eq_lineMap_vadd (f := g) x 0)]
  rw [hlin, hconst]
