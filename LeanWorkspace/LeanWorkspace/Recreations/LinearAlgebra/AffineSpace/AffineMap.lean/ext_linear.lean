import Mathlib

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*} {V3 : Type*}
  {P3 : Type*} {V4 : Type*} {P4 : Type*} [Ring k] [AddCommGroup V1] [Module k V1]
  [AddTorsor V1 P1] [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2] [AddCommGroup V3]
  [Module k V3] [AddTorsor V3 P3] [AddCommGroup V4] [Module k V4] [AddTorsor V4 P4]

theorem ext_linear {f g : P1 →ᵃ[k] P2} (h₁ : f.linear = g.linear) {p : P1} (h₂ : f p = g p) :
    f = g := by
  ext q
  have hgl : g.linear (q -ᵥ p) = toFun g ((q -ᵥ p) +ᵥ q) -ᵥ toFun g q := by simp
  have := f.map_vadd' q (q -ᵥ p)
  rw [h₁, hgl, AffineMap.toFun_eq_coe, AffineMap.map_vadd, AffineMap.linearMap_vsub, h₂] at this
  simpa

