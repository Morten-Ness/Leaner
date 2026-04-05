import Mathlib

theorem Group.ext {G : Type*} ⦃g₁ g₂ : Group G⦄
    (h_mul : (letI := g₁; HMul.hMul : G → G → G) = (letI := g₂; HMul.hMul : G → G → G)) :
    g₁ = g₂ := by
  have h₁ : g₁.one = g₂.one := congr_arg (·.one) (Monoid.ext h_mul)
  let f : @MonoidHom G G g₁.toMulOne g₂.toMulOne :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  exact
    Group.toDivInvMonoid_injective
      (DivInvMonoid.ext h_mul
        (funext <| @MonoidHom.map_inv G G g₁ g₂.toDivisionMonoid f))

