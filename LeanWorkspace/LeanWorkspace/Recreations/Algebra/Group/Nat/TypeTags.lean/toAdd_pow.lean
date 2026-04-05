import Mathlib

theorem toAdd_pow (a : Multiplicative ℕ) (b : ℕ) : (a ^ b).toAdd = a.toAdd * b := mul_comm _ _

