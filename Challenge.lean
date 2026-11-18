module

public import Mathlib

@[expose] public section

namespace FibonacciLucasResultant

open Polynomial

/-- The modulus in the variable t. -/
noncomputable def golden : ℤ[X] := X ^ 2 - X - 1

/-- Eliminate x, keeping t as the polynomial variable in the coefficient ring. -/
noncomputable def productResultant (n : ℕ) : ℤ[X] :=
  resultant (X ^ 2 - X - 1 : ℤ[X][X]) (C (X ^ n) - C X * X ^ (n - 1) - X ^ n)

/-- The Lucas sequence, indexed from L₀ = 2 and L₁ = 1. -/
def lucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | k + 2 => lucas k + lucas (k + 1)

/-- The full product resultant is a polynomial with explicit Lucas coefficients. -/
theorem resultant_closed_form (n : ℕ) (hn : 3 ≤ n) :
    productResultant n =
      X ^ (2*n) - C (lucas (n-1)) * X ^ (n+1) - C (lucas n) * X ^ n
      + C ((-1 : ℤ) ^ (n-1)) * X ^ 2 + C ((-1 : ℤ) ^ (n-1)) * X + C ((-1 : ℤ) ^ n) := by
  sorry

/-- The linear remainder of the product resultant modulo the golden polynomial. -/
theorem fibonacci_remainder (n : ℕ) (hn : 3 ≤ n) :
    productResultant n %ₘ golden =
      C (-(Nat.fib (2*n) : ℤ) + (-1) ^ (n+1)) * X + C (-(Nat.fib (2*n-1) : ℤ)) := by
  sorry

/-- The actual algebra norm in ℤ[t]/(t²−t−1), with its sharp absolute minimum. -/
theorem lucas_norm_and_minimum (n : ℕ) (hn : 3 ≤ n) :
    let value := Algebra.norm ℤ (AdjoinRoot.mk golden (productResultant n))
    value = (-1 : ℤ) ^ (n+1) * lucas (2*n-1) ∧ 11 ≤ |value| ∧ (|value| = 11 ↔ n = 3) := by
  sorry

end FibonacciLucasResultant
