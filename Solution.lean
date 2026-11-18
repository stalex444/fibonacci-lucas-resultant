module

public import SpectralLaw.Resultant
public import SpectralLaw.Consequences

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

private theorem lucas_eq (n : ℕ) : lucas n = SpectralLaw.lucas n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k h₀ h₁ => simp only [lucas, SpectralLaw.lucas, h₀, h₁]

private theorem product_eq (n : ℕ) (hn : 3 ≤ n) :
    productResultant n = SpectralLaw.P2 n := SpectralLaw.P2_eq_resultant n hn

/-- The full product resultant is a polynomial with explicit Lucas coefficients. -/
theorem resultant_closed_form (n : ℕ) (hn : 3 ≤ n) :
    productResultant n =
      X ^ (2*n) - C (lucas (n-1)) * X ^ (n+1) - C (lucas n) * X ^ n
      + C ((-1 : ℤ) ^ (n-1)) * X ^ 2 + C ((-1 : ℤ) ^ (n-1)) * X + C ((-1 : ℤ) ^ n) := by
  rw [product_eq n hn]
  simp only [SpectralLaw.P2, lucas_eq]

/-- The linear remainder of the product resultant modulo the golden polynomial. -/
theorem fibonacci_remainder (n : ℕ) (hn : 3 ≤ n) :
    productResultant n %ₘ golden =
      C (-(Nat.fib (2*n) : ℤ) + (-1) ^ (n+1)) * X + C (-(Nat.fib (2*n-1) : ℤ)) := by
  rw [product_eq n hn]
  exact SpectralLaw.P2_mod n hn

/-- The actual algebra norm in ℤ[t]/(t²−t−1), with its sharp absolute minimum. -/
theorem lucas_norm_and_minimum (n : ℕ) (hn : 3 ≤ n) :
    let value := Algebra.norm ℤ (AdjoinRoot.mk golden (productResultant n))
    value = (-1 : ℤ) ^ (n+1) * lucas (2*n-1) ∧ 11 ≤ |value| ∧ (|value| = 11 ↔ n = 3) := by
  dsimp only
  rw [product_eq n hn, lucas_eq]
  have hnorm : Algebra.norm ℤ (AdjoinRoot.mk golden (SpectralLaw.P2 n)) =
      SpectralLaw.goldNorm (SpectralLaw.P2 n) := SpectralLaw.norm_mk_eq_goldNorm _
  simp only [hnorm]
  exact ⟨(SpectralLaw.P2_goldNorm n hn).1, SpectralLaw.P2_goldNorm_ge n hn,
    SpectralLaw.P2_goldNorm_eq_eleven_iff n hn⟩

end FibonacciLucasResultant
