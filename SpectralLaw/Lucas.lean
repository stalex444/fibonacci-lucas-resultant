module

public import Mathlib
public import SpectralLaw.Basic

/-!
# SpectralLaw.Lucas — Lucas numbers, the Fibonacci link, Cassini, and `φ^k = F_k φ + F_{k−1}`

The identities the paper's proof of Theorem 2 uses (:61–66): `φ^k = F_k φ + F_{k−1}`, the
Lucas identity `L_k = F_{k+1} + F_{k−1}`, and Cassini's identity. All ring-level facts are
stated for any `φ` with `φ² = φ + 1` in any commutative ring, with `φ̄ = 1 − φ`.
-/

@[expose] public section

namespace SpectralLaw

open Polynomial

@[simp] lemma lucas_zero : lucas 0 = 2 := rfl
@[simp] lemma lucas_one : lucas 1 = 1 := rfl
lemma lucas_add_two (k : ℕ) : lucas (k + 2) = lucas k + lucas (k + 1) := rfl

/-- The Lucas–Fibonacci link `L_{k+1} = F_k + F_{k+2}` (the paper's `L_k = F_{k+1} + F_{k−1}`). -/
theorem lucas_succ_eq_fib (k : ℕ) : lucas (k + 1) = Nat.fib k + Nat.fib (k + 2) := by
  have key : ∀ k : ℕ, lucas (k + 1) = Nat.fib k + Nat.fib (k + 2) ∧
      lucas (k + 2) = Nat.fib (k + 1) + Nat.fib (k + 3) := by
    intro k
    induction k with
    | zero => refine ⟨rfl, ?_⟩; rw [lucas_add_two]; norm_num [Nat.fib_add_two]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [lucas_add_two, ih.1, ih.2]
      have h1 : Nat.fib (k + 1 + 3) = Nat.fib (k + 2) + Nat.fib (k + 3) := Nat.fib_add_two
      have h2 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
      have h3 : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
        exact_mod_cast Nat.fib_add_two
      rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega, h1, h2]
      push_cast
      linear_combination -h3
  exact (key k).1

/-- Control: `L₀ = 2` and `L₅ = 11`. -/
theorem lucas_control : lucas 0 = 2 ∧ lucas 5 = 11 := ⟨rfl, by decide⟩

/-- Cassini, in the form used here: `F_{j+1}² − F_{j+1} F_j − F_j² = (−1)^j`. -/
lemma cassini (j : ℕ) :
    (Nat.fib (j + 1) : ℤ) ^ 2 - Nat.fib (j + 1) * Nat.fib j - (Nat.fib j : ℤ) ^ 2 = (-1) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show j + 1 + 1 = j + 2 by omega, Nat.fib_add_two, pow_succ]
    push_cast
    linear_combination -ih

/-- `L_k ≥ k` and `L_k ≥ 1`. -/
lemma lucas_ge (k : ℕ) : (k : ℤ) ≤ lucas k ∧ 1 ≤ lucas k := by
  have key : ∀ k : ℕ, ((k : ℤ) ≤ lucas k ∧ 1 ≤ lucas k) ∧
      ((k + 1 : ℕ) ≤ lucas (k + 1) ∧ 1 ≤ lucas (k + 1)) := by
    intro k
    induction k with
    | zero => exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [show k + 1 + 1 = k + 2 by omega, lucas_add_two]
      obtain ⟨⟨_, h1⟩, ⟨h2, h3⟩⟩ := ih
      push_cast at h2 ⊢
      constructor <;> linarith
  exact (key k).1

/-- The Lucas numbers are strictly increasing from index 1. -/
lemma lucas_strictMono : StrictMono (fun k => lucas (k + 1)) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  show lucas (k + 1) < lucas (k + 1 + 1)
  rw [show k + 1 + 1 = k + 2 by omega, lucas_add_two]
  linarith [(lucas_ge k).2]

section Ring

variable {R : Type*} [CommRing R] {φ : R}

lemma conj_sq (hφ : φ ^ 2 = φ + 1) : (1 - φ) ^ 2 = (1 - φ) + 1 := by
  linear_combination hφ

lemma mul_conj (hφ : φ ^ 2 = φ + 1) : φ * (1 - φ) = -1 := by
  linear_combination -hφ

/-- `φ^k + φ̄^k = L_k`. -/
lemma pow_add_conj_pow (hφ : φ ^ 2 = φ + 1) (k : ℕ) :
    φ ^ k + (1 - φ) ^ k = (lucas k : R) := by
  have key : ∀ k : ℕ, φ ^ k + (1 - φ) ^ k = (lucas k : R) ∧
      φ ^ (k + 1) + (1 - φ) ^ (k + 1) = (lucas (k + 1) : R) := by
    intro k
    induction k with
    | zero => constructor <;> simp; norm_num
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [show k + 1 + 1 = k + 2 by omega, lucas_add_two]
      push_cast
      rw [← ih.1, ← ih.2]
      linear_combination φ ^ k * hφ + (1 - φ) ^ k * conj_sq hφ
  exact (key k).1

/-- `φ^{k+1} = F_{k+1} φ + F_k`. -/
lemma pow_succ_eq_fib (hφ : φ ^ 2 = φ + 1) (k : ℕ) :
    φ ^ (k + 1) = (Nat.fib (k + 1) : R) * φ + (Nat.fib k : R) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 by omega, Nat.fib_add_two]
    push_cast
    linear_combination φ * ih + (Nat.fib (k + 1) : R) * hφ

end Ring

/-- In `ℤ[φ]`: `φ^k = F_k φ + F_{k−1}` for `k ≥ 1`. -/
theorem phi_pow_eq_fib (k : ℕ) (hk : 1 ≤ k) :
    phi ^ k = (Nat.fib k : AdjoinRoot gZ) * phi + (Nat.fib (k - 1) : AdjoinRoot gZ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact pow_succ_eq_fib rootPhi_sq j

end SpectralLaw
