# The Fibonacci remainder and Lucas norm of the product resultant for xⁿ − x − 1

For every integer n ≥ 3, a polynomial of degree 2n has a remainder of degree one whose two coefficients are Fibonacci numbers up to a sign correction. The norm of that remainder in the golden quadratic ring is a signed Lucas number. This repository formalizes Theorem 2 of Stephanie Alexander’s *A Fibonacci–Lucas Spectral Law for the Trinomials xⁿ = x + 1* and derives its sharp minimum. [Source paper, eq. (2) and Theorem 2](https://doi.org/10.5281/zenodo.18817597)

## The polynomial and its remainder

Let g(x) = x² − x − 1 and let F₀ = 0, F₁ = 1 and L₀ = 2, L₁ = 1. Both sequences satisfy the Fibonacci recurrence. Eliminate x in the following resultant, retaining t as the polynomial variable.

$$
R_n(t)=\operatorname{Res}_x\bigl(x^2-x-1,\ t^n-tx^{n-1}-x^n\bigr).
$$

If α is either root of g and β ranges over the roots of xⁿ − x − 1, the factors t − αβ give this product resultant, counted with multiplicity. The compared theorems establish the following identities for every n ≥ 3.

1. The whole polynomial is
   $$
   R_n(t)=t^{2n}-L_{n-1}t^{n+1}-L_nt^n+(-1)^{n-1}(t^2+t)+(-1)^n.
   $$
2. Its remainder in ℤ[t] is
   $$
   R_n(t)\bmod(t^2-t-1)=\bigl(-F_{2n}+(-1)^{n+1}\bigr)t-F_{2n-1}.
   $$
3. In ℤ[φ] = ℤ[t]/(t² − t − 1), the algebra norm of the residue is
   $$
   N(R_n(\varphi))=(-1)^{n+1}L_{2n-1}.
   $$
   Its absolute value is at least 11, with equality exactly at n = 3.

At n = 3 the remainder is −7t − 5. The norm of aφ + b is b² + ab − a², so this residue has norm 25 + 35 − 49 = 11. At n = 4 the remainder is −22t − 13 and the norm is −29.

The paper introduces the product polynomial through its resultant and uses a minimal-polynomial description. The formal statements use the resultant itself. Equality with the minimal polynomial of an individual product requires irreducibility. The three statements above hold on the full range n ≥ 3 without an irreducibility hypothesis.

## Relation to prior work

Rush studied the ordinary integer resultants of two Selmer trinomials sⱼ(x) = xʲ − x − 1. His Proposition 3.4 gives Res(s₂, s₂₊ₖ) = (−1)ᵏ − Lₖ + 1. At k = 2n − 1 this already gives −L₂ₙ₋₁. The overlap includes the absolute norms 11 and 29. Alexander’s Theorem 2 gives the linear polynomial before applying the norm, including both Fibonacci coefficients. Its formalization provides an exact calculation for researchers studying Selmer resultants and polynomial recurrences. [Rush, *Fibonacci Quarterly* 50 (2012), Prop. 3.4](https://www.mathstat.dal.ca/FQ/Papers1/50-4/Rush.pdf)

The construction taking products of roots is the multiplicative composed product. Brawley and Carlitz develop that operation and study irreducibility over finite fields. The identities here are in ℤ[t] and its golden quadratic quotient. [Brawley and Carlitz, *Discrete Mathematics* 65 (1987)](https://doi.org/10.1016/0012-365X(87)90135-X)

Two earlier Palomars by Alexander concern the same trinomial family. *The golden family's boundary at n = 3* establishes results about its individual roots rₙ. *The compositum of the two Mahler minimizers* treats the fixed product of the degree-three and degree-four roots, ρQ. This entry examines the products of the degree-two roots with the roots of every degree n ≥ 3. [Golden Family Boundary](https://palomar-registry.org/entry?id=PALOMAR-2026-09-01-000012&version=1) · [Compositum, version 2](https://palomar-registry.org/entry?id=PALOMAR-2026-09-01-000005&version=2)

## Formalization history

Alexander’s earlier Lean file `PdtGoldenResidue.lean` (revision `813b46e265560ff397e365cbd8486e603298a96d`) certified the finite row n = 3 through 8 and identified the quadratic coefficient formula with the algebra norm. Her November 17, 2026 package `SpectralLawPkg` (revision `e8771930171fbccef76fdf9cfd9a4d51d78fc184`) ported the quadratic norm lemmas and established the product-resultant identities for every n ≥ 3. Both predecessors were developed in her private research repository. This standalone release includes the six supporting proof modules and presents the three public challenge statements directly in terms of Mathlib’s resultant.

## Verification

The [challenge](Challenge.lean) defines the resultant using Mathlib, the quotient ring using its modulus, and the Lucas numbers by recurrence. Each [solution](Solution.lean) is checked against the statement of the same name.

| Compared theorem in FibonacciLucasResultant | Conclusion |
| --- | --- |
| `resultant_closed_form` | Full resultant polynomial |
| `fibonacci_remainder` | Both coefficients of the remainder |
| `lucas_norm_and_minimum` | Signed algebra norm, absolute lower bound, and unique equality case |

Use Lean 4.35.0-rc2 and Mathlib revision `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The statement placeholders appear in Challenge.lean. The solutions and supporting proofs are in Solution.lean and SpectralLaw/.

```sh
lake exe cache get
lake build
lake comparator --config comparator.json
```
