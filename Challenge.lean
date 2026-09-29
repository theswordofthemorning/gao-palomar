module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Log

@[expose] public section

/-!
# Gao's conjecture on consecutive integers under the Collatz map

This file is the human-auditable statement. It imports only Mathlib.

Let `C` be the Collatz map, `C(n) = n / 2` for even `n` and `C(n) = 3n + 1` for
odd `n`. G.-G. Gao, *On consecutive numbers of the same height in the Collatz
problem*, Discrete Math. 112 (1993) 261–267, says that `n` and `n + 1`
*coalesce at step `k`* (p. 264) if

1. `C^k(n) = C^k(n + 1)`;
2. the two trajectories have the same number of halvings among their first
   `k` steps; and
3. the number `1` occurs in neither trajectory (we take the most demanding
   reading: `C^i(n) ≠ 1` and `C^i(n + 1) ≠ 1` for `0 ≤ i ≤ k`).

He defines (p. 265)
`d̄_k = 2^(-k) · #{0 ≤ n < 2^k - 1 : n, n + 1 coalesce at some step j ≤ k}` and
`d(x) = x^(-1) · #{0 ≤ n < x : n, n + 1 coalesce}`, and writes: "The conjecture
asserts that d̄_k → 1 as k → ∞". He adds that it is not easy to determine
whether `d(x)` has a limit.

J. C. Lagarias, *The 3x+1 problem: an annotated bibliography (1963–1999)*,
entry 68, records the conjecture as: the set of `n` such that
`C^k(n) = C^k(n + 1)` for some `k ≤ log₂ n` has natural density one.

Both forms are stated below. Neither says anything about whether trajectories
reach `1`: this is not the `3x + 1` conjecture.
-/

open Filter Topology

namespace GaoCoalescence

/-- The Collatz map on `ℕ`: `n / 2` if `n` is even, `3n + 1` if `n` is odd. -/
def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `halvings k n` is the number of halvings among the first `k` steps of the
trajectory of `n`, that is, the number of even terms among
`n, C(n), …, C^(k-1)(n)`. -/
def halvings : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => (if n % 2 = 0 then 1 else 0) + halvings k (collatz n)

/-- Gao's coalescence of `n` and `n + 1` at step `k`: the trajectories agree at
step `k`, have the same number of halvings in their first `k` steps, and
neither of them contains `1` among its terms of index `0, …, k`. -/
def Coalesce (n k : ℕ) : Prop :=
  collatz^[k] n = collatz^[k] (n + 1) ∧ halvings k n = halvings k (n + 1) ∧
    ∀ i, i ≤ k → collatz^[i] n ≠ 1 ∧ collatz^[i] (n + 1) ≠ 1

open Classical in
/-- Gao's `d̄_k`: the number of `0 ≤ n < 2^k - 1` such that `n` and `n + 1`
coalesce at some step `j ≤ k`, divided by `2^k`. -/
noncomputable def dbar (k : ℕ) : ℝ :=
  (((Finset.range (2 ^ k - 1)).filter (fun n => ∃ j, j ≤ k ∧ Coalesce n j)).card : ℝ) / 2 ^ k

open Classical in
/-- Gao's `d(x)`: the proportion of `0 ≤ n < x` such that `n` and `n + 1`
coalesce at some step, with no bound on the step. -/
noncomputable def d (x : ℕ) : ℝ :=
  (((Finset.range x).filter (fun n => ∃ j, Coalesce n j)).card : ℝ) / x

open Classical in
/-- **Gao's conjecture, in Lagarias's form.** The set of `m` such that
`C^k(m) = C^k(m + 1)` for some `k ≤ log₂ m` has natural density one. -/
theorem lagarias_form :
    Tendsto (fun N : ℕ => (((Finset.range N).filter
      (fun m => ∃ k, k ≤ Nat.log 2 m ∧ collatz^[k] m = collatz^[k] (m + 1))).card : ℝ) / N)
      atTop (𝓝 1) := by
  sorry

/-- **Gao's conjecture, in Gao's form.** `d̄_k → 1`; moreover `d(x) → 1`. -/
theorem gao_form : Tendsto dbar atTop (𝓝 1) ∧ Tendsto d atTop (𝓝 1) := by
  sorry

end GaoCoalescence
