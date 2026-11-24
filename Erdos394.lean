/-
Copyright 2026 Laughing Bear.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib

/-!
# Erdős Problem 394: the lower bound `∑_{n ≤ x} t₂(n) ≫ x² / log x`

A proof of `Erdos394.erdos_394.variants.lower_bound` from google-deepmind/formal-conjectures
(`FormalConjectures/ErdosProblems/394.lean`). The definition of `t`, the API lemma `t_eq_of` and
the `≪` notation are copied verbatim from formal-conjectures.

Proof: `t₂(p) = p - 1` for primes `p`, so the sum is at least `(x/4 - 1)` times the number of
primes in `(x/4, x]`. That number is at least `(θ(x) - θ(x/4)) / log x`, and Chebyshev's bounds in
Mathlib (`Chebyshev.theta_ge`, `Chebyshev.theta_le_log4_mul_x`) give
`θ(x) - θ(x/4) ≥ (log 2 / 2) x - o(x)`.
-/

open Filter Finset Real Asymptotics Chebyshev

/-- From `FormalConjecturesForMathlib/Analysis/Asymptotics/Basic.lean` (verbatim). -/
notation g " ≪ " f => Asymptotics.IsBigO Filter.atTop (g : ℕ → ℝ) (f : ℕ → ℝ)

namespace Erdos394

/--
Let $t_k(n)$ denote the least $m$ such that $n\mid m(m+1)(m+2)\cdots (m+k-1).$
-/
noncomputable def t (k n : ℕ) : ℕ :=
  sInf { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i) }

/-- `t k n = v` when `v` works and nothing positive below it does. -/
theorem t_eq_of {n k v : ℕ} (hv : 0 < v)
    (hdvd : n ∣ ∏ i ∈ range k, (v + i))
    (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    t k n = v := by
  refine le_antisymm (Nat.sInf_le ⟨hv, hdvd⟩) ?_
  by_contra! hc
  have hne : { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i) }.Nonempty := ⟨v, hv, hdvd⟩
  obtain ⟨hpos, hd⟩ := Nat.sInf_mem hne
  exact hlt _ (mem_range.mpr hc) hpos hd

lemma t_two_prime {p : ℕ} (hp : p.Prime) : t 2 p = p - 1 := by
  have h2 := hp.two_le
  refine t_eq_of (by omega) ?_ ?_
  · rw [Finset.prod_range_succ, Finset.prod_range_one]
    have : p - 1 + 1 = p := by omega
    rw [this]
    exact dvd_mul_left _ _
  · intro m hm hm0 hdvd
    rw [Finset.mem_range] at hm
    rw [Finset.prod_range_succ, Finset.prod_range_one, add_zero] at hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact absurd (Nat.le_of_dvd hm0 h) (by omega)
    · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)

/-- The primes in `(x/4, x]`. -/
def S (x : ℕ) : Finset ℕ := (Nat.primesLE x).filter (fun p => x < 4 * p)

lemma mem_S {x p : ℕ} : p ∈ S x ↔ (p ≤ x ∧ p.Prime) ∧ x < 4 * p := by
  simp [S, Nat.mem_primesLE]

/-- The sum of `t₂` dominates the sum of `p - 1` over primes in `(x/4, x]`. -/
lemma sum_ge (x : ℕ) :
    ((S x).card : ℝ) * ((x : ℝ) / 4 - 1) ≤ ∑ n ∈ Icc 1 x, (t 2 n : ℝ) := by
  calc ((S x).card : ℝ) * ((x : ℝ) / 4 - 1)
      ≤ ∑ p ∈ S x, ((p : ℝ) - 1) := by
        rw [← nsmul_eq_mul]
        refine Finset.card_nsmul_le_sum _ _ _ fun p hp => ?_
        have h := (mem_S.1 hp).2
        have : (x : ℝ) < 4 * p := by exact_mod_cast h
        linarith
    _ = ∑ p ∈ S x, (t 2 p : ℝ) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        have hp' := (mem_S.1 hp).1.2
        rw [t_two_prime hp', Nat.cast_sub hp'.one_le, Nat.cast_one]
    _ ≤ ∑ n ∈ Icc 1 x, (t 2 n : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun _ _ _ => by positivity
        obtain ⟨⟨hpx, hp⟩, -⟩ := mem_S.1 hp
        exact Finset.mem_Icc.2 ⟨hp.one_le, hpx⟩

/-- Chebyshev: `θ(x) - θ(x/4)` is at most the log-sum over primes in `(x/4, x]`. -/
lemma theta_sub_le (x : ℕ) :
    θ (x : ℝ) - log 4 * ((x : ℝ) / 4) ≤ ∑ p ∈ S x, log (p : ℝ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Nat.primesLE x) (fun p => x < 4 * p)
    (fun p => log (p : ℝ))
  have hsmall : ∑ p ∈ (Nat.primesLE x).filter (fun p => ¬ x < 4 * p), log (p : ℝ)
      ≤ θ ((x : ℝ) / 4) := by
    rw [theta_eq_sum_primesLE]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => ?_
    · simp only [Finset.mem_filter, Nat.mem_primesLE, not_lt] at hp
      refine Nat.mem_primesLE.2 ⟨Nat.le_floor ?_, hp.1.2⟩
      have : (4 * p : ℝ) ≤ x := by exact_mod_cast hp.2
      linarith
    · exact log_natCast_nonneg p
  have htheta := theta_le_log4_mul_x (x := (x : ℝ) / 4) (by positivity)
  rw [theta_eq_sum_primesLE_log]
  unfold S
  linarith

/-- `log (x + 1) + 2 √x log x = o(x)`. -/
lemma error_isLittleO :
    (fun x : ℝ => log (x + 1) + 2 * √x * log x) =o[atTop] id := by
  have hA : (fun x : ℝ => log (x + 1)) =o[atTop] id := by
    have h1 := Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_atTop_add_const_right atTop 1 tendsto_id)
    have h2 : (fun x : ℝ => x + 1) =O[atTop] id := by
      refine IsBigO.of_bound 2 ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      rw [Real.norm_of_nonneg (by linarith), id, Real.norm_of_nonneg (by linarith)]
      linarith
    exact h1.trans_isBigO h2
  have hB : (fun x : ℝ => 2 * √x * log x) =o[atTop] id := by
    have h1 := isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    have h2 := (isBigO_refl (fun x : ℝ => √x) atTop).mul_isLittleO h1
    have h3 : (fun x : ℝ => √x * x ^ (1 / 2 : ℝ)) =ᶠ[atTop] id := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt hx, id]
    have h4 := (h2.congr_right fun x => rfl).trans_eventuallyEq h3
    have h5 := h4.const_mul_left 2
    refine h5.congr_left fun x => ?_
    ring
  exact hA.add hB

/-- Eventually, the primes in `(x/4, x]` have log-sum at least `(log 2 / 4) x`. -/
lemma eventually_logsum :
    ∀ᶠ x : ℕ in atTop, (log 2 / 4) * (x : ℝ) ≤ ∑ p ∈ S x, log (p : ℝ) := by
  have hb := (error_isLittleO.bound (c := log 2 / 4) (by positivity))
  have hb' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hb
  filter_upwards [hb', eventually_ge_atTop 1] with x hx hx1
  have hθ := theta_ge x
  have hS := theta_sub_le x
  have hlog4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hxpos : (0 : ℝ) ≤ x := by positivity
  have hlogx : 0 ≤ log (x : ℝ) := log_natCast_nonneg x
  have hlog1 : 0 ≤ log ((x : ℝ) + 1) := Real.log_nonneg (by linarith)
  have herr : 0 ≤ log ((x : ℝ) + 1) + 2 * √(x : ℝ) * log x := by positivity
  rw [Real.norm_of_nonneg herr, id, Real.norm_of_nonneg hxpos] at hx
  rw [hlog4] at hS
  nlinarith

/-- **Erdős 394, lower bound.** Same statement as
`Erdos394.erdos_394.variants.lower_bound` in formal-conjectures. -/
theorem erdos_394.variants.lower_bound :
    (fun x ↦ x ^ 2 / Real.log x) ≪
    (fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, (t 2 n : ℝ)) := by
  have hlog2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  refine IsBigO.of_bound (32 / log 2) ?_
  filter_upwards [eventually_logsum, eventually_ge_atTop 8] with x hx h8
  have hx8 : (8 : ℝ) ≤ x := by exact_mod_cast h8
  have hL : 0 < log (x : ℝ) := Real.log_pos (by linarith)
  have hcard : ∑ p ∈ S x, log (p : ℝ) ≤ ((S x).card : ℝ) * log x := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
    obtain ⟨⟨hpx, hp⟩, -⟩ := mem_S.1 hp
    exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpx)
  have hc : (log 2 / 4) * x / log x ≤ ((S x).card : ℝ) := by
    rw [div_le_iff₀ hL]; linarith
  have hsum := sum_ge x
  have hfl : ⌊x⌋₊ = x := Nat.floor_natCast (R := ℕ) x
  rw [hfl]
  have hmain : (log 2 / 32) * ((x : ℝ) ^ 2 / log x) ≤ ∑ n ∈ Icc 1 x, (t 2 n : ℝ) := by
    calc (log 2 / 32) * ((x : ℝ) ^ 2 / log x) = ((log 2 / 4) * x / log x) * (x / 8) := by ring
      _ ≤ ((S x).card : ℝ) * (x / 8) := by gcongr
      _ ≤ ((S x).card : ℝ) * ((x : ℝ) / 4 - 1) := by gcongr; linarith
      _ ≤ _ := hsum
  have hpos : 0 ≤ (x : ℝ) ^ 2 / log x := by positivity
  have hsum0 : 0 ≤ ∑ n ∈ Icc 1 x, (t 2 n : ℝ) := by positivity
  rw [Real.norm_of_nonneg hpos, Real.norm_of_nonneg hsum0]
  calc (x : ℝ) ^ 2 / log x = (32 / log 2) * ((log 2 / 32) * ((x : ℝ) ^ 2 / log x)) := by
        field_simp
    _ ≤ (32 / log 2) * ∑ n ∈ Icc 1 x, (t 2 n : ℝ) := by gcongr

end Erdos394
