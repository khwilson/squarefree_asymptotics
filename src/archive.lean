import analysis.p_series
import number_theory.arithmetic_function
import algebra.squarefree
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral
import analysis.special_functions.integrals
import defs
import summability
import lemmas_on_tendsto
import general
import integral_facts

noncomputable theory
-- open_locale classical
open nat finset list finsupp set function filter measure_theory
open_locale classical topological_space interval big_operators filter ennreal asymptotics

namespace squarefree_sums

def coi (f : ℕ → ℝ) := (λ (x : ℝ), f (⌊x⌋₊))

def coi' (f : ℝ → ℝ) := (λ (x : ℝ), f (⌊x⌋₊))

lemma fafa (n : ℕ) (f : ℕ → ℝ) :
∫ (x : ℝ) in ↑n..↑n + 1, f n
=
∫ (x : ℝ) in ↑n..↑n + 1, (coi f) x
:=
begin
  apply interval_integral.integral_congr_ae',
  rw filter.eventually_iff,
  rw measure_theory.mem_ae_iff,
  have : {x : ℝ | x ∈ set.Ioc (n : ℝ) (↑n + 1) → f n = coi f x}ᶜ ⊆ {↑n + 1},
  {
    rw compl_subset_iff_union,
    ext,
    simp,
    by_cases x = n + 1,
    simp [h],
    simp [h],
    intros ha hb,
    let foooo := lt_or_eq_of_le hb,
    simp [h] at foooo,
    rw ← nat.cast_one at foooo,
    rw ← nat.cast_add at foooo,
    unfold coi,
    have fdfdfdfd : 0 ≤ x, exact le_of_lt (calc (0 : ℝ) ≤ n : by simp ... < x : ha),
    have : n ≤ ⌊x⌋₊, exact nat.le_floor (le_of_lt ha),
    have : ⌊x⌋₊ < ↑n + 1, simp [(nat.floor_lt fdfdfdfd).mpr foooo],
    have : ⌊x⌋₊ = n, linarith,
    rw this,
  },
  exact measure_subset_null _ {↑n + 1} this real.volume_singleton,
  simp,
end


lemma convert_finite_sum_to_interval_integral (n : ℕ) (f : ℕ → ℝ) :
∑ (i : ℕ) in finset.range n,
∫ (x : ℝ) in ↑i..↑i + 1,
f i
=
∫ (x : ℝ) in 0..n, (coi f) x
:=
begin
  conv {
    to_lhs,
    congr,
    skip,
    funext,
    rw fafa i f,
  },
  -- Problem: There are a lot of lemmas that show that if a function is constant
  -- on all of ℝ then the function is integrable, but this function is constant _only_
  -- on the interval of integration. This is messing up the parser.
  have hint : ∀ (k : ℕ), k < n → interval_integrable (coi f) measure_theory.measure_space.volume (k : ℝ) ((k : ℝ) + 1),
  {
    intros k hk,
    have : ∃c, ∀ (x : ℝ), x ∈ set.Ioo (k : ℝ) (↑k + 1) → (coi f) x = c, {
      use f k,
      intros x hx,
      unfold coi,
      rw doodoo k x hx,
    },
    exact real_constant_on_interval_integrable k (k + 1) (by linarith) (coi f) this,
  },
  exact interval_integral.sum_integral_adjacent_intervals hint,
end

end squarefree_sums
