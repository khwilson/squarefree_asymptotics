import number_theory.arithmetic_function
import algebra.squarefree
import algebra.order.floor
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral
import general
import defs
import lemmas_on_defs
import multiplicativity

noncomputable theory
open nat finset function filter
open_locale topological_space interval big_operators filter asymptotics arithmetic_function

namespace squarefree_sums


lemma tμ_ind {p i : ℕ} (hp : nat.prime p) :
tμ (p ^ (i + 1)) = tμ (p ^ i) + sμ (p ^ (i + 1)) :=
begin
  unfold tμ,
  unfold sμ,
  simp,
  unfold sμ',

  rw nat.divisors_prime_pow hp (i + 1),
  rw ← Ico_eq_range,
  have munion : finset.map {to_fun := pow p, inj' := _} (finset.Ico 0 (i + 1 + 1)) =
  (finset.map {to_fun := pow p, inj' := _} (finset.Ico 0 (i + 1))) ∪
  (finset.map {to_fun := pow p, inj' := _} (finset.Ico (i + 1) (i + 1 + 1))), {
    have : (finset.Ico 0 (i + 1 + 1)) = (finset.Ico 0 (i + 1)) ∪ (finset.Ico (i + 1) (i + 1 + 1)), {
      simp,
      rw range_succ,
      rw finset.union_singleton,
    },
    rw this,
    rw map_union,
  },
  have udisjoint : disjoint
  (finset.map {to_fun := pow p, inj' := _} (finset.Ico 0 (i + 1)))
  (finset.map {to_fun := pow p, inj' := _} (finset.Ico (i + 1) (i + 1 + 1))), {
    rw disjoint_iff_ne,
    intros a ha b hb,
    rw finset.mem_map at ha,
    rcases ha with ⟨ia, hia, via⟩,
    rw finset.mem_map at hb,
    rcases hb with ⟨ib, hib, vib⟩,
    simp at via,
    simp at vib,
    by_contradiction H,
    rw ← H at vib,
    rw ← vib at via,
    rw ← exp_eq_iff_pow_eq hp.two_le at via,
    simp at hia,
    simp at hib,
    linarith [vib, hia, hib, via],
  },
  rw munion,
  rw finset.sum_union udisjoint,
  simp,
  rw nat.divisors_prime_pow hp i,
  simp,
end

lemma barrr {i p : ℕ} (hp : nat.prime p) : 2 ≤ i → squarefree_nat (p^i) = 0 :=
begin
  intros hi,
  unfold squarefree_nat,
  simp,
  unfold squarefree_nat',
  simp,
  by_contradiction H,
  have : p * p ∣ p ^ i, {
    obtain ⟨i', hi'⟩ : ∃ i', i = 2 + i', exact two_add hi,
    rw hi',
    rw pow_add,
    rw pow_two,
    exact dvd_mul_right (p * p) (p ^ i'),
  },
  unfold squarefree at H,
  specialize H p this,
  simp at H,
  rw H at hp,
  exact not_prime_one hp,
end

--------------------------------------------------------------------------
--         THEOREM 1: SQUAREFREE CAN BE WRITTEN AS SUM OF MU
--------------------------------------------------------------------------
lemma case_0 (p : ℕ) (hp : nat.prime p) : squarefree_nat p = tμ 1 + sμ p :=
begin
  unfold squarefree_nat,
  unfold sμ,
  simp,
  unfold squarefree_nat',
  unfold sμ',
  simp [(prime_iff.mp hp).squarefree, is_multiplicative_tμ, ssqrt_prime hp],
end

lemma case_1 (p : ℕ) (hp : nat.prime p) (hi : squarefree_nat p = tμ p) : squarefree_nat (p ^ 2) = tμ p + sμ (p ^ 2) :=
begin
  rw barrr hp (calc 2 ≤ 2 : by linarith),
  rw ← hi,
  unfold sμ,
  unfold squarefree_nat,
  simp,
  unfold squarefree_nat',
  unfold sμ',
  simp [(prime_iff.mp hp).squarefree],
  rw pow_two p,
  rw ssqrt_eq,
  rw moebius_of_prime hp,
  ring,
end

theorem squarefree_nat_eq_tμ : squarefree_nat = tμ :=
begin
  rw arithmetic_function.is_multiplicative.eq_iff_eq_on_prime_powers squarefree_nat is_multiplicative_squarefree_nat tμ is_multiplicative_tμ,
  intros p i hp,
  induction i with i hi,
  simp [is_multiplicative_tμ, is_multiplicative_squarefree_nat],
  rw tμ_ind hp,

  by_cases c1 : i = 0,
  simp [c1, case_0 p hp],

  by_cases c2 : i = 1,
  simp [c2] at hi,
  simp [c2, case_1 p hp hi],

  have : 2 ≤ i, exact two_le_nat_iff_not_zero_one.mpr ⟨c1, c2⟩,
  rw ← hi,
  simp [barrr hp this, barrr hp (le_of_lt (calc 2 ≤ i : this ... < i.succ : lt_succ_self i))],

  simp [sμ_prime_pow_le_three p (i + 1) hp (by linarith)],
end


--------------------------------------------------------------------
--       REWRITE tμ IN A WAY MORE CONDUCIVE TO SUM MANIPULATION
--------------------------------------------------------------------

lemma blah {n : ℕ} : μ (ssqrt n) = ite (square n) (μ (sqrt n)) 0 :=
begin
  unfold ssqrt,
  by_cases square n,
  simp [h],
  simp [h],
end

lemma ifififif {n : ℕ} : set.bij_on (λ i, sqrt i) (finset.filter square n.divisors) (finset.filter (λ x, x ^ 2 ∣ n) (finset.Icc 1 n)) :=
begin
  refine ⟨(λ x hx, _), ⟨_, _⟩⟩,
  simp only [mem_filter, mem_coe, ne.def, mem_divisors] at hx,
  simp only [coe_filter, coe_Icc, set.mem_sep_eq, set.mem_Icc],
  obtain ⟨⟨hx_dvd_n, hn_ne_zero⟩, ⟨x', hx'⟩⟩ := hx,
  have hx_ne_zero : x ≠ 0,
  { by_contradiction H, rw H at hx_dvd_n, exact hn_ne_zero (zero_dvd_iff.mp hx_dvd_n), },
  have one_le_x : 1 ≤ x, exact one_le_iff_ne_zero.mpr hx_ne_zero,
  refine ⟨⟨_, _⟩, _⟩,
  rw [←sqrt_one],
  exact sqrt_le_sqrt one_le_x,
  calc sqrt x ≤ x : x.sqrt_le_self
    ... ≤ n : le_of_dvd (zero_lt_iff.mpr hn_ne_zero) hx_dvd_n,
  rw pow_two at hx',
  rwa [hx', sqrt_eq x', pow_two, ←hx'],

  intros x hx y hy hf,
  simp only [mem_filter, mem_coe, ne.def, mem_divisors] at hx,
  simp only [mem_filter, mem_coe, ne.def, mem_divisors] at hy,
  obtain ⟨⟨hy_dvd_n, hn_ne_zero⟩, ⟨x', hx'⟩⟩ := hx,
  obtain ⟨⟨hy_dvd_n, _⟩, ⟨y', hy'⟩⟩ := hy,
  simp only at hf,
  rw pow_two at hx',
  rw pow_two at hy',
  rw [hx', hy', sqrt_eq x', sqrt_eq y'] at hf,
  rw hf at hx',
  calc x = y' * y' : hx' ... = y : hy'.symm,

  intros y hy,
  simp only [coe_filter, coe_Icc, set.mem_sep_eq, set.mem_Icc] at hy,
  obtain ⟨⟨hone_le_y, hy_le_n⟩, ⟨y', hy'⟩⟩ := hy,
  rw pow_two at hy',
  simp only [coe_filter, set.mem_sep_eq, set.mem_image, mem_coe, ne.def, mem_divisors],
  use y * y,
  exact ⟨⟨⟨dvd.intro y' (eq.symm hy'), (by linarith)⟩, (by {use y, rw pow_two} )⟩, sqrt_eq y⟩,
end

lemma finset.sum_bij_on
(f : ℕ → ℤ) (g : ℕ → ℕ) (s t : finset ℕ) (hg : set.bij_on g t s) :
∑ i in t, f (g i) = ∑ i in s, f i :=
begin
  rw [←finsum_mem_coe_finset, ←finsum_mem_coe_finset],
  exact finsum_mem_eq_of_bij_on g hg (λ _ _, rfl),
end

lemma rw_tμ {n : ℕ}: tμ n = ∑ d in finset.Icc 1 n, ite (d ^ 2 ∣ n) (μ d) 0 :=
begin
  unfold tμ,
  simp,
  unfold sμ,
  simp,
  unfold sμ',
  conv {
    to_lhs,
    congr,
    skip,
    funext,
    rw blah,
  },
  rw [sum_ite, sum_ite],
  simp,
  rw [←finsum_mem_coe_finset, ←finsum_mem_coe_finset],
  exact finsum_mem_eq_of_bij_on _ ifififif (λ _ _, rfl),
end



end squarefree_sums
