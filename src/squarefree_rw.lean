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
  simp [prime_squarefree hp, is_multiplicative_tμ, ssqrt_prime hp],
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
  simp [prime_squarefree hp],
  rw pow_two p,
  rw ssqrt_eq,
  rw moebius_of_prime hp,
  ring,
end

theorem squarefree_nat_eq_tμ : squarefree_nat = tμ :=
begin
  rw multiplicative_eq_iff_eq_on_prime_powers is_multiplicative_squarefree_nat is_multiplicative_tμ,
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

lemma blah {n : ℕ} : μ (ssqrt n) = ite (is_square n) (μ (sqrt n)) 0 :=
begin
  unfold ssqrt,
  by_cases is_square n,
  simp [h],
  simp [h],
end

lemma ifififif {n : ℕ} : set.bij_on (λ i, sqrt i) (finset.filter is_square n.divisors) (finset.filter (λ x, x ^ 2 ∣ n) (finset.Icc 1 n)) :=
begin
  unfold set.bij_on,
  unfold set.maps_to,
  split,
  intros x hx,
  simp at hx,
  simp,
  split,
  split,
  have : x ≠ 0, {
    by_contradiction H,
    rw H at hx,
    exact hx.left.right (zero_dvd_iff.mp hx.left.left),
  },
  exact one_le_sqrt (one_le_iff_ne_zero.mpr this),
  have : x ≤ n, exact le_of_dvd (zero_lt_iff.mpr hx.left.right) hx.left.left,
  calc sqrt x ≤ sqrt n : sqrt_le_sqrt this
    ... ≤ n : sqrt_le_self n,
  rcases hx.right with ⟨x', hx'⟩,
  rw ← hx',
  rw sqrt_eq,
  rw pow_two,
  rw hx',
  exact hx.left.left,
  split,
  unfold set.inj_on,
  intros x hx y hy hf,
  simp at hx,
  simp at hy,
  rcases hx.right with ⟨x', hx'⟩,
  rcases hy.right with ⟨y', hy'⟩,
  rw [← hx', ← hy', sqrt_eq, sqrt_eq] at hf,
  calc x = x' * x' : hx'.symm
    ... = y' * y' : by rw hf
    ... = y : hy',
  unfold set.surj_on,
  -- Why so many unfolds? Why doesn't rw subset_iff work?
  unfold has_subset.subset,
  unfold set.subset,
  intros a ha,
  simp at ha,
  simp,
  use a^2,
  split,
  split,
  split,
  exact ha.right,
  linarith,
  use a,
  rw pow_two,
  rw [pow_two, sqrt_eq],
end

/- This repackackges finset.sum_bij as specifying the _forward_ function -/
lemma finset.sum_bij''
(f : ℕ → ℤ) (g : ℕ → ℕ) (s t : finset ℕ) (hg : set.bij_on g t s) :
∑ i in t, f (g i) = ∑ i in s, f i :=
begin
  rcases hg with ⟨hg1, hg2, hg3⟩,
  apply finset.sum_bij,

  have : ∀ (a : ℕ) (ha : a ∈ t), (λ (b : ℕ) (H : b ∈ t), g b) a ha ∈ s, {
    intros a ha,
    simp,
    unfold set.maps_to at hg1,
    exact hg1 ha,
  },
  exact this,
  intros a ha,
  congr,
  intros a b ha hb hginv,
  unfold set.inj_on at hg2,
  simp at hginv,
  exact hg2 ha hb hginv,
  intros b hb,
  unfold set.surj_on at hg3,
  simp,
  unfold set.image at hg3,
  simp at hg3,
  unfold has_subset.subset at hg3,
  unfold set.subset at hg3,
  specialize hg3 hb,
  simp at hg3,
  rcases hg3 with ⟨a', ha', ha''⟩,
  use a',
  exact ⟨ha', ha''.symm⟩,
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
  apply finset.sum_bij'',
  exact ifififif,
end



end squarefree_sums
