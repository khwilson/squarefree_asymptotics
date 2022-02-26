import analysis.p_series
import number_theory.arithmetic_function
import topology.algebra.infinite_sum
import algebra.squarefree
import data.list.intervals
import tactic


noncomputable theory
-- open_locale classical
open finset list finsupp
open_locale big_operators

namespace nat
namespace arithmetic_function


/-
  First, let's define a version of the squarefree function which yields an integer
  instead of a boolean. We'll prove that this function is arithmetic and multiplicative
-/
def squarefree_nat (n : ℕ) := if squarefree n then (1 : ℤ) else (0 : ℤ)

def squarefree_nat' : arithmetic_function ℤ :=
⟨
  squarefree_nat,
  (by dec_trivial)
⟩

/-
  Next, we'll define another way of writing this function as a sum over square divisors.
  This function turns out to _also_ be multiplicative
-/
def is_square (n : ℕ) : Prop := ∃ s, s * s = n

instance : decidable_pred (is_square : ℕ → Prop)
| n := decidable_of_iff' _ (nat.exists_mul_self n)

@[simp] lemma ffffactorization_prod_pow_eq_self {n : ℕ} (hn : n ≠ 0) : n.factorization.prod has_pow.pow = n :=
begin
  --simp only [←prod_to_multiset, factorization, multiset.coe_prod, multiset.to_finsupp_to_multiset],
  simp only [←prod_to_multiset, factorization, multiset.coe_prod, multiset.to_finsupp_to_multiset],
  exact prod_factors hn.bot_lt,
end

lemma asdf_strong (N : ℕ) : ∀ (n : ℕ), n ≤ N → n ≠ 0 → ∀ (f g : ℕ → ℕ → ℕ), n.factorization.prod f * n.factorization.prod g = n.factorization.prod (f * g) :=
begin
  induction N with N hN,
  intros n hN,
  have : n = 0, linarith,
  simp [this],
  intros n hN,
  by_cases n = 1,
  simp [h],
  intros n_ne_zero f g,



end

lemma asdf {n : ℕ} (hn : n ≠ 0) (f g : ℕ → ℕ → ℕ) : n.factorization.prod f * n.factorization.prod g = n.factorization.prod (f * g) :=
begin
  induction n,
  simp,
  by_cases n_n = 0,
  simp [h],

end

lemma is_square_iff_factorization_all_even {n : ℕ} : is_square n ↔ ∀ (p : ℕ), even (n.factorization p) :=
begin
  split,
  rintros ⟨s, hs⟩,
  intros p,
  unfold even,
  use s.factorization p,
  by_cases n = 0,
  simp [h] at hs,
  simp [h, hs],
  have : s ≠ 0, { sorry, },
  rw ← hs,
  have : (s * s).factorization = s.factorization + s.factorization, {exact factorization_mul this this,},
  rw this,
  simp,
  ring,
  intros h,
  unfold even at h,
  choose u hu using h,
  use n.factorization.prod (has_pow.pow ∘ u),

  simp only [factorization, ← prod_to_multiset, multiset.coe_prod, multiset.to_finsupp_to_multiset],

  -- ⟨λ p, (h n).intro p⟩,

  sorry,
end


lemma is_multiplicative.is_square {a b : ℕ} (hab : a.coprime b) : is_square (a * b) ↔ is_square a ∧ is_square b :=
begin
  split,
  intros hsquare,
  unfold is_square at hsquare,
  cases hsquare with s hs,
  sorry,
  rintros ⟨⟨sa, hsa⟩, ⟨sb, hsb⟩⟩,
  use sa * sb,
  have : sa * sb * (sa * sb) = (sa * sa) * (sb * sb), { ring, },
  rw [this, hsa, hsb],
end

def moebius_of_sqrt (n : ℕ) : ℤ := ite (is_square n) (moebius (sqrt n)) 0

def moebius_of_sqrt' : arithmetic_function ℤ :=
⟨
  moebius_of_sqrt,
  (by simp [moebius_of_sqrt])
⟩

lemma is_multiplicative_moebius : is_multiplicative moebius :=
begin
  sorry,
end

lemma is_multiplicative.moebius_of_sqrt : is_multiplicative moebius_of_sqrt' :=
begin
  unfold is_multiplicative,
  split,
  unfold moebius_of_sqrt',
  simp,
  unfold moebius_of_sqrt,
  have : is_square 1, {
    unfold is_square,
    use 1,
    ring,
  },
  simp [this],
  have : sqrt 1 = 1, {
    symmetry,
    rw eq_sqrt,
    simp,
    linarith,
  },
  rw this,
  simp,

  intros m n hmn_coprime,
  unfold moebius_of_sqrt',
  simp,
  unfold moebius_of_sqrt,
  by_cases hm : is_square m,
  {
    by_cases hn : is_square n,
    {
      have hmn : is_square (m * n),
      {
        apply (is_multiplicative.is_square hmn_coprime).mpr,
        exact ⟨hm, hn⟩,
      },
      simp [hm, hn, hmn],
      unfold is_square at hm,
      cases hm with m' hm',
      have : m' = sqrt m, {
        rw eq_sqrt,
        simp [hm'],
        linarith,
      },
      rw ← this,

      unfold is_square at hn,
      cases hn with n' hn',
      have : n' = sqrt n, {
        rw eq_sqrt,
        simp [hn'],
        linarith,
      },
      rw ← this,

      have : m' * n' = sqrt (m * n), {
        rw eq_sqrt,
        split,
        have dumb : m' * n' * (m' * n') = (m' * m') * (n' * n'), {ring,},
        rw dumb,
        rw hm',
        rw hn',
        have dumb : (m' * n' + 1) * (m' * n' + 1) = (m' * m') * (n' * n') + 2 * m' * n' + 1, {ring,},
        rw [dumb, hm', hn'],
        have m'_ge_0 : 0 ≤ m', { simp, },
        have n'_ge_0 : 0 ≤ n', { simp, },
        have mn'_ge_0 : 0 ≤ m' * n', { simp, },
        have mmnn'_ge_0 : 0 ≤ 2 * m' * n', { simp, },
        calc m * n < m * n + 1 : by linarith
          ... = m * n + 0 + 1 : by simp
          ... ≤ m * n + 2 * m' * n' + 1 : by simp,
      },
      rw ← this,
      have m'_dvd_m : m' ∣ m, { exact dvd.intro m' hm', },
      have n'_dvd_n : n' ∣ n, { exact dvd.intro n' hn', },

      have part1 : m'.coprime n, {
        apply coprime.coprime_dvd_left,
        exact m'_dvd_m,
        exact hmn_coprime,
      },
      have part2 : m.coprime n', {
        apply coprime.coprime_dvd_right,
        exact n'_dvd_n,
        exact hmn_coprime,
      },
      have : m'.coprime n', {
        exact coprime.coprime_dvd_left m'_dvd_m part2,
      },
      simp [is_multiplicative_moebius, this],
    },
    {
      have hmn : ¬ is_square (m * n),
      {
        by_contradiction H,
        rw is_multiplicative.is_square hmn_coprime at H,
        exact H.right hn,
      },
      simp [hm, hn, hmn],
    },
  },
  {
    have hmn : ¬ is_square (m * n),
    {
      by_contradiction H,
      rw is_multiplicative.is_square hmn_coprime at H,
      exact H.left hm,
    },
    simp [hm, hn, hmn],
  },
end

def squarefree_nat_as_moebius_sum' (n : ℕ) : arithmetic_function ℤ  :=
⟨λ n, ∑ d in divisors n, moebius_of_sqrt' d, by simp⟩

lemma zeta_mul_moebius_of_sqrt_eq_squarefree_nat : zeta * moebius_of_sqrt' = squarefree_nat_as_moebius_sum' :=
begin

end

end arithmetic_function
end nat