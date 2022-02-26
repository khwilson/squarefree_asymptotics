import analysis.p_series
import number_theory.arithmetic_function
import topology.algebra.infinite_sum
import algebra.squarefree
import data.list.intervals
import tactic


noncomputable theory
-- open_locale classical
-- open_locale big_operators

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

def squarefree_nat_as_moebius_sum (n : ℕ) :=
multiset.sum (multiset.map moebius (multiset.map sqrt (finset.filter is_square n.divisors).val))

def squarefree_nat_as_moebius_sum' : arithmetic_function ℤ :=
⟨
  squarefree_nat_as_moebius_sum,
  (by dec_trivial)
⟩



lemma asdfasdf (m n : ℕ) : m ∣ n ∧ ¬ squarefree m → ¬ squarefree n :=
begin
  rintros ⟨aa, bb⟩,
  unfold squarefree at bb,
  push_neg at bb,
  cases bb with x hx,
  rcases hx with ⟨hxx, hxy⟩,
  unfold squarefree,
  push_neg,
  use x,
  split,
  transitivity m,
  exact hxx,
  exact aa,
  exact hxy,
end

lemma prime_pow_dvd_mul_of_coprime {p i a b : ℕ} (pp : nat.prime p) (hi : 1 ≤ i) (hab : a.coprime b) :
p^i ∣ a * b ↔ (p^i ∣ a ∧ ¬ (p ∣ b)) ∨ (p^i ∣ b ∧ ¬ (p ∣ a)) :=
begin
  split,
  {
    intro h,
    induction i with n hn,

    -- The base case i = 0 is not true by assumption
    linarith [hi],

    -- The true base case is when n = 0
    -- We don't use the inductive assumption in the following because it's not true
    by_cases bound : n = 0,
    have : n.succ = 1, { exact congr_arg succ bound, },
    rw this at *,
    simp at h,
    simp,
    have fdfd : p ∣ a ∨ p ∣ b, { exact (prime.dvd_mul pp).mp h, },
    cases fdfd,
    have dfdf : ¬ p ∣ b, {
      by_contradiction H,
      have aaaaa : p ∣ a.gcd b, exact dvd_gcd fdfd H,
      have bbbbb : p ≤ a.gcd b, { sorry, },
      have : 1 < a.gcd b, {
        calc 1 < p : by { exact prime.one_lt pp, }
          ... ≤ a.gcd b : bbbbb,
      },
      unfold coprime at hab,
      linarith [hab, this],
    },
    simp [fdfd, dfdf],

    -- This is the exact same as above
    have dfdf : ¬ p ∣ a, {
      by_contradiction H,
      have aaaaa  : p ∣ a.gcd b, exact dvd_gcd H fdfd,
      have bbbbb : p ≤ a.gcd b, { sorry, },
      have : 1 < a.gcd b, {
        calc 1 < p : by { exact prime.one_lt pp, }
          ... ≤ a.gcd b : bbbbb,
      },
      unfold coprime at hab,
      linarith [hab, this],
    },
    simp [fdfd, dfdf],

    -- Now we turn to the case n > 0
    have bbound : 1 ≤ n, { sorry, },
    specialize hn bbound,
    have aaaaa : p^n ∣ a * b, { sorry, },
    specialize hn aaaaa,
    rcases hn with ⟨pn_dvd_a, p_not_dvd_b⟩,
    have p_dvd_a : p ∣ a, { sorry, },
    simp [p_dvd_a, p_not_dvd_b],
    let c := a / p^n,
    have p_dvd_ab_div_pn : p ∣ (c * b), { sorry, },
    have p_dvd_c : p ∣ c, { sorry, },
    -- now need to recompute a = c * p^n and dvd applies happily
    sorry,

    -- This is the exact proof, just with a and b reversed
    sorry,
  },

  {
    --- The easy direction that's just transitivity
    intro h,
    cases h,
    transitivity,
    exact h.left,
    exact dvd_mul_right a b,
    transitivity,
    exact h.left,
    exact dvd_mul_left b a,
  },
end

/-
  If two integers m and n are coprime, then the product is squarefree iff both
  m and n are coprime.
-/
lemma coprime_prod_squarefree_iff {m n : ℕ} (hmn : m.coprime n) : squarefree m ∧ squarefree n ↔ squarefree (m * n) :=
begin
  split,

  -- We'll prove by contradiction that if m * n is not squarefree, then
  -- one of m and n cannot be squarefree
  -- Proof strategy:
  --   * Since m * n is not squarefree, there must be some x ≥ 2 with x * x ∣ m * n
  --   * There must be some prime p such that p ∣ x and so p * p ∣ m * n
  --   * By the above lemma, p * p ∣ m ∨ p * p ∣ n
  --   * Definition of squarefree

  -- Step 1
  rintros ⟨hm, hn⟩,
  by_contradiction H,
  unfold squarefree at H,
  push_neg at H,
  rcases H with ⟨x, hx, hx_not_unit⟩,
  have two_le_x : 2 ≤ x, {
    rw nat.two_le_iff,
    split,
    {
      by_contradiction x_eq_zero,
      rw x_eq_zero at hx,
      simp at hx,
      cases hx,
      rw hx at hm,
      exact not_squarefree_zero hm,
      rw hx at hn,
      exact not_squarefree_zero hn,
    },
    {
      exact hx_not_unit,
    },
  },

  -- Step 2
  have : ∃ (p : ℕ), nat.prime p ∧ p ∣ x, {
    exact exists_prime_and_dvd two_le_x,
  },
  rcases this with ⟨p, p_is_prime, p_dvd_x⟩,
  have pp_dvd_xx : p * p ∣ x * x, { exact mul_dvd_mul p_dvd_x p_dvd_x, },
  have p2_dvd_xx : p^2 ∣ x * x, { ring_nf, ring_nf at pp_dvd_xx, exact pp_dvd_xx, },

  have p2_dvd_mn : p^2 ∣ m * n, {
    transitivity,
    exact p2_dvd_xx,
    exact hx,
  },

  -- Step 3 and 4
  rw prime_pow_dvd_mul_of_coprime p_is_prime at p2_dvd_mn,
  sorry,
  linarith,
  exact hmn,

  -- In the other direction, we once again work by contradition.
  unfold squarefree,
  intros h,
  split,
  by_contradiction H,
  push_neg at H,
  rcases H with ⟨x, hx, hxx⟩,
  specialize h x,
  have : x * x ∣ m * n, {
    calc
      x * x ∣ m : hx
        ... ∣ m * n : dvd.intro n rfl,
  },
  specialize h this,
  tauto,

  -- Identical to above
  by_contradiction H,
  push_neg at H,
  rcases H with ⟨x, hx, hxx⟩,
  specialize h x,
  have : x * x ∣ m * n, {
    calc
      x * x ∣ n : hx
        ... ∣ n * m : dvd.intro m rfl
        ... = m * n : by { exact mul_comm n m, },
  },
  specialize h this,
  tauto,
end

/-
  The previous lemma can be reinterpreted as saying that squarefree_nat'
  is a multiplicative function. Note that thsi proof is horrendous and presumably
  there's a much better way to write it!
-/
lemma is_multiplicative_squarefree : is_multiplicative squarefree_nat' :=
begin
  unfold is_multiplicative,
  split,
  unfold squarefree_nat',
  simp,
  unfold squarefree_nat,
  simp [squarefree_one],
  intros m n hmn,
  unfold squarefree_nat',
  simp,
  unfold squarefree_nat,
  simp,
  by_cases h : squarefree (m * n), {
    by_cases hh : squarefree m , {
      by_cases hhh : squarefree n, {
        simp [h, hh, hhh],
      },
      {
        exfalso,
        have : squarefree n, {
          rw ← coprime_prod_squarefree_iff hmn at h,
          exact h.right,
        },
        exact hhh this,
      },
    },
    {
      exfalso,
      have : squarefree m, {
        rw ← coprime_prod_squarefree_iff hmn at h,
        exact h.left,
      },
      exact hh this,
    },
  },
  {
    simp [h],
    by_cases hh : squarefree m, {
      by_cases hhh : squarefree n, {
        exfalso,
        rw ← coprime_prod_squarefree_iff hmn at h,
        push_neg at h,
        exact h hh hhh,
      },
      {
        simp [hhh],
      },
    },
    {
      simp [hh],
    },
  },
end


lemma is_multiplicative_moebius {m n : ℕ} : m.coprime n → moebius (m * n) = moebius m * moebius n :=
begin
  intros h,
  by_cases hm : squarefree m,
  {
    by_cases hn : squarefree n,
    {
      have m_ne_zero : m ≠ 0, { by_contradiction H, rw H at hm, exact not_squarefree_zero hm, },
      have n_ne_zero : n ≠ 0, { by_contradiction H, rw H at hn, exact not_squarefree_zero hn, },
      have aa : moebius m = (-1) ^ card_factors m, { rw moebius_apply_of_squarefree, exact hm, },
      have bb : moebius n = (-1) ^ card_factors n, { rw moebius_apply_of_squarefree, exact hn, },
      have cc : squarefree (m * n), {
        rw ← coprime_prod_squarefree_iff,
        exact ⟨hm, hn⟩,
        exact h,
      },
      have dd : moebius (m * n) = (-1) ^ card_factors (m * n), { rw moebius_apply_of_squarefree, exact cc, },
      have ee : card_factors (m * n) = card_factors m + card_factors n, { rw card_factors_mul m_ne_zero n_ne_zero, },
      rw [aa, bb, dd, ee],
      sorry, -- ring doesn't work here for some reason
    },
    {
      have aa : moebius n = 0, exact moebius_eq_zero_of_not_squarefree hn,
      have bb : n ∣ m * n, exact dvd_mul_left n m,
      have cc : ¬ squarefree (m * n), {
        apply asdfasdf n (m * n),
        exact ⟨bb, hn⟩,
      },
      have dd : moebius (m * n) = 0, exact moebius_eq_zero_of_not_squarefree cc,
      rw [aa, dd],
      ring,
    },
  },
  {
    have aa : moebius m = 0, exact moebius_eq_zero_of_not_squarefree hm,
    have bb : m ∣ m * n, exact dvd_mul_right m n,
    have cc : ¬ squarefree (m * n), {
      apply asdfasdf m (m * n),
      exact ⟨bb, hm⟩,
    },
    have dd : moebius (m * n) = 0, exact moebius_eq_zero_of_not_squarefree cc,
    rw [aa, dd],
    ring,
  },
end

lemma length_zero_iff_nil {a : list ℕ} : a = list.nil ↔ a.length = 0 :=
begin
  sorry,
end

lemma length_sublist_aux : ∀ (b a : list ℕ) (ha : a ⊆ b), a.length ≤ b.length :=
begin
  intros b,
  induction b,
  {
    intros a ha,
    simp,
    rw list.length_eq_zero,
    exact list.eq_nil_of_subset_nil ha,
  },
  {
    intros a ha,
    by_cases b_hd ∈ a,
    {
      let a' := a.erase b_hd,
      have : a' ⊆ b_tl, { sorry, },
      specialize b_ih a' this,
      simp,
      have fff : a'.length + 1 = a.length, { sorry, },
      linarith,
    },
    {
      have aa : a ⊆ b_tl, { sorry, },
      have bb : b_tl.length ≤ (b_hd :: b_tl).length, { sorry, },
      specialize b_ih a aa,
      transitivity,
      exact b_ih,
      exact bb,
    },
  },

end

lemma length_sublist {a b : list ℕ} (ha : a ⊆ b) : a.length ≤ b.length :=
begin
  -- idea: induct on b.length
  --       * If b.length = 0, then a = b = ∅ and so the result is trivial
  --       * If b.length > 0, two cases: a = b in which case result is trivial
  --           and a ≠ b. In that case, find some x ∈ b ∧ x ∉ a. Then
  --           a ⊆ b.erase x, (b.erase x).length = b.length - 1 ≤ b.length
  --           and so it all follows by induction and transitivity.
  exact length_sublist_aux b a ha,
end

lemma card_factors_eq_zero_iff_zero_one { n : ℕ } : card_factors n = 0 ↔ n = 0 ∨ n = 1 :=
begin
  split,
  {
    intros h,
    by_contradiction H,
    push_neg at H,
    have two_le_n : 2 ≤ n, {
      rw two_le_iff,
      split,
      exact H.left,
      simp [H.right],
    },
    have : ∃ (p : ℕ), nat.prime p ∧ p ∣ n, {
      exact exists_prime_and_dvd two_le_n,
    },
    rcases this with ⟨p, p_is_prime, p_dvd_n⟩,
    have aa : p.factors ⊆ n.factors, { exact factors_subset_of_dvd p_dvd_n (by linarith), },
    have bb : p.factors = [p], { exact factors_prime p_is_prime, },
    have cc: p.factors.length ≤ n.factors.length, { exact length_sublist aa, },
    have dd: p.factors.length = 1, { rw bb, exact list.length_singleton p, },
    have : n.factors.length > 0, { linarith, },
    have : n.factors.length = 0, { exact h, },
    linarith,
  },
  {
    intros h,
    cases h,
    rw h,
    simp,
    rw h,
    simp,
  },
end

lemma card_distinct_factors_eq_zero_iff_zero_one { n : ℕ } : card_distinct_factors n = 0 ↔ n = 0 ∨ n = 1 :=
begin
  sorry,
end


lemma multiplicative_eq_on_prime_powers_imp_eq {f g : arithmetic_function ℤ} (hf : is_multiplicative f) (hg : is_multiplicative g) :
(∀ (i p : ℕ), nat.prime p → f (p^i) = g (p^i)) → f = g :=
begin
  intros h,
  rw zero_hom.ext_iff,
  intros x,
  by_cases x_ne_zero : x = 0, {
    rw x_ne_zero,
    simp,
  },

  by_cases h : card_distinct_factors x = 0,
  {
    have x_eq_one : x = 1, {
      rw card_distinct_factors_eq_zero_iff_zero_one at h,
      cases h,
      exfalso,
      exact x_ne_zero h_1,
      exact h_1,
    },
    rw x_eq_one,
    rw [is_multiplicative.map_one hf, is_multiplicative.map_one hg],
  },
  {
    have two_le_x : 2 ≤ x, {
      rw card_distinct_factors_eq_zero_iff_zero_one at h,
      push_neg at h,
      have x_ne_one : x ≠ 1, exact h.right,
      rw two_le_iff,
      simp [x_ne_zero, x_ne_one],
    },
    -- the case when x is a prime power
    -- the case when x is not a prime power, break up into two coprimes factors
    --   both of which are < x so equal by induction and then coprime wins the day
    sorry,
  },
end


def fop (x : ℕ × ℕ) := x.fst * x.snd

lemma nat_ne_zero_ne_one_ge_two {n : ℕ} : n ≠ 0 ∧ n ≠ 1 ↔ n ≥ 2 :=
begin
  induction n,
  simp,
  have n_n_ge_one : n_n.succ ≥ 1, {
    calc n_n.succ = n_n + 1 : by exact rfl
      ... ≥ 0 + 1 : le_add_self
      ... ≥ 1 : rfl.ge,
  },
  induction n_n,
  simp,
  have n_n_n_ge_two : n_n_n.succ.succ ≥ 2, {
    calc n_n_n.succ.succ = n_n_n.succ + 1 : rfl
      ... ≥ n_n_n + 1 + 1 : rfl.ge
      ... ≥ n_n_n + 2 : rfl.ge
      ... ≥ 0 + 2 : le_add_self
      ... ≥ 2 : rfl.ge,
  },
  simp,
  linarith,
end

lemma nat_ne_zero_ne_one_two_le {n : ℕ} : n ≠ 0 ∧ n ≠ 1 ↔ 2 ≤ n :=
begin
  rw ← ge_iff_le,
  exact nat_ne_zero_ne_one_ge_two,
end


lemma divisors_of_prod_is_prod_of_divisors_aux (N : ℕ) : ∀ (m : ℕ), m ≤ N → ∀ (n x : ℕ), x ∈ (m * n).divisors → ∃ a ∈ m.divisors, ∃ b ∈ n.divisors, x = a * b :=
begin
  induction N with N hN,
  {
    -- N = 0 => m = 0, which can't happen given the assumptions
    intros m hm n x hx,
    exfalso,
    have m_eq_zero : m = 0, { linarith, },
    simp at hx,
    push_neg at hx,
    exact hx.right.left m_eq_zero,
  },
  {
    -- The true base case is m = 1
    intros m hm n x hx,
    by_cases m_eq_one : m = 1, {
      use 1,
      rw m_eq_one,
      simp,
      rw m_eq_one at hx,
      simp at hx,
      exact hx,
    },
    {
      obtain ⟨m_ne_zero, n_ne_zero⟩ : m ≠ 0 ∧ n ≠ 0, {
        simp at hx,
        push_neg at hx,
        exact hx.right,
      },
      have zero_lt_m : 0 < m, { exact zero_lt_iff.mpr m_ne_zero, },
      have two_le_m : 2 ≤ m, exact nat_ne_zero_ne_one_two_le.mp ⟨m_ne_zero, m_eq_one⟩,

      obtain ⟨p, p_is_prime, p_dvd_m⟩ : ∃ (p : ℕ), prime p ∧ p ∣ m, exact exists_prime_and_dvd two_le_m,

      have one_lt_p : 1 < p, { exact prime.one_lt p_is_prime, },
      have p_ne_zero : p ≠ 0, { linarith, },
      have zero_lt_p : 0 < p, { linarith, },
      have m_div_p_lt_m : (m / p) < m, { apply div_lt_self zero_lt_m one_lt_p },
      have m_div_p_le_N : (m / p) ≤ N, {
        have : m / p + 1 ≤ N + 1, {
          calc m / p + 1 ≤ m : by simpa [lt_add_one_iff]
            ... ≤ N.succ : hm
            ... = N + 1: succ_eq_add_one N,
          },
        simp at this,
        exact this,
      },
      have p_m_div_p_eq_m : p * (m / p) = m, { exact @nat.mul_div_cancel_left' p m p_dvd_m, },
      have m_div_p_ne_zero : m / p ≠ 0, {
        have p_le_m : p ≤ m, { exact le_of_dvd zero_lt_m p_dvd_m, },
        have : m / p ≥ 1, {
          by_contradiction H,
          push_neg at H,
          rw div_lt_iff_lt_mul' at H,
          simp at H,
          linarith,
          exact zero_lt_p,
        },
        linarith,
      },
      by_cases p_dvd_x : p ∣ x,
      {
        have p_x_div_p_eq_x : p * (x / p) = x, { exact @nat.mul_div_cancel_left' p x p_dvd_x, },

        have x_div_p_in_m_div_p_n_divisors : (x / p) ∈ (m / p * n).divisors, {
          simp,
          split,
          apply dvd_of_mul_dvd_mul_left,
          exact zero_lt_p,
          rw p_x_div_p_eq_x,
          have rearrange : p * (m / p * n) = (p * (m / p)) * n, {
            ring,
          },
          rw rearrange,
          rw p_m_div_p_eq_m,
          simp at hx,
          exact hx.left,
          push_neg,
          exact ⟨m_div_p_ne_zero, n_ne_zero⟩,
        },

        specialize hN (m / p) m_div_p_le_N n (x / p) x_div_p_in_m_div_p_n_divisors,
        rcases hN with ⟨a', ha', b, hb, x_div_p_eq_a'_b⟩,
        simp at ha',
        rcases ha' with ⟨a'_dvd_m_div_p, _⟩,
        use p * a',
        split,
        simp,
        split,
        rw ← p_m_div_p_eq_m,
        apply mul_dvd_mul,
        simp,
        exact a'_dvd_m_div_p,
        exact m_ne_zero,
        use b,
        simp [hb],
        rw ← p_x_div_p_eq_x,
        rw x_div_p_eq_a'_b,
        ring,
      },
      {
        have x_in_m_div_p_n_divisors : x ∈ (m / p * n).divisors, {
          have p_dvd_mn : p ∣ m * n, exact dvd_mul_of_dvd_left p_dvd_m n,
          have aa : x ∣ (m * n) / p, {
            rw dvd_div_iff p_dvd_mn,
            simp at hx,
            exact nat.coprime.mul_dvd_of_dvd_of_dvd ((prime.coprime_iff_not_dvd p_is_prime).mpr p_dvd_x) p_dvd_mn hx.left,
          },
          have aa' : (m * n) / p = (m / p) * n, {
            rw @nat.div_eq_iff_eq_mul_left (m * n) p ((m / p) * n) zero_lt_p p_dvd_mn,
            have rearrange : m / p * n * p  = p * (m / p) * n, { ring, },
            rw rearrange,
            rw p_m_div_p_eq_m,
          },
          rw aa' at aa,
          simp [aa],
          push_neg,
          exact ⟨m_div_p_ne_zero, n_ne_zero⟩,
        },
        specialize hN (m / p) m_div_p_le_N n x x_in_m_div_p_n_divisors,
        rcases hN with ⟨a, ha, b, hb, x_eq_a_b⟩,
        have a_in_m_divisors : a ∈ m.divisors, {
          simp [m_ne_zero],
          simp at ha,
          rcases ha with ⟨a_dvd_m_div_p, _⟩,
          have : a ∣ p * (m / p), exact dvd_mul_of_dvd_right a_dvd_m_div_p p,
          rw p_m_div_p_eq_m at this,
          exact this,
        },
        use [a, a_in_m_divisors, b, hb],
        exact x_eq_a_b,
      },
    },
  },
end

lemma divisors_of_prod_is_prod_of_divisors { m n x : ℕ } : x ∈ (m * n).divisors ↔ ∃ a ∈ m.divisors, ∃ b ∈ n.divisors, x = a * b :=
begin
  split,
  intros h,
  {
    have : m ≤ m, {exact rfl.ge,},
    apply divisors_of_prod_is_prod_of_divisors_aux,
    exact this,
    exact h,
  },
  {
    rintros ⟨a, ha, b, hb, x_eq_ab⟩,
    simp at ha,
    simp at hb,
    have : a * b ∣ m * n, { exact mul_dvd_mul ha.left hb.left, },
    simp,
    split,
    rwa x_eq_ab,
    push_neg,
    exact ⟨ha.right, hb.right⟩,
  },
end

lemma divisors_of_prod_is_prod_of_divisors_coprime_aux_strong
(N : ℕ)
:
∀ (n : ℕ), (n ≤ N) → ∀ (m : ℕ), m.coprime n → ∀ (x : ℕ), x ∈ (m * n).divisors → ∃! a ∈ m.divisors, a ∣ x ∧ x / a ∈ n.divisors :=
begin
  induction N with N hN,
  {
    -- the base case n = 0 actually can't occur!
    intros n hn m hmn x hx,
    exfalso,
    have : n = 0, {exact le_zero_iff.mp hn,},
    have : m * n = 0, { simp [this], },
    simp [this] at hx,
    exact hx,
  },
  {
    -- Now the actual base case: n = 1
    intros n,
    by_cases n_eq_one : n = 1,
    {
      intros hn m hmn x hx,
      use x,
      unfold,
      rw n_eq_one at hx,
      split,
      simp,
      split,
      simp at hx,
      exact hx,
      split,
      have : 0 < x, {
        simp at hx,
        rw zero_lt_iff,
        by_contradiction H,
        rw ← zero_dvd_iff at H,
        have : 0 ∣ m, {
          transitivity,
          exact H,
          exact hx.left,
        },
        rw zero_dvd_iff at this,
        exact hx.right this,
      },
      have : x / x = 1, { apply @nat.div_self, exact this, },
      rw this,
      simp,
      linarith,
      intros a',
      rintros ⟨ha', hha', hhha'⟩,
      rcases hha' with ⟨aprime_dvd_x, x_div_aprime_in_n_divisors⟩,
      specialize hhha' ha',
      unfold at hhha',
      specialize hhha' ⟨aprime_dvd_x, x_div_aprime_in_n_divisors⟩,
      simp at x_div_aprime_in_n_divisors,
      rw n_eq_one at x_div_aprime_in_n_divisors,
      rcases x_div_aprime_in_n_divisors with ⟨aa, bb⟩,
      have : x / a' = 1, {exact nat.dvd_one.mp aa,},
      have : a' * (x / a') = a' * 1, { exact congr_arg (has_mul.mul a') this, },
      rw @nat.mul_div_cancel_left' a' x aprime_dvd_x at this,
      simp at this,
      exact this.symm,
    },
    {
      -- and now the case n ≥ 2
      intros hn m hmn x hx,
      have n_ne_zero : n ≠ 0, {
        by_contradiction H,
        simp [H] at hx,
        exact hx,
      },
      have two_le_n : 2 ≤ n, {
        exact nat_ne_zero_ne_one_two_le.mp ⟨n_ne_zero, n_eq_one⟩,
      },
      have zero_lt_n : 0 < n, { linarith, },

      have exists_prime : ∃ (p : ℕ), prime p ∧ p ∣ n, exact exists_prime_and_dvd two_le_n,
      rcases exists_prime with ⟨p, p_is_prime, p_dvd_n⟩,
      have one_lt_p : 1 < p, { exact prime.one_lt p_is_prime, },
      have p_ne_zero : p ≠ 0, { linarith, },
      have zero_lt_p : 0 < p, { linarith, },
      have n_div_p_lt_m : (n / p) < n, { apply div_lt_self zero_lt_n one_lt_p },
      have n_div_p_le_N : (n / p) ≤ N, {
        have : n / p + 1 ≤ N + 1, {
          calc n / p + 1 ≤ n : by simpa [lt_add_one_iff]
            ... ≤ N.succ : hn
            ... = N + 1: succ_eq_add_one N,
          },
        simp at this,
        exact this,
      },

      have m_coprime_n_div_p : m.coprime (n / p), { exact coprime.coprime_div_right hmn p_dvd_n, },
      by_cases p_dvd_x : p ∣ x, {
        have x_dvd_mn_div_p : x ∈ (m * (n / p)).divisors, {sorry,},
        specialize hN (n / p) n_div_p_le_N m m_coprime_n_div_p x x_dvd_mn_div_p,
        cases hN with a ha,
        unfold at ha,
        cases ha with ha' ha'',
        simp at ha',
        rcases ha' with ⟨⟨a_dvd_m, m_ne_zero⟩, a_dvd_x, x_div_a_dvd_n_div_p, n_div_p_ne_zero⟩,
        use a,
        unfold,
        simp,
        split,
        split,
        exact ⟨a_dvd_m, m_ne_zero⟩,
        split,
        exact a_dvd_x,
        have : x / a ∣ n, { sorry, },
        split,
        exact this,
        linarith [two_le_n],
        simp at ha'',
        intros a' a'_dvd_m m_ne_zero a'_dvd_x x_div_a'_dvd_n n_ne_zero,
        specialize ha'' a' a'_dvd_m m_ne_zero a'_dvd_x,
        have : (x / a') ∣ (n / p), {sorry,},
        specialize ha'' this,
        have : n / p ≠ 0, { sorry, },
        specialize ha'' this,
        exact ha'',
      },
      {
        specialize hN (n / p) n_div_p_le_N m m_coprime_n_div_p (x / p),
        sorry,
      },
    },
  },
end

lemma divisors_of_prod_is_prod_of_divisors_coprime { m n x : ℕ } (hmn : m.coprime n) : x ∈ (m * n).divisors → ∃! a ∈ m.divisors, a ∣ x ∧ x / a ∈ n.divisors :=
begin
  apply divisors_of_prod_is_prod_of_divisors_coprime_aux_strong n,
  linarith,
  exact hmn,
end

example : is_multiplicative (sigma 0) :=
begin
  rw [← zeta_mul_pow_eq_sigma],
  apply ((is_multiplicative_zeta).mul is_multiplicative_pow),
end

end arithmetic_function
end nat
