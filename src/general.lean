import algebra.squarefree
import measure_theory.integral.interval_integral

noncomputable theory
open nat finset
open_locale interval

namespace squarefree_sums

variables {R : Type*} {S : Type*}

lemma two_add {n a : ℕ} (hn : a ≤ n) : ∃ n', n = a + n' :=
begin
  use n - a,
  zify,
  ring,
end

lemma two_le_nat_iff_not_zero_one {m : ℕ} : 2 ≤ m ↔ m ≠ 0 ∧ m ≠ 1 :=
begin
  split,
  intros h,
  split,
  linarith,
  linarith,
  rintros ⟨h, hh⟩,
  induction m,
  simp [h],
  exact h rfl,
  induction m_n,
  exfalso,
  exact hh rfl,

  calc m_n_n.succ.succ = m_n_n.succ + 1 : rfl
    ... = m_n_n + 1 + 1 : rfl
    ... = m_n_n + 2 : by ring
    ... ≥ 0 + 2 : le_add_self
    ... = 2 : by ring,
end

lemma lt_of_div {a b : ℕ} (hb : 2 ≤ b) : a ≠ 0 → a / b < a :=
begin
  contrapose!,
  intros h,
  exact nat.eq_zero_of_le_div hb h,
end

lemma has_coprime_part_strong : ∀ (M m p : ℕ), m ≤ M → 1 ≤ m → nat.prime p → ∃ (m' i : ℕ), m = (p^i) * m' ∧ p.coprime m' :=
begin
  intros M,
  induction M with M hM,
  simp,
  intros m p hm hm',
  linarith,
  intros m p hm_ind one_le_m hp,
  have m_ne_zero : m ≠ 0, linarith,
  have zero_lt_m : 0 < m, linarith,
  by_cases p_dvd_m : p ∣ m,
  {
    have p_le_m : p ≤ m, exact nat.le_of_dvd zero_lt_m p_dvd_m,
    have mdp_ne_zero : m / p ≠ 0, {
      by_contradiction H,
      have : p * (m / p) = 0,
        calc p * (m / p) = p * 0 : by simp [H]
          ... = 0 : by simp,
      rw @nat.mul_div_cancel_left' p m p_dvd_m at this,
      exact m_ne_zero this,
    },
    have : 2 ≤ p, exact hp.two_le,
    have : m / p < M.succ,
      calc m / p < m : lt_of_div this m_ne_zero
        ... ≤ M.succ : hm_ind,
    have aaa : m / p ≤ M, exact lt_succ_iff.mp this,
    have bbb : 1 ≤ m / p, exact zero_lt_iff.mpr mdp_ne_zero,
    rcases hM (m / p) p aaa bbb hp with ⟨m', i', hm', hmp'⟩,
    use m',
    use i' + 1,
    split,
    conv {
      to_rhs,
      rw pow_add,
      congr,
      rw mul_comm,
    },
    conv {
      to_rhs,
      rw mul_assoc,
    },
    rw ← hm',
    simp,
    rw @nat.mul_div_cancel_left' p m p_dvd_m,
    exact hmp',
  },
  {
    use [m, 0],
    simp,
    cases coprime_or_dvd_of_prime hp m,
    exact h,
    exfalso,
    exact p_dvd_m h,
  },
end

lemma has_coprime_part : ∀ (m p : ℕ), 1 ≤ m → nat.prime p → ∃ (m' i : ℕ), m = (p^i) * m' ∧ p.coprime m' :=
begin
  intros m p,
  exact has_coprime_part_strong m m p (by linarith),
end

lemma exp_eq_iff_pow_eq {a m n : ℕ} (h : 2 ≤ a) : (m = n ↔ a ^ m = a ^ n) :=
begin
  split,
  { exact congr_arg (λ {m : ℕ}, a ^ m), },
  { intros hh,
    by_contradiction H,
    obtain ht | ht := lt_or_lt_iff_ne.mpr H,
    { exact ne_of_lt (@pow_lt_pow _ _ a _ _ (by linarith [h]) ht) hh },
    { exact ne_of_lt (@pow_lt_pow _ _ a _ _ (by linarith [h]) ht) hh.symm }, },
end

lemma prime_pow_eq_one_imp_pow_eq_zero {p i : ℕ} (hp : nat.prime p) : p^i = 1 → i = 0 :=
begin
  intros h,
  rw ← pow_zero at h,
  exact (exp_eq_iff_pow_eq hp.two_le).mpr h,
end

lemma nat_idemp_iff_zero_one {p : ℕ} : p = p * p ↔ p = 0 ∨ p = 1 :=
begin
  conv { to_lhs, to_lhs, rw ← one_mul p, },
  split,
  { intros h,
    by_cases hp : p = 0,
    { simp [hp], },
    { rw nat.mul_left_inj (zero_lt_iff.mpr hp) at h, simp [h], }, },
  intros h,
  cases h,
  { simp [h], },
  { simp [h], },
end

lemma pow_le_abs_pow [linear_ordered_ring R] {a : R} {b : ℕ} : a^b ≤ |a| ^ b :=
begin
  rw pow_abs,
  rw le_abs,
  left,
  refl,
end

lemma Ico_eq_range {n : ℕ} : finset.Ico 0 n = finset.range n :=
begin
  simp,
end

lemma finset.union_singleton {n : ℕ} {s : finset ℕ} : s ∪ {n} = insert n s :=
begin
  ext,
  rw [mem_union, mem_insert, mem_singleton, or_comm],
end

lemma not_mem_if_gt_max'
[linear_order R]
{s : finset R}
{hs : s.nonempty}
{n : R}
(hn : max' s hs < n)
:
n ∉ s
:=
begin
  by_contradiction H,
  exact ne_of_lt (calc n ≤ max' s hs : le_max' s n H ... < n : hn) rfl,
end

lemma finset.subset_finset_min_max
[linear_order R]
[locally_finite_order R]
{s : finset R}
(hs : s.nonempty) :
s ⊆ finset.Icc (s.min' hs) (s.max' hs) :=
begin
  rw subset_iff,
  intros x hx,
  simp,
  by_contradiction H,
  push_neg at H,
  by_cases h : s.min' hs ≤ x,
  specialize H h,
  rw finset.max'_lt_iff at H,
  exact ne_of_lt (H x hx) rfl,
  push_neg at h,
  rw finset.lt_min'_iff at h,
  exact ne_of_lt (h x hx) rfl,
end

lemma finset.Icc_subset_range {a b : ℕ} : finset.Icc a b ⊆ finset.range (b + 1) :=
begin
  rw subset_iff,
  intros x hx,
  rw finset.mem_range,
  simp at hx,
  simp [lt_succ_of_le hx.right],
end

lemma ite_const_rw
[decidable_eq S]
{n : S}
{f : S → R}
{a : R}
:
∀ (i : S), ite (i = n) (f i) a = ite (i = n) (f n) a
:=
begin
  intros i,
  by_cases i = n,
  simp [h],
  simp [h],
end

lemma interval_eq_Icc {a b : ℝ} (hab : a ≤ b) : [a, b] = set.Icc a b :=
begin
  unfold set.interval,
  have : min a b = a, simp [hab],
  rw this,
  have : max a b = b, simp [hab],
  rw this,
end

lemma interval_eq_Icc' {a b : ℝ} (hab : a ≤ b) : [b, a] = set.Icc a b :=
begin
  unfold set.interval,
  have : min b a = a, simp [hab],
  rw this,
  have : max b a = b, simp [hab],
  rw this,
end

lemma mem_Icc_mem_Ici
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Icc (a : ℝ) ↑b → x ∈ set.Ici (a : ℝ) :=
begin
  simp,
  intros h _,
  exact h,
end

lemma mem_Icc_mem_Ici'
{a b c : ℕ}
{x : ℝ}
:
x ∈ set.Icc (a : ℝ) ↑b → c ≤ a → x ∈ set.Ici (c : ℝ) :=
begin
  simp,
  intros h _ h',
  calc (c : ℝ) ≤ ↑a : cast_le.mpr h' ... ≤ x : h,
end


lemma mem_Ico_mem_Ici
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Ico (a : ℝ) ↑b → x ∈ set.Ici (a : ℝ) :=
begin
  simp,
  intros h _,
  exact h,
end

lemma mem_Ioc_mem_Ioi
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Ioc (a : ℝ) ↑b → x ∈ set.Ioi (a : ℝ) :=
begin
  simp,
  intros h _,
  exact h,
end

lemma mem_Ioo_mem_Ioi
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Ioo (a : ℝ) ↑b → x ∈ set.Ioi (a : ℝ) :=
begin
  simp,
  intros h _,
  exact h,
end

lemma mem_Ico_mem_Icc
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Ico (a : ℝ) ↑b → x ∈ set.Icc (a : ℝ) ↑b :=
begin
  simp,
  intros h h',
  exact ⟨h, le_of_lt h'⟩,
end

lemma mem_Ioo_mem_Icc
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Ioo (a : ℝ) ↑b → x ∈ set.Icc (a : ℝ) ↑b :=
begin
  simp,
  intros h h',
  exact ⟨le_of_lt h, le_of_lt h'⟩,
end

lemma mem_Ioo_mem_Ioc
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Ioo (a : ℝ) ↑b → x ∈ set.Ioc (a : ℝ) ↑b :=
begin
  simp,
  intros h h',
  exact ⟨h, le_of_lt h'⟩,
end

lemma mem_Ioo_mem_Ico
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Ioo (a : ℝ) ↑b → x ∈ set.Ico (a : ℝ) ↑b :=
begin
  simp,
  intros h h',
  exact ⟨le_of_lt h, h'⟩,
end

lemma ceil_of_Icc_mem_Icc
{a b : ℕ}
{x : ℝ}
(hx : x ∈ set.Icc (a : ℝ) ↑b)
:
↑⌈x⌉₊ ∈ set.Icc (a : ℝ) ↑b
:=
begin
  simp at hx,
  simp,
  split,
  have : ↑a ≤ (⌈x⌉₊ : ℝ), calc ↑a ≤ x : hx.left ... ≤ ↑⌈x⌉₊ : le_ceil x,
  exact cast_le.mp this,
  exact hx.right,
end

lemma floor_of_Icc_mem_Icc
{a b : ℕ} {x : ℝ}
(hx : x ∈ set.Icc (a : ℝ) ↑b)
:
↑⌊x⌋₊ ∈ set.Icc (a : ℝ) ↑b
:=
begin
  simp at hx,
  have : 0 ≤ x, calc (0 : ℝ) ≤ ↑a : by simp ... ≤ x : hx.left,
  simp,
  split,
  exact le_floor hx.left,
  have : (⌊x⌋₊ : ℝ) ≤ ↑b, calc ↑⌊x⌋₊ ≤ x : floor_le this ... ≤ ↑b : hx.right,
  exact cast_le.mp this,
end

lemma floor_of_unit_Ioo_val {R : Type*} [linear_ordered_semiring R] [floor_semiring R]
  {k : ℕ} {x : R} : x ∈ set.Ioo (k : R) (↑k + 1) → ⌊x⌋₊ = k :=
(λ ⟨hxl, hxr⟩, k.floor_eq_on_Ico x ⟨le_of_lt hxl, hxr⟩)

-- How do I use to_floor_semiring?
instance : floor_semiring ℝ :=
{ floor := λ a, ⌊a⌋.to_nat,
  ceil := λ a, ⌈a⌉.to_nat,
  floor_of_neg := λ a ha, int.to_nat_of_nonpos (int.floor_nonpos ha.le),
  gc_floor := λ a n ha, by { rw [int.le_to_nat_iff (int.floor_nonneg.2 ha), int.le_floor], refl },
  gc_ceil := λ a n, by { rw [int.to_nat_le, int.ceil_le], refl } }

lemma ceil_le_floor_add_one {R : Type*} [linear_ordered_semiring R] [floor_semiring R]
  {a : R} : ⌈a⌉₊ ≤ ⌊a⌋₊ + 1 :=
ceil_le.mpr $ le_of_lt $ lt_floor_add_one a

lemma floor_off_by_le_one {R : Type*} [linear_ordered_field R] [floor_semiring R]
  {a b : ℕ} : |(b : R) / a - ↑(b / a)| ≤ 1 :=
begin
  rw ← @floor_div_eq_div R _ _ b a,
  have target_nonneg : 0 ≤ (b : R) / ↑a - ↑⌊↑b / ↑a⌋₊,
  { rw sub_nonneg,
    exact floor_le (div_nonneg (cast_le.mpr zero_le') (cast_le.mpr zero_le')), },
  rw abs_of_nonneg target_nonneg,
  rw tsub_le_iff_left,
  refine le_trans (le_ceil _) _,
  norm_cast,
  exact ceil_le_floor_add_one,
end

end squarefree_sums
