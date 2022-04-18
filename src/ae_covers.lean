
import measure_theory.integral.interval_integral
import order.filter.at_top_bot
import measure_theory.integral.integral_eq_improper

open measure_theory filter set topological_space
open_locale ennreal nnreal topological_space

namespace measure_theory

section ae_cover

variables {α ι : Type*} [measurable_space α] (μ : measure α) (l : filter ι)

variables {μ} {l}

section preorder_α

variables [linear_order α] [topological_space α] [order_closed_topology α]
  [opens_measurable_space α] [has_no_atoms μ] {a b : ι → α} {A B : α} (hab : A ≤ B)

lemma eventually_le_nhds
(a b : α) (hab : a ≤ b)
:
∀ᶠ (x : α) in (nhds a), x ≤ b :=
begin
  sorry,
end

lemma eventually_lt_nhds
(a b : α) (hab : a < b)
:
∀ᶠ (x : α) in (nhds a), x < b :=
begin
  sorry,
end

lemma eventually_ge_nhds
(a b : α) (hab : b ≤ a)
:
∀ᶠ (x : α) in (nhds a), b ≤ x :=
begin
  sorry,
end

lemma eventually_gt_nhds
(a b : α) (hab : b < a)
:
∀ᶠ (x : α) in (nhds a), b < x :=
begin
  sorry,
end

/-! ### finite ae covers by finite intervals

TODO: Pull out the `of_Icc`'s into a `preorder` section since that's all that's required
-/

lemma ae_eq_restrict_aux
{s t : set α}
(hs : measurable_set s) (ht : measurable_set t)
(hst : s =ᵐ[μ] t)
{f : α → Prop} :
(∀ᵐ (x : α) ∂μ.restrict s, f x) → (∀ᵐ (x : α) ∂μ.restrict t, f x) :=
begin
  rw [ae_restrict_iff' hs, ae_restrict_iff' ht, ae_iff, ae_iff],
  simp only [not_forall, exists_prop],
  intros h,
  have aa : {a : α | a ∈ s ∧ ¬f a} ∪ {a : α | a ∈ t ∧ ¬f a} = {a : α | a ∈ s ∧ ¬f a} ∪ {a : α | a ∈ (t \ s) ∧ ¬f a},
  {
    ext,
    simp only [mem_union_eq, mem_set_of_eq, mem_diff],
    conv { congr, congr, rw and_comm, skip, rw and_comm, skip, congr, rw and_comm, skip, rw and_comm, },
    rw [←and_or_distrib_left, ←and_or_distrib_left, and.congr_right_iff],
    intros hf,
    rw [←mem_union, ←mem_diff, ←mem_union],
    conv { to_rhs, rw union_comm, rw diff_union_self, rw union_comm, },
  },
  have bb : {a : α | a ∈ t ∧ ¬f a} ⊆ {a : α | a ∈ s ∧ ¬f a} ∪ {a : α | a ∈ t ∧ ¬f a}, simp,
  have cc : μ ({a : α | a ∈ s ∧ ¬f a} ∪ {a : α | a ∈ t ∧ ¬f a}) = 0, {
    rw aa,
    have : μ ({a : α | a ∈ s ∧ ¬f a} ∪ {a : α | a ∈ (t \ s) ∧ ¬f a}) ≤ μ {a : α | a ∈ s ∧ ¬f a} + μ {a : α | a ∈ (t \ s) ∧ ¬f a}, exact measure_union_le _ _,
    rw h at this,
    rw ae_eq_set at hst,
    have dd : {a : α | a ∈ (t \ s) ∧ ¬f a} ⊆ t \ s, rw subset_def, simp, intros x ht hs _, exact ⟨ht, hs⟩,
    rw measure_mono_null dd hst.right at this,
    rw zero_add at this,
    rw nonpos_iff_eq_zero at this,
    exact this,
  },
  exact measure_mono_null bb cc,
end

lemma ae_eq_restrict
{s t : set α}
(hs : measurable_set s) (ht : measurable_set t)
(hst : s =ᵐ[μ] t)
{f : α → Prop} :
(∀ᵐ (x : α) ∂μ.restrict s, f x) ↔ (∀ᵐ (x : α) ∂μ.restrict t, f x) :=
begin
  split,
  exact ae_eq_restrict_aux hs ht hst,
  exact ae_eq_restrict_aux ht hs hst.symm,
end

lemma ae_cover_restrict_of_ae_eq_aux
{φ : ι → set α}
{s t : set α}
(hs : measurable_set s)
(ht : measurable_set t)
(hst : s =ᵐ[μ] t)
(h : ae_cover (μ.restrict s) l φ) :
ae_cover (μ.restrict t) l φ := {
  ae_eventually_mem := begin
    rw ←ae_eq_restrict hs ht hst,
    exact h.ae_eventually_mem,
  end,
  measurable := h.measurable,
}

lemma ae_cover_restrict_of_ae_eq
{φ : ι → set α}
{s t : set α}
(hs : measurable_set s)
(ht : measurable_set t)
(hst : s =ᵐ[μ] t) :
ae_cover (μ.restrict s) l φ ↔ ae_cover (μ.restrict t) l φ :=
⟨ae_cover_restrict_of_ae_eq_aux hs ht hst, ae_cover_restrict_of_ae_eq_aux ht hs hst.symm⟩

lemma ae_cover_Ioo_of_Icc (ha : tendsto a l (nhds A)) (hb : tendsto b l (nhds B))
:
ae_cover (μ.restrict $ Ioo A B) l (λ i, Icc (a i) (b i)) := {
  ae_eventually_mem := (ae_restrict_iff' measurable_set_Ioo).mpr (
      ae_of_all μ (λ x hx,
      (ha.eventually $ eventually_le_nhds A x hx.left.le).mp $
      (hb.eventually $eventually_ge_nhds B x hx.right.le).mono $
      λ i hbi hai, ⟨hai, hbi⟩)),
  measurable := λ i, measurable_set_Icc, }

lemma ae_cover_Ioo_of_Ico (ha : tendsto a l (nhds A)) (hb : tendsto b l (nhds B))
:
ae_cover (μ.restrict $ Ioo A B) l (λ i, Ico (a i) (b i)) := {
  ae_eventually_mem := (ae_restrict_iff' measurable_set_Ioo).mpr (
      ae_of_all μ (λ x hx,
      (ha.eventually $ eventually_le_nhds A x hx.left.le).mp $
      (hb.eventually $ eventually_gt_nhds B x hx.right).mono $
      λ i hbi hai, ⟨hai, hbi⟩)),
  measurable := λ i, measurable_set_Ico, }

lemma ae_cover_Ioo_of_Ioc (ha : tendsto a l (nhds A)) (hb : tendsto b l (nhds B))
:
ae_cover (μ.restrict $ Ioo A B) l (λ i, Ioc (a i) (b i)) := {
  ae_eventually_mem := (ae_restrict_iff' measurable_set_Ioo).mpr (
      ae_of_all μ (λ x hx,
      (ha.eventually $ eventually_lt_nhds A x hx.left).mp $
      (hb.eventually $ eventually_ge_nhds B x hx.right.le).mono $
      λ i hbi hai, ⟨hai, hbi⟩)),
  measurable := λ i, measurable_set_Ioc, }

lemma ae_cover_Ioo_of_Ioo (ha : tendsto a l (nhds A)) (hb : tendsto b l (nhds B))
:
ae_cover (μ.restrict $ Ioo A B) l (λ i, Ioo (a i) (b i)) := {
  ae_eventually_mem := (ae_restrict_iff' measurable_set_Ioo).mpr (
      ae_of_all μ (λ x hx,
      (ha.eventually $ eventually_lt_nhds A x hx.left).mp $
      (hb.eventually $ eventually_gt_nhds B x hx.right).mono $
      λ i hbi hai, ⟨hai, hbi⟩)),
  measurable := λ i, measurable_set_Ioo, }

lemma ae_cover_Ioc_of_Icc (ha : tendsto a l (nhds A)) (hb : tendsto b l (nhds B))
:
ae_cover (μ.restrict $ Ioc A B) l (λ i, Icc (a i) (b i)) :=
begin
  have : Ioo A B =ᵐ[μ] Ioc A B, exact Ioo_ae_eq_Ioc,
  rw (ae_cover_restrict_of_ae_eq measurable_set_Ioc measurable_set_Ioo this.symm),
  exact ae_cover_Ioo_of_Icc ha hb,
end

lemma ae_cover_Ioc_of_Ico (ha : tendsto a l (nhds A)) (hb : tendsto b l (nhds B))
:
ae_cover (μ.restrict $ Ioc A B) l (λ i, Ico (a i) (b i)) :=
begin
  have : Ioo A B =ᵐ[μ] Ioc A B, exact Ioo_ae_eq_Ioc,
  rw (ae_cover_restrict_of_ae_eq measurable_set_Ioc measurable_set_Ioo this.symm),
  exact ae_cover_Ioo_of_Ico ha hb,
end

lemma ae_cover_Ioc_of_Ioc (ha : tendsto a l (nhds A)) (hb : tendsto b l (nhds B))
:
ae_cover (μ.restrict $ Ioc A B) l (λ i, Ioc (a i) (b i)) :=
begin
  have : Ioo A B =ᵐ[μ] Ioc A B, exact Ioo_ae_eq_Ioc,
  rw (ae_cover_restrict_of_ae_eq measurable_set_Ioc measurable_set_Ioo this.symm),
  exact ae_cover_Ioo_of_Ioc ha hb,
end

lemma ae_cover_Ioc_of_Ioo (ha : tendsto a l (nhds A)) (hb : tendsto b l (nhds B))
:
ae_cover (μ.restrict $ Ioc A B) l (λ i, Ioo (a i) (b i)) :=
begin
  have : Ioo A B =ᵐ[μ] Ioc A B, exact Ioo_ae_eq_Ioc,
  rw (ae_cover_restrict_of_ae_eq measurable_set_Ioc measurable_set_Ioo this.symm),
  exact ae_cover_Ioo_of_Ioo ha hb,
end

lemma ae_cover_Ico_of_Icc (ha : tendsto a l (nhds A)) (hb : tendsto b l (nhds B))
:
ae_cover (μ.restrict $ Ico A B) l (λ i, Icc (a i) (b i)) :=
begin
  have : Ioo A B =ᵐ[μ] Ico A B, exact Ioo_ae_eq_Ico,
  rw (ae_cover_restrict_of_ae_eq measurable_set_Ico measurable_set_Ioo this.symm),
  exact ae_cover_Ioo_of_Icc ha hb,
end

lemma ae_cover_Ico_of_Ico (ha : tendsto a l (nhds A)) (hb : tendsto b l (nhds B))
:
ae_cover (μ.restrict $ Ico A B) l (λ i, Ico (a i) (b i)) :=
begin
  have : Ioo A B =ᵐ[μ] Ico A B, exact Ioo_ae_eq_Ico,
  rw (ae_cover_restrict_of_ae_eq measurable_set_Ico measurable_set_Ioo this.symm),
  exact ae_cover_Ioo_of_Ico ha hb,
end

lemma ae_cover_Ico_of_Ioc (ha : tendsto a l (nhds A)) (hb : tendsto b l (nhds B))
:
ae_cover (μ.restrict $ Ico A B) l (λ i, Ioc (a i) (b i)) :=
begin
  have : Ioo A B =ᵐ[μ] Ico A B, exact Ioo_ae_eq_Ico,
  rw (ae_cover_restrict_of_ae_eq measurable_set_Ico measurable_set_Ioo this.symm),
  exact ae_cover_Ioo_of_Ioc ha hb,
end

lemma ae_cover_Ico_of_Ioo (ha : tendsto a l (nhds A)) (hb : tendsto b l (nhds B))
:
ae_cover (μ.restrict $ Ico A B) l (λ i, Ioo (a i) (b i)) :=
begin
  have : Ioo A B =ᵐ[μ] Ico A B, exact Ioo_ae_eq_Ico,
  rw (ae_cover_restrict_of_ae_eq measurable_set_Ico measurable_set_Ioo  this.symm),
  exact ae_cover_Ioo_of_Ioo ha hb,
end

lemma ae_cover_Icc_of_Icc (ha : tendsto a l (nhds A)) (hb : tendsto b l (nhds B))
:
ae_cover (μ.restrict $ Icc A B) l (λ i, Icc (a i) (b i)) :=
begin
  have : Ioo A B =ᵐ[μ] Icc A B, exact Ioo_ae_eq_Icc,
  rw (ae_cover_restrict_of_ae_eq measurable_set_Icc measurable_set_Ioo this.symm),
  exact ae_cover_Ioo_of_Icc ha hb,
end

lemma ae_cover_Icc_of_Ico (ha : tendsto a l (nhds A)) (hb : tendsto b l (nhds B))
:
ae_cover (μ.restrict $ Icc A B) l (λ i, Ico (a i) (b i)) :=
begin
  have : Ioo A B =ᵐ[μ] Icc A B, exact Ioo_ae_eq_Icc,
  rw (ae_cover_restrict_of_ae_eq measurable_set_Icc measurable_set_Ioo this.symm),
  exact ae_cover_Ioo_of_Ico ha hb,
end

lemma ae_cover_Icc_of_Ioc (ha : tendsto a l (nhds A)) (hb : tendsto b l (nhds B))
:
ae_cover (μ.restrict $ Icc A B) l (λ i, Ioc (a i) (b i)) :=
begin
  have : Ioo A B =ᵐ[μ] Icc A B, exact Ioo_ae_eq_Icc,
  rw (ae_cover_restrict_of_ae_eq measurable_set_Icc measurable_set_Ioo this.symm),
  exact ae_cover_Ioo_of_Ioc ha hb,
end

lemma ae_cover_Icc_of_Ioo (ha : tendsto a l (nhds A)) (hb : tendsto b l (nhds B))
:
ae_cover (μ.restrict $ Icc A B) l (λ i, Ioo (a i) (b i)) :=
begin
  have : Ioo A B =ᵐ[μ] Icc A B, exact Ioo_ae_eq_Icc,
  rw (ae_cover_restrict_of_ae_eq measurable_set_Icc measurable_set_Ioo this.symm),
  exact ae_cover_Ioo_of_Ioo ha hb,
end

end preorder_α
end ae_cover
end measure_theory