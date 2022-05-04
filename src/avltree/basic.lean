/-
Copyright (c) 2022 Henry Pearson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Henry Pearson.
-/

import analysis.asymptotics.asymptotics
import order.filter.basic
import init.data.set
import data.nat.log
import avltree.init

/-!
# AVL node basic theorems

This file follows from `avltree.init.lean`, as well as the avlnode module and contains a proof
that for an avltree t, depth t = O(log (size t)) (i.e. why the structure is beneficial). It
contains multiple private lemmas/defintions that are used in the proof, but do not have general
applications.

## Main definitions

* `dep_is_O_with_size` is a proof that depth t = O(log 2 (size t)) for all non empty trees t.

-/

open avltree
open asymptotics

universe u

namespace avltree
variables {α : Type u} [linear_order α]
/--
Function that returns a prop that is true if a tree is a 'max unbalanced' tree - i.e. a tree where
the balance factor of every node that isn't a leaf is either 1 or -1. This is used for a proof later
-/
private def avlnode.max_unbalanced : avlnode α → Prop
  | avlnode.nil := true
  | (avlnode.node avlnode.nil _ avlnode.nil) := true
  | (avlnode.node l val r) := (avlnode.balance_factor (avlnode.node l val r) = 1 ∨ avlnode.balance_factor (avlnode.node l val r) = -1) 
                                 ∧ avlnode.max_unbalanced r ∧ avlnode.max_unbalanced l

/--
Same function as `avlnode.max_unbalanced` except defined on avltrees
-/
private def max_unbalanced : avltree α → Prop
  | ⟨n, _⟩ := avlnode.max_unbalanced n

private lemma avlnode.if_mu_properties_then_mu (l r : avlnode α) (val : α)
  : (avlnode.balance_factor (avlnode.node l val r) = 1 ∨ avlnode.balance_factor (avlnode.node l val r) = -1) 
    ∧ avlnode.max_unbalanced r ∧ avlnode.max_unbalanced l → avlnode.max_unbalanced (avlnode.node l val r) :=
begin
  intro h,
  cases l,
  cases r,
  rw avlnode.max_unbalanced,
  trivial,
  rw avlnode.max_unbalanced,
  exact h,
  cases r,
  rw avlnode.max_unbalanced,
  exact h,
  rw avlnode.max_unbalanced,
  exact h,
end

private lemma avlnode.mu_l_val_r_then_mu_l_and_mu_r (l r : avlnode α) (val : α) (h : avlnode.max_unbalanced (avlnode.node l val r))
  : (avlnode.max_unbalanced r ∧ avlnode.max_unbalanced l) :=
begin
  cases l,
  cases r,
  rw avlnode.max_unbalanced,
  split,
  trivial,
  trivial,
  rw [avlnode.max_unbalanced] at h,
  exact (and.elim_right h),
  rw [avlnode.max_unbalanced] at h,
  exact (and.elim_right h),
end

/--
Proof that given a max unbalanced tree n, for every tree with greater than or equal depth to n, the
size of that tree is greater than or equal to n.
-/
private lemma avlnode.mu_n_for_dep_is_min_size
  : ∀ (n n2 : avlnode α), avlnode.well_balanced n → avlnode.well_balanced n2 → avlnode.max_unbalanced n → n.depth ≤ n2.depth → avlnode.size n ≤ avlnode.size n2
| (avlnode.nil) (avlnode.nil) :=
  begin 
    intros wb_n wb_n2 mu_t h,
    rw avlnode.size,
  end
| (avlnode.node l val r) (avlnode.nil) :=
  begin 
    intros wb_n wb_n2 mu_t h,
    have h3 := avlnode.neg_1_le_dep_n l,
    have h4 := avlnode.dep_l_add_1_le_dep_l_v_r l r val,
    rw [avlnode.depth, avlnode.depth] at h,
    rw avlnode.depth at h4,
    linarith,
  end
| (avlnode.nil) (avlnode.node l2 val2 r2) :=
  begin 
    intros wb_n wb_n2 mu_t h,
    repeat {rw avlnode.size},
    linarith,
  end
| (avlnode.node l val r) (avlnode.node l2 val2 r2) :=
  begin 
    intros wb_n wb_n2 mu_t h,

    cases l,
    cases r,

    repeat {rw avlnode.size},
    linarith,

    rw avlnode.well_balanced at wb_n,
    have h2 := and.elim_left wb_n,
    have h3l := avlnode.dep_l_add_1_le_dep_l_v_r r_left r_right r_val,
    have h3r := avlnode.dep_r_add_1_le_dep_l_v_r r_left r_right r_val,
    rw [avlnode.balance_factor, avlnode.depth, avlnode.depth] at h2,
    rw avlnode.depth at h3l,
    rw avlnode.depth at h3r,
    have h4r := avlnode.neg_1_le_dep_n r_right,
    have h4l := avlnode.neg_1_le_dep_n r_left,
    have h5r : r_right.depth = -1 := begin linarith, end,
    have h5l : r_left.depth = -1 := begin linarith, end,
    rw avlnode.dep_n_eq_neg_1_iff_n_nil at h5r,
    rw avlnode.dep_n_eq_neg_1_iff_n_nil at h5l,
    rw [h5r, h5l],
    have h6 := avlnode.dep_nil_v_r_eq_dep_r_add_1 (r_left.node r_val r_right) val,
    rw [h6, h5l, h5r, avlnode.depth, if_pos, avlnode.depth, avlnode.depth] at h,
    cases classical.em (l2.depth ≤ r2.depth),
    have h7 := avlnode.dep_l_le_dep_r_then_dep_l_v_r_eq_dep_r_add_1 l2 r2 val2 h_1,
    rw avlnode.depth at h7,
    rw h7 at h,
    cases r2,
    rw avlnode.depth at h,
    linarith,
    repeat {rw avlnode.size},
    linarith,
    have h7 := avlnode.dep_r_le_dep_l_then_dep_l_v_r_eq_dep_l_add_1 l2 r2 val2 (le_of_not_le h_1),
    rw avlnode.depth at h7,
    rw h7 at h,
    cases l2,
    rw avlnode.depth at h,
    linarith,
    repeat {rw avlnode.size},
    linarith,
    refl,

    cases r,

    rw avlnode.well_balanced at wb_n,
    have h2 := and.elim_left (and.elim_right wb_n),
    have h3l := avlnode.dep_l_add_1_le_dep_l_v_r l_left l_right l_val,
    have h3r := avlnode.dep_r_add_1_le_dep_l_v_r l_left l_right l_val,
    rw [avlnode.balance_factor, avlnode.depth, avlnode.depth] at h2,
    rw avlnode.depth at h3l,
    rw avlnode.depth at h3r,
    have h4r := avlnode.neg_1_le_dep_n l_right,
    have h4l := avlnode.neg_1_le_dep_n l_left,
    have h5r : l_right.depth = -1 := begin linarith, end,
    have h5l : l_left.depth = -1 := begin linarith, end,
    rw avlnode.dep_n_eq_neg_1_iff_n_nil at h5r,
    rw avlnode.dep_n_eq_neg_1_iff_n_nil at h5l,
    rw [h5r, h5l],
    have h6 := avlnode.dep_l_v_nil_eq_dep_l_add_1 (l_left.node l_val l_right) val,
    rw [h6, h5l, h5r, avlnode.depth, if_pos, avlnode.depth, avlnode.depth] at h,
    cases classical.em (l2.depth ≤ r2.depth),
    have h7 := avlnode.dep_l_le_dep_r_then_dep_l_v_r_eq_dep_r_add_1 l2 r2 val2 h_1,
    rw avlnode.depth at h7,
    rw h7 at h,
    cases r2,
    rw avlnode.depth at h,
    linarith,
    repeat {rw avlnode.size},
    linarith,
    have h7 := avlnode.dep_r_le_dep_l_then_dep_l_v_r_eq_dep_l_add_1 l2 r2 val2 (le_of_not_le h_1),
    rw avlnode.depth at h7,
    rw h7 at h,
    cases l2,
    rw avlnode.depth at h,
    linarith,
    repeat {rw avlnode.size},
    linarith,
    refl,

    cases classical.em ((l_left.node l_val l_right).depth ≤ (r_left.node r_val r_right).depth),

    have h2 := avlnode.dep_l_le_dep_r_then_dep_l_v_r_eq_dep_r_add_1 (l_left.node l_val l_right) (r_left.node r_val r_right) val h_1,
    rw [avlnode.max_unbalanced, avlnode.balance_factor] at mu_t,
    cases (and.elim_left mu_t),
    rw [avlnode.well_balanced, avlnode.balance_factor] at wb_n2,
    cases classical.em (r2.depth - l2.depth = 1),

    have h3 : l2.depth ≤ r2.depth := begin linarith, end,
    have h4 := avlnode.dep_l_le_dep_r_then_dep_l_v_r_eq_dep_r_add_1 l2 r2 val2 h3,
    rw [h2, h4] at h,
    rw avlnode.well_balanced at wb_n,
    have h5 := and.elim_right (and.elim_right (and.elim_right wb_n)),
    have h6 := and.elim_right (and.elim_right (and.elim_right wb_n2)),
    have h7 : avlnode.depth (r_left.node r_val r_right) ≤ avlnode.depth r2 := begin linarith, end,
    have h9 := avlnode.mu_n_for_dep_is_min_size (r_left.node r_val r_right) r2 h5 h6 (and.elim_left (and.elim_right mu_t)) h7,
    have h10 := and.elim_left (and.elim_right (and.elim_right wb_n)),
    have h11 := and.elim_left (and.elim_right (and.elim_right wb_n2)),
    have h12 : avlnode.depth (l_left.node l_val l_right) ≤ avlnode.depth l2 := begin linarith, end,
    have h14 := avlnode.mu_n_for_dep_is_min_size (l_left.node l_val l_right) l2 h10 h11 (and.elim_right (and.elim_right mu_t)) h12,
    rw avlnode.size at h9,
    rw avlnode.size at h14,
    repeat {rw avlnode.size},
    linarith,

    cases classical.em (r2.depth - l2.depth = 0),

    have h3 : l2.depth ≤ r2.depth := begin linarith, end,
    have h4 := avlnode.dep_l_le_dep_r_then_dep_l_v_r_eq_dep_r_add_1 l2 r2 val2 h3,
    rw [h2, h4] at h,
    rw avlnode.well_balanced at wb_n,
    have h5 := and.elim_right (and.elim_right (and.elim_right wb_n)),
    have h6 := and.elim_right (and.elim_right (and.elim_right wb_n2)),
    have h7 : avlnode.depth (r_left.node r_val r_right) ≤ avlnode.depth r2 := begin linarith, end,
    have h9 := avlnode.mu_n_for_dep_is_min_size (r_left.node r_val r_right) r2 h5 h6 (and.elim_left (and.elim_right mu_t)) h7,
    have h10 := and.elim_left (and.elim_right (and.elim_right wb_n)),
    have h11 := and.elim_left (and.elim_right (and.elim_right wb_n2)),
    have h12 : avlnode.depth (l_left.node l_val l_right) ≤ avlnode.depth l2 := begin linarith, end,
    have h14 := avlnode.mu_n_for_dep_is_min_size (l_left.node l_val l_right) l2 h10 h11 (and.elim_right (and.elim_right mu_t)) h12,
    rw avlnode.size at h9,
    rw avlnode.size at h14,
    repeat {rw avlnode.size},
    linarith,

    cases classical.em (r2.depth - l2.depth = -1),

    have h3 : r2.depth ≤ l2.depth := begin linarith, end,
    have h4 := avlnode.dep_r_le_dep_l_then_dep_l_v_r_eq_dep_l_add_1 l2 r2 val2 h3,
    rw [h2, h4] at h,
    rw avlnode.well_balanced at wb_n,
    have h5 := and.elim_right (and.elim_right (and.elim_right wb_n)),
    have h6 := and.elim_left (and.elim_right (and.elim_right wb_n2)),
    have h7 : avlnode.depth (r_left.node r_val r_right) ≤ avlnode.depth l2 := begin linarith, end,
    have h9 := avlnode.mu_n_for_dep_is_min_size (r_left.node r_val r_right) l2 h5 h6 (and.elim_left (and.elim_right mu_t)) h7,
    have h10 := and.elim_left (and.elim_right (and.elim_right wb_n)),
    have h11 := and.elim_right (and.elim_right (and.elim_right wb_n2)),
    have h12 : avlnode.depth (l_left.node l_val l_right) ≤ avlnode.depth r2 := begin linarith, end,
    have h14 := avlnode.mu_n_for_dep_is_min_size (l_left.node l_val l_right) r2 h10 h11 (and.elim_right (and.elim_right mu_t)) h12,
    rw avlnode.size at h9,
    rw avlnode.size at h14,
    repeat {rw avlnode.size},
    linarith,

    exfalso,
    have h3 := ne.intro h_3,
    have h4 := ne.intro h_4,
    have h5 := ne.intro h_5,
    rw ne_iff_lt_or_gt at h3,
    rw ne_iff_lt_or_gt at h4,
    rw ne_iff_lt_or_gt at h5,

    cases h5,
    linarith,
    cases h4,
    linarith,
    cases h3,
    linarith,
    linarith,

    linarith,

    have h2 := avlnode.dep_r_le_dep_l_then_dep_l_v_r_eq_dep_l_add_1 (l_left.node l_val l_right) (r_left.node r_val r_right) val (le_of_not_le h_1),
    rw [avlnode.max_unbalanced, avlnode.balance_factor] at mu_t,
    cases (and.elim_left mu_t),
    linarith,
    rw [avlnode.well_balanced, avlnode.balance_factor] at wb_n2,
    cases classical.em (r2.depth - l2.depth = 1),

    have h3 : l2.depth ≤ r2.depth := begin linarith, end,
    have h4 := avlnode.dep_l_le_dep_r_then_dep_l_v_r_eq_dep_r_add_1 l2 r2 val2 h3,
    rw [h2, h4] at h,
    rw avlnode.well_balanced at wb_n,
    have h5 := and.elim_left (and.elim_right (and.elim_right wb_n)),
    have h6 := and.elim_right (and.elim_right (and.elim_right wb_n2)),
    have h7 : avlnode.depth (l_left.node l_val l_right) ≤ avlnode.depth r2 := begin linarith, end,
    have h9 := avlnode.mu_n_for_dep_is_min_size (l_left.node l_val l_right) r2 h5 h6 (and.elim_right (and.elim_right mu_t)) h7,
    have h10 := and.elim_right (and.elim_right (and.elim_right wb_n)),
    have h11 := and.elim_left (and.elim_right (and.elim_right wb_n2)),
    have h12 : avlnode.depth (r_left.node r_val r_right) ≤ avlnode.depth l2 := begin linarith, end,
    have h14 := avlnode.mu_n_for_dep_is_min_size (r_left.node r_val r_right) l2 h10 h11 (and.elim_left (and.elim_right mu_t)) h12,
    rw avlnode.size at h9,
    rw avlnode.size at h14,
    repeat {rw avlnode.size},
    linarith,

    cases classical.em (r2.depth - l2.depth = 0),

    have h3 : l2.depth ≤ r2.depth := begin linarith, end,
    have h4 := avlnode.dep_l_le_dep_r_then_dep_l_v_r_eq_dep_r_add_1 l2 r2 val2 h3,
    rw [h2, h4] at h,
    rw avlnode.well_balanced at wb_n,
    have h5 := and.elim_left (and.elim_right (and.elim_right wb_n)),
    have h6 := and.elim_right (and.elim_right (and.elim_right wb_n2)),
    have h7 : avlnode.depth (l_left.node l_val l_right) ≤ avlnode.depth r2 := begin linarith, end,
    have h9 := avlnode.mu_n_for_dep_is_min_size (l_left.node l_val l_right) r2 h5 h6 (and.elim_right (and.elim_right mu_t)) h7,
    have h10 := and.elim_right (and.elim_right (and.elim_right wb_n)),
    have h11 := and.elim_left (and.elim_right (and.elim_right wb_n2)),
    have h12 : avlnode.depth (r_left.node r_val r_right) ≤ avlnode.depth l2 := begin linarith, end,
    have h14 := avlnode.mu_n_for_dep_is_min_size (r_left.node r_val r_right) l2 h10 h11 (and.elim_left (and.elim_right mu_t)) h12,
    rw avlnode.size at h9,
    rw avlnode.size at h14,
    repeat {rw avlnode.size},
    linarith,

    cases classical.em (r2.depth - l2.depth = -1),

    have h3 : r2.depth ≤ l2.depth := begin linarith, end,
    have h4 := avlnode.dep_r_le_dep_l_then_dep_l_v_r_eq_dep_l_add_1 l2 r2 val2 h3,
    rw [h2, h4] at h,
    rw avlnode.well_balanced at wb_n,
    have h5 := and.elim_left (and.elim_right (and.elim_right wb_n)),
    have h6 := and.elim_left (and.elim_right (and.elim_right wb_n2)),
    have h7 : avlnode.depth (l_left.node l_val l_right) ≤ avlnode.depth l2 := begin linarith,end,
    have h9 := avlnode.mu_n_for_dep_is_min_size (l_left.node l_val l_right) l2 h5 h6 (and.elim_right (and.elim_right mu_t)) h7,
    have h10 := and.elim_right (and.elim_right (and.elim_right wb_n)),
    have h11 := and.elim_right (and.elim_right (and.elim_right wb_n2)),
    have h12 : avlnode.depth (r_left.node r_val r_right) ≤ avlnode.depth r2 := begin linarith,end,
    have h14 := avlnode.mu_n_for_dep_is_min_size (r_left.node r_val r_right) r2 h10 h11 (and.elim_left (and.elim_right mu_t)) h12,
    rw avlnode.size at h9,
    rw avlnode.size at h14,
    repeat {rw avlnode.size},
    linarith,

    exfalso,
    have h3 := ne.intro h_3,
    have h4 := ne.intro h_4,
    have h5 := ne.intro h_5,
    rw ne_iff_lt_or_gt at h3,
    rw ne_iff_lt_or_gt at h4,
    rw ne_iff_lt_or_gt at h5,

    cases h5,
    linarith,
    cases h4,
    linarith,
    cases h3,
    linarith,
    linarith,
  end

private lemma avlnode.construct_mu_n_with_eq_dep
  : ∀ (n : avlnode α), (∃ (n2 : avlnode α), avlnode.depth n = avlnode.depth n2 ∧ avlnode.max_unbalanced n2)
| (avlnode.nil) :=
  begin
    use (avlnode.nil),
    rw avlnode.max_unbalanced,
    split,
    refl,
    trivial,
  end
| (avlnode.node l val r) :=
  begin
    cases classical.em (l.depth ≤ r.depth),
    have h_l := avlnode.construct_mu_n_with_eq_dep r,
    have h2 := avlnode.dep_l_le_dep_r_then_dep_l_v_r_eq_dep_r_add_1 l r val h,
    cases h_l with nl hl,
    cases nl,
    use (avlnode.node avlnode.nil val avlnode.nil),
    rw [avlnode.depth, if_pos, avlnode.depth, if_pos, avlnode.depth],
    split,
    rw avlnode.depth at hl,
    linarith,
    rw avlnode.max_unbalanced,
    trivial,
    refl,
    exact h,
    cases classical.em (nl_left.depth ≤ nl_right.depth),
    use (avlnode.node (nl_left.node nl_val nl_right) val nl_right),
    split,
    have h3 := avlnode.dep_r_add_1_le_dep_l_v_r nl_left nl_right nl_val,
    rw [h2, avlnode.depth, if_neg],
    linarith,
    linarith,
    have h3 := avlnode.dep_l_le_dep_r_then_dep_l_v_r_eq_dep_r_add_1 nl_left nl_right nl_val h_1,
    have h4 : ((nl_left.node nl_val nl_right).node val nl_right).balance_factor = -1 :=
      begin
        rw avlnode.balance_factor,
        linarith,
      end,
    have h5 := or.intro_right (((nl_left.node nl_val nl_right).node val nl_right).balance_factor = 1) h4,
    have h6 := and.elim_left (avlnode.mu_l_val_r_then_mu_l_and_mu_r nl_left nl_right nl_val (and.elim_right hl)),
    exact avlnode.if_mu_properties_then_mu (nl_left.node nl_val nl_right) nl_right val (and.intro h5 (and.intro h6 (and.elim_right hl))),
    
    use (avlnode.node (nl_left.node nl_val nl_right) val nl_left),
    split,
    have h3 := avlnode.dep_l_add_1_le_dep_l_v_r nl_left nl_right nl_val,
    rw [h2, avlnode.depth, if_neg],
    linarith,
    linarith,
    have h3 := avlnode.dep_r_le_dep_l_then_dep_l_v_r_eq_dep_l_add_1 nl_left nl_right nl_val (le_of_not_le h_1),
    have h4 : ((nl_left.node nl_val nl_right).node val nl_left).balance_factor = -1 :=
      begin
        rw avlnode.balance_factor,
        linarith,
      end,
    have h5 := or.intro_right (((nl_left.node nl_val nl_right).node val nl_left).balance_factor = 1) h4,
    have h6 := and.elim_right (avlnode.mu_l_val_r_then_mu_l_and_mu_r nl_left nl_right nl_val (and.elim_right hl)),
    exact avlnode.if_mu_properties_then_mu (nl_left.node nl_val nl_right) nl_left val (and.intro h5 (and.intro h6 (and.elim_right hl))),
    
    have h_l := avlnode.construct_mu_n_with_eq_dep l,
    have h2 := avlnode.dep_r_le_dep_l_then_dep_l_v_r_eq_dep_l_add_1 l r val (le_of_not_le h),
    cases h_l with nl hl,
    cases nl,
    rw [(and.elim_left hl), avlnode.depth] at h,
    have h3 := avlnode.neg_1_le_dep_n r,
    linarith,
    cases classical.em (nl_left.depth ≤ nl_right.depth),
    use (avlnode.node (nl_left.node nl_val nl_right) val nl_right),
    split,
    have h3 := avlnode.dep_r_add_1_le_dep_l_v_r nl_left nl_right nl_val,
    rw [h2, avlnode.depth, if_neg],
    linarith,
    linarith,
    have h3 := avlnode.dep_l_le_dep_r_then_dep_l_v_r_eq_dep_r_add_1 nl_left nl_right nl_val h_1,
    have h4 : ((nl_left.node nl_val nl_right).node val nl_right).balance_factor = -1 :=
      begin
        rw avlnode.balance_factor,
        linarith,
      end,
    have h5 := or.intro_right (((nl_left.node nl_val nl_right).node val nl_right).balance_factor = 1) h4,
    have h6 := and.elim_left (avlnode.mu_l_val_r_then_mu_l_and_mu_r nl_left nl_right nl_val (and.elim_right hl)),
    exact avlnode.if_mu_properties_then_mu (nl_left.node nl_val nl_right) nl_right val (and.intro h5 (and.intro h6 (and.elim_right hl))),
    
    use (avlnode.node (nl_left.node nl_val nl_right) val nl_left),
    split,
    have h3 := avlnode.dep_l_add_1_le_dep_l_v_r nl_left nl_right nl_val,
    rw [h2, avlnode.depth, if_neg],
    linarith,
    linarith,
    have h3 := avlnode.dep_r_le_dep_l_then_dep_l_v_r_eq_dep_l_add_1 nl_left nl_right nl_val (le_of_not_le h_1),
    have h4 : ((nl_left.node nl_val nl_right).node val nl_left).balance_factor = -1 :=
      begin
        rw avlnode.balance_factor,
        linarith,
      end,
    have h5 := or.intro_right (((nl_left.node nl_val nl_right).node val nl_left).balance_factor = 1) h4,
    have h6 := and.elim_right (avlnode.mu_l_val_r_then_mu_l_and_mu_r nl_left nl_right nl_val (and.elim_right hl)),
    exact avlnode.if_mu_properties_then_mu (nl_left.node nl_val nl_right) nl_left val (and.intro h5 (and.intro h6 (and.elim_right hl))),
  end

private lemma avlnode.mu_n_then_wb_n (n : avlnode α) (h : avlnode.max_unbalanced n)
  : avlnode.well_balanced n :=
begin
  induction n with l v r lh rh,
  rw avlnode.well_balanced,
  trivial,
  rw avlnode.well_balanced,
  cases l,
  cases r,
  rw [avlnode.balance_factor, avlnode.depth, avlnode.well_balanced],
  split,
  linarith,
  split,
  linarith,
  split,
  trivial,
  trivial,
  rw avlnode.max_unbalanced at h,
  cases (and.elim_left h),
  any_goals {
    split,
    linarith,
    split,
    linarith,
    split,
    rw avlnode.well_balanced,
    trivial,
    exact (rh (and.elim_left (and.elim_right h))),
  },
  rw avlnode.max_unbalanced at h,
  cases (and.elim_left h),
  any_goals {
    split,
    linarith,
    split,
    linarith,
    split,
    exact (lh (and.elim_right (and.elim_right h))),
    exact (rh (and.elim_left (and.elim_right h))),
  },
end

/--
Proof that depth t = O(log 2 (size t)) for all non empty trees t.
-/
theorem dep_is_O_with_size 
 : is_O depth ((int.of_nat ∘ (nat.log 2) ∘ size) : avltree α → int) (filter.principal (non_empty : set (avltree α))) :=
 begin
  rw is_O_iff,
  use 2,
  intros x h,
  cases x with n nh,
  have new_mu_h := avlnode.construct_mu_n_with_eq_dep n,
  cases new_mu_h with n2 h_dep_mu,
  have n2_wb := avlnode.mu_n_then_wb_n n2 (and.elim_right h_dep_mu),
  simp *,
  rw [int.norm_eq_abs, int.norm_eq_abs],
  induction n2 with l val r lh rh generalizing n,
  exfalso,
  rw avlnode.depth at h_dep_mu,
  have h2 := and.elim_left h_dep_mu,
  rw avlnode.dep_n_eq_neg_1_iff_n_nil at h2,
  simp [h2] at h,
  cases h,

  norm_num,
  
  have mu_lr := avlnode.mu_l_val_r_then_mu_l_and_mu_r l r val (and.elim_right h_dep_mu),
  have lwb := avlnode.mu_n_then_wb_n l (and.elim_right mu_lr),
  have rwb := avlnode.mu_n_then_wb_n r (and.elim_left mu_lr),
  have lh2 := lh lwb l lwb,
  have rh2 := rh rwb r rwb,
  /- case analysis on left and right subtree - trivial when both nil -/
  cases l,
  cases r,

  have h_dep := and.elim_left h_dep_mu,
  rw [avlnode.depth, if_pos, avlnode.depth] at h_dep,
  have h_n_leaf : ∃ (val : α), n = (avlnode.node avlnode.nil val avlnode.nil) :=
    begin 
      rw ← avlnode.dep_n_eq_0_iff_n_leaf,
      linarith,
    end,
  cases h_n_leaf with val2 h2,
  rw [depth, size, h2, avlnode.depth, if_pos, avlnode.depth, avlnode.size, avlnode.size],
  simp,
  refl,

  have mu_n2 := and.elim_right h_dep_mu,
  rw avlnode.max_unbalanced at mu_n2,
  cases (and.elim_left mu_n2),
  have h2 : ∃ (val2 : α), (r_left.node r_val r_right) = (avlnode.node avlnode.nil val2 avlnode.nil) :=
    begin
      rw [avlnode.balance_factor, avlnode.depth, avlnode.depth] at h_1,
      rw ← avlnode.dep_n_eq_0_iff_n_leaf,
      rw avlnode.depth,
      linarith,
    end,
  cases h2 with val2 h3,
  rw [depth, size, (and.elim_left h_dep_mu), h3, avlnode.depth, if_pos, avlnode.depth, if_pos, avlnode.depth],
  have h_dep := and.elim_left h_dep_mu,
  have h4 := avlnode.dep_nil_v_r_eq_dep_r_add_1 (r_left.node r_val r_right) val,
  rw [h4, h3] at h_dep,
  have h5 : avlnode.depth (avlnode.nil.node val (r_left.node r_val r_right)) ≤ avlnode.depth n := begin linarith, end,
  have h6 := avlnode.mu_n_for_dep_is_min_size (avlnode.nil.node val (r_left.node r_val r_right)) n n2_wb nh (and.elim_right h_dep_mu) h5,
  repeat {rw avlnode.size at h6},
  have h7 : 2 ≤ n.size := begin linarith, end,
  have h8 := nat.log_le_log_of_le h7,
  have h9 : 2 < 2 * 2 ∧ 1 < 2 ∧ 2 ≤ 2 := 
    begin 
      repeat {split},
      all_goals {linarith}, 
    end,
  rw ← nat.log_eq_one_iff at h9,
  rw h9 at h8,
  norm_cast,
  have h11 : 1 ≤ 2 * nat.log 2 n.size := begin linarith, end,
  rw ← int.coe_nat_le_coe_nat_iff at h11,
  rw (int.coe_nat_mul 2 (nat.log 2 n.size)) at h11,
  norm_num *,
  exact h11,
  refl,
  rw [avlnode.depth, if_pos, avlnode.depth],
  linarith,
  refl,

  rw [avlnode.balance_factor, avlnode.depth, avlnode.depth] at h_1,
  have h2 := avlnode.neg_1_le_dep_n (r_left.node r_val r_right),
  rw avlnode.depth at h2,
  linarith,

  cases r,

  have mu_n2 := and.elim_right h_dep_mu,
  rw avlnode.max_unbalanced at mu_n2,
  cases (and.elim_left mu_n2),
  rw [avlnode.balance_factor, avlnode.depth, avlnode.depth] at h_1,
  have h2 := avlnode.neg_1_le_dep_n (l_left.node l_val l_right),
  rw avlnode.depth at h2,
  linarith,

  have h2 : ∃ (val2 : α), (l_left.node l_val l_right) = (avlnode.node avlnode.nil val2 avlnode.nil) :=
    begin
      rw [avlnode.balance_factor, avlnode.depth, avlnode.depth] at h_1,
      rw ← avlnode.dep_n_eq_0_iff_n_leaf,
      rw avlnode.depth,
      linarith,
    end,
  cases h2 with val2 h3,
  rw [depth, size, (and.elim_left h_dep_mu), h3, avlnode.depth, if_neg, avlnode.depth, if_pos, avlnode.depth],
  have h_dep := and.elim_left h_dep_mu,
  have h4 := avlnode.dep_l_v_nil_eq_dep_l_add_1 (l_left.node l_val l_right) val,
  rw [h4, h3] at h_dep,
  have h5 : avlnode.depth ((l_left.node l_val l_right).node val avlnode.nil) ≤ avlnode.depth n := begin linarith, end,
  have h6 := avlnode.mu_n_for_dep_is_min_size ((l_left.node l_val l_right).node val avlnode.nil) n n2_wb nh (and.elim_right h_dep_mu) h5,
  repeat {rw avlnode.size at h6},
  have h7 : 2 ≤ n.size := begin linarith, end,
  have h8 := nat.log_le_log_of_le h7,
  have h9 : 2 < 2 * 2 ∧ 1 < 2 ∧ 2 ≤ 2 := 
    begin 
      repeat {split},
      all_goals {linarith}, 
    end,
  rw ← nat.log_eq_one_iff at h9,
  rw h9 at h8,
  norm_cast,
  have h11 : 1 ≤ 2 * nat.log 2 n.size := begin linarith, end,
  rw ← int.coe_nat_le_coe_nat_iff at h11,
  rw (int.coe_nat_mul 2 (nat.log 2 n.size)) at h11,
  norm_num *,
  exact h11,
  refl,
  rw [avlnode.depth, if_pos, avlnode.depth],
  linarith,
  refl,

  have mu_n2 := and.elim_right h_dep_mu,
  rw avlnode.max_unbalanced at mu_n2,
  cases (and.elim_left mu_n2),

  rw avlnode.balance_factor at h_1,
  have h2 : (l_left.node l_val l_right).depth ≤ (r_left.node r_val r_right).depth := begin linarith, end,
  have h3 := avlnode.dep_l_le_dep_r_then_dep_l_v_r_eq_dep_r_add_1 (l_left.node l_val l_right) (r_left.node r_val r_right) val h2,
  have h4 : non_empty (⟨l_left.node l_val l_right, lwb⟩ : avltree α) :=
    begin
      rw [non_empty, avlnode.non_empty],
      trivial,
    end,
  have lh3 := lh2 h4 (and.intro (eq.refl (l_left.node l_val l_right).depth) (and.elim_right mu_lr)),
  rw [depth, size] at lh3,
  norm_cast at lh3,
  have lh4 := int.add_le_add_right lh3 (↑(2 : nat)),
  rw ← (int.coe_nat_add (2 * nat.log 2 (l_left.node l_val l_right).size) 2) at lh4,
  have h5 : 2 * nat.log 2 (l_left.node l_val l_right).size + 2 = 2 * (nat.log 2 (l_left.node l_val l_right).size + 1) := begin linarith, end,
  have h6 : 1 < 2 := begin linarith, end,
  have h7 := eq.symm (nat.log_pow h6 (nat.log 2 (l_left.node l_val l_right).size + 1)),
  rw [pow_add, pow_one, mul_comm] at h7,
  have h8 : 0 < (l_left.node l_val l_right).size :=
    begin
      rw avlnode.size,
      linarith,
    end,
  have h9 := nat.pow_log_le_self h6 h8,
  have h10 : 2 * (2 ^ nat.log 2 (l_left.node l_val l_right).size) ≤ 2 * (l_left.node l_val l_right).size := begin linarith, end,
  rw [h5, h7] at lh4,
  have h11 : nat.log 2 _ ≤ nat.log 2 _ := nat.log_le_log_of_le h10,
  have h12 := nat.mul_le_mul_left 2 h11,
  have h13 := avlnode.mu_n_for_dep_is_min_size (l_left.node l_val l_right) (r_left.node r_val r_right) lwb rwb (and.elim_right mu_lr) h2,
  have h14 : 2 * (l_left.node l_val l_right).size ≤ (l_left.node l_val l_right).size + (r_left.node r_val r_right).size + 1 := begin linarith, end,
  have h15 : |((l_left.node l_val l_right).node val (r_left.node r_val r_right)).depth| ≤ ↑(2 * nat.log 2 (((l_left.node l_val l_right).node val (r_left.node r_val r_right)).size)) := 
    begin
      have h16 : ((l_left.node l_val l_right).node val (r_left.node r_val r_right)).depth = (l_left.node l_val l_right).depth + 2 := 
        begin 
          rw h3,
          linarith, 
        end,
      rw [h16, avlnode.size],
      transitivity (|(l_left.node l_val l_right).depth| + 2 : int),
      have h17 := abs_add (l_left.node l_val l_right).depth 2,
      norm_cast at h17,
      exact h17,
      transitivity ↑(2 * nat.log 2 (2 * 2 ^ nat.log 2 (l_left.node l_val l_right).size)),
      exact lh4,
      norm_cast,
      transitivity 2 * nat.log 2 (2 * (l_left.node l_val l_right).size),
      exact h12,
      have h18 : nat.log 2 _ ≤ nat.log 2 _ := nat.log_le_log_of_le h14,
      exact nat.mul_le_mul_left 2 h18,
    end,
  have h16 : ((l_left.node l_val l_right).node val (r_left.node r_val r_right)).depth ≤ n.depth := begin linarith, end,
  have h17 := avlnode.mu_n_for_dep_is_min_size ((l_left.node l_val l_right).node val (r_left.node r_val r_right)) n (avlnode.mu_n_then_wb_n ((l_left.node l_val l_right).node val (r_left.node r_val r_right)) (and.elim_right h_dep_mu)) nh (and.elim_right (h_dep_mu)) h16,
  have h18 : nat.log 2 _ ≤ nat.log 2 _ := nat.log_le_log_of_le h17,
  have h19 := nat.mul_le_mul_left 2 h18,
  rw [depth, size, (and.elim_left h_dep_mu)],
  norm_cast,
  transitivity (↑(2 * nat.log 2 ((l_left.node l_val l_right).node val (r_left.node r_val r_right)).size) : int),
  exact h15,
  norm_cast,
  exact h19,

  rw avlnode.balance_factor at h_1,
  have h2 : (r_left.node r_val r_right).depth ≤ (l_left.node l_val l_right).depth := begin linarith, end,
  have h3 := avlnode.dep_r_le_dep_l_then_dep_l_v_r_eq_dep_l_add_1 (l_left.node l_val l_right) (r_left.node r_val r_right) val h2,
  have h4 : non_empty (⟨r_left.node r_val r_right, rwb⟩ : avltree α) :=
    begin
      rw [non_empty, avlnode.non_empty],
      trivial,
    end,
  have rh3 := rh2 h4 (and.intro (eq.refl (r_left.node r_val r_right).depth) (and.elim_left mu_lr)),
  rw [depth, size] at rh3,
  norm_cast at rh3,
  have rh4 := int.add_le_add_right rh3 (↑(2 : nat)),
  rw ← (int.coe_nat_add (2 * nat.log 2 (r_left.node r_val r_right).size) 2) at rh4,
  have h5 : 2 * nat.log 2 (r_left.node r_val r_right).size + 2 = 2 * (nat.log 2 (r_left.node r_val r_right).size + 1) := begin linarith, end,
  have h6 : 1 < 2 := begin linarith, end,
  have h7 := eq.symm (nat.log_pow h6 (nat.log 2 (r_left.node r_val r_right).size + 1)),
  rw [pow_add, pow_one, mul_comm] at h7,
  have h8 : 0 < (r_left.node r_val r_right).size :=
    begin
      rw avlnode.size,
      linarith,
    end,
  have h9 := nat.pow_log_le_self h6 h8,
  have h10 : 2 * (2 ^ nat.log 2 (r_left.node r_val r_right).size) ≤ 2 * (r_left.node r_val r_right).size := begin linarith, end,
  rw [h5, h7] at rh4,
  have h11 : nat.log 2 _ ≤ nat.log 2 _ := nat.log_le_log_of_le h10,
  have h12 := nat.mul_le_mul_left 2 h11,
  have h13 := avlnode.mu_n_for_dep_is_min_size (r_left.node r_val r_right) (l_left.node l_val l_right) rwb lwb (and.elim_left mu_lr) h2,
  have h14 : 2 * (r_left.node r_val r_right).size ≤ (l_left.node l_val l_right).size + (r_left.node r_val r_right).size + 1 := begin linarith, end,
  have h15 : |((l_left.node l_val l_right).node val (r_left.node r_val r_right)).depth| ≤ ↑(2 * nat.log 2 (((l_left.node l_val l_right).node val (r_left.node r_val r_right)).size)) := 
    begin
      have h16 : ((l_left.node l_val l_right).node val (r_left.node r_val r_right)).depth = (r_left.node r_val r_right).depth + 2 := 
        begin 
          rw h3,
          linarith, 
        end,
      rw [h16, avlnode.size],
      transitivity (|(r_left.node r_val r_right).depth| + 2 : int),
      have h17 := abs_add (r_left.node r_val r_right).depth 2,
      norm_cast at h17,
      exact h17,
      transitivity ↑(2 * nat.log 2 (2 * 2 ^ nat.log 2 (r_left.node r_val r_right).size)),
      exact rh4,
      norm_cast,
      transitivity 2 * nat.log 2 (2 * (r_left.node r_val r_right).size),
      exact h12,
      have h18 : nat.log 2 _ ≤ nat.log 2 _ := nat.log_le_log_of_le h14,
      exact nat.mul_le_mul_left 2 h18,
    end,
  have h16 : ((l_left.node l_val l_right).node val (r_left.node r_val r_right)).depth ≤ n.depth := begin linarith, end,
  have h17 := avlnode.mu_n_for_dep_is_min_size ((l_left.node l_val l_right).node val (r_left.node r_val r_right)) n (avlnode.mu_n_then_wb_n ((l_left.node l_val l_right).node val (r_left.node r_val r_right)) (and.elim_right h_dep_mu)) nh (and.elim_right (h_dep_mu)) h16,
  have h18 : nat.log 2 _ ≤ nat.log 2 _ := nat.log_le_log_of_le h17,
  have h19 := nat.mul_le_mul_left 2 h18,
  rw [depth, size, (and.elim_left h_dep_mu)],
  norm_cast,
  transitivity (↑(2 * nat.log 2 ((l_left.node l_val l_right).node val (r_left.node r_val r_right)).size) : int),
  exact h15,
  norm_cast,
  exact h19,
 end

end avltree