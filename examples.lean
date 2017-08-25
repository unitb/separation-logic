import data.bitvec
import data.dlist
import util.logic
import util.control.applicative
import util.control.monad.non_termination
import ..separation.heap
import ..separation.program
import ..separation.specification
import ..separation.tactics

universes u v w w'

open nat list function nonterm

variables {α β : Type}

namespace separation

namespace examples

def swap_ptr (p q : pointer) : program unit := do
t ← alloc1 0,
copy t p,
copy p q,
copy q t,
free1 t

lemma swap_ptr_spec (p q : pointer) (v₀ v₁ : word)
: sat (swap_ptr p q) { pre := p ↦ v₀ :*: q ↦ v₁
                     , post := λ _, p ↦ v₁ :*: q ↦ v₀ } :=
begin
  unfold swap_ptr,
  bind_step t with h,
  bind_step,
  bind_step,
  bind_step,
  last_step,
end

open program

def map_list : pointer → program unit :=
fix (λ map_list p,
if p = 0
then return ()
else do
  modify p (+1),
  p' ← read_nth p 1 2,
  map_list p'.to_ptr)

lemma map_list_def (p : pointer)
: map_list p =
  if p = 0 then return ()
  else do
    modify p (+1),
    p' ← read_nth p 1 2 dec_trivial,
    map_list p'.to_ptr :=
begin
  unfold map_list,
  -- transitivity,
  admit -- rw [program.fix_unroll,dif_eq_if], refl
end

def is_list : pointer → list word → hprop
  | p [] := [| p = 0 |]
  | p (v :: vs) := [| p ≠ 0 |] :*: ∃∃ nx : word, p ↦* [v,nx] :*: is_list nx.to_ptr vs

lemma map_list_spec (p : pointer) (vs : list word)
: sat (map_list p)
    { pre := is_list p vs
    , post := λ _, is_list p (list.map (+1) vs) } :=
begin
  revert p,
  induction vs ; intros p,
  case nil
  { unfold map is_list,
    rw ← embed_s_and_self,
    apply context_left, simp,
    intro Hp₀, rw [map_list_def],
    rw if_pos Hp₀,
    apply return.spec' },
  case cons x xs
  { unfold map is_list,
    apply context_left, intro Hp_nz,
    rw [map_list_def],
    rw if_neg Hp_nz, simp,
    apply s_exists_intro_pre _,
    intro nx,
    apply bind_framing_right (is_list (nx.to_ptr) xs)
                             (modify_head.spec p (+1) x [nx]),
    { ac_refl },
    intro x, cases x, simp,
    apply bind_framing_right (is_list (nx.to_ptr) xs)
                             (read_nth.spec p 1 [x+1,nx] (of_as_true trivial)),
    { ac_refl },
    intro r_nx, simp [nth_le,embed_eq_emp Hp_nz],
    rw [← s_and_comm,s_and_assoc],
    apply context_left, intro Hnx,
    subst r_nx,
    apply s_exists_intro_post nx,
    apply framing_left,
    apply ih_1, }
end

lemma lift_ite (p : Prop) [decidable p] (f g : α → β) (x : α)
: (if p then f else g) x = if p then f x else g x :=
by { by_cases p with h, simp [if_pos h], simp [if_neg h] }

def list_reverse_aux : ∀ (p r : pointer),  program pointer :=
fix2 (λ list_reverse_aux p r,
if p = 0 then return r
else do
  p' ← read_nth p 1 2,
  write_nth p 1 2 ⟨ r ⟩,
  list_reverse_aux p'.to_ptr p)

lemma list_reverse_aux_def (p r : pointer)
: list_reverse_aux p r =
  if p = 0 then return r
  else do
    p' ← read_nth p 1 2 dec_trivial,
    write_nth p 1 2 ⟨ r ⟩ dec_trivial,
    list_reverse_aux p'.to_ptr p :=
begin
  unfold list_reverse_aux,
  -- transitivity,
  admit -- rw [program.fix2_unroll], refl
end

lemma list_reverse_aux_spec (p r : pointer) (xs ys : list word)
: sat (list_reverse_aux p r)
      { pre := is_list p xs :*: is_list r ys
      , post := λ r', is_list r' (reverse xs ++ ys) } :=
begin
  revert p r ys,
  induction xs ; intros p r ys,
  case nil
  { simp [is_list],
    apply context_left,
    intro h,
    rw [list_reverse_aux_def,if_pos h],
    apply postcondition _ (return.spec r _),
    intro, simp, },
  case cons x xs
  { simp [is_list],
    rw [s_and_assoc],
    apply context_left,
    intro h,
    rw [list_reverse_aux_def,if_neg h,s_exists_s_and_distr],
    apply s_exists_intro_pre, intro nx,
    apply bind_framing_left _ (read_nth.spec p 1 [x,nx] (of_as_true trivial)),
    { rw s_and_assoc },
    intro r, simp [nth_le,s_and_assoc],
    apply context_left,
    intro, subst r,
    apply bind_framing_left _ (write_nth.spec p _ 1 [x,nx] _),
    { refl },
    intro x, cases x, simp [replace,const],
    have h : is_list r ys = is_list ( word.to_word r ).to_ptr ys, { simp },
    rw h, clear h,
    generalize : (word.to_word r) = k,
    apply s_exists_elim_pre k,
    apply precondition (is_list nx.to_ptr xs :*: is_list p (x :: ys)),
    apply ih_1 nx.to_ptr p (x :: ys),
    { simp [is_list,embed_eq_emp h],
      rw [s_and_s_exists_distr],
      apply s_exists_congr,
      intro, ac_refl } }
end

def list_reverse (p : pointer) : program pointer :=
list_reverse_aux p 0

lemma list_reverse_spec (p : pointer) (xs : list word)
: sat (list_reverse p)
      { pre := is_list p xs
      , post := λ r, is_list r (reverse xs) } :=
begin
  unfold list_reverse,
  apply precondition (is_list p xs :*: is_list 0 []),
  apply postcondition _ (list_reverse_aux_spec p 0 xs []),
  { intros, simp },
  { simp [is_list,embed_eq_emp], }
end

def list_reverse' (p : pointer) : program pointer :=
sorry

lemma list_reverse_spec' (p : pointer) (vs : list word)
: sat (list_reverse' p) { pre := is_list p vs,
                         post := λ q, is_list q (list.reverse vs) } :=
sorry

def list_reverse_dup_aux : pointer → pointer → program pointer :=
fix2 (λ list_reverse_dup_aux p q,
if p = 0 then return q
else do
  x  ← read_nth p 0 2 dec_trivial,
  q' ← alloc [x,⟨ q ⟩],
  p' ← read_nth p 1 2 dec_trivial,
  list_reverse_dup_aux p'.to_ptr q')

lemma list_reverse_dup_aux_def (p q : pointer)
: list_reverse_dup_aux p q =
  if p = 0 then return q
  else do
    x  ← read_nth p 0 2 dec_trivial,
    q' ← alloc [x,⟨ q ⟩],
    p' ← read_nth p 1 2 dec_trivial,
    list_reverse_dup_aux p'.to_ptr q' := sorry

def segment : pointer → pointer → list word → hprop
 | p q [] := [| p = q |]
 | p q (x :: xs) := [| p ≠ q |] :*: ∃∃ nx, p ↦* [x,nx] :*: segment nx.to_ptr q xs

lemma segment_nil (p : pointer) (xs : list word)
: segment p 0 xs = is_list p xs :=
sorry

lemma segment_append (p q : pointer) (xs ys : list word)
: segment p q (xs++ys) = ∃∃ r, segment p q xs :*: segment q r ys :=
sorry

lemma segment_single (p q : pointer) (x : word)
: segment p q [x] = p ↦* [x,⟨ q ⟩] :=
sorry

lemma list_reverse_dup_aux_spec (p q r : pointer) (xs ys zs : list word)
: sat (list_reverse_dup_aux q r)
      { pre := segment p q xs :*: is_list q ys :*: is_list r zs,
        post := λ q, is_list p (xs ++ ys) :*: is_list q (list.reverse ys ++ zs) } :=
begin
  revert xs q zs r,
  induction ys ; intros xs q zs r,
  case nil
  { unfold is_list,
    extract_context [`h],
    rw [list_reverse_dup_aux_def,if_pos h],
    subst q, simp [segment_nil],
    apply postcondition _ (return.spec _ _),
    { intros, ac_refl } },
  case cons y ys
  { unfold is_list,
    extract_context [`h],
    s_exists `nx,
    rw [list_reverse_dup_aux_def,if_neg h],
    bind_step `ry,
--     extract_context [`h₀],
    bind_step `q',
    bind_step `p',
    unfold nth_le,
    extract_context [`h₀,`h₁,`h₂],
    subst ry, subst p',
    -- apply s_exists_elim_pre nx,
    -- apply s_exists_replace_pre word.to_word word.to_ptr,
    -- { intro, cases x, refl },
    have HH := (ih_1 (xs ++ [y]) _ (y :: zs) _),
    apply framing_spec' _ HH,
    { simp [segment_append,is_list],
      simp [s_exists_s_and_distr,s_and_s_exists_distr],
      -- apply s_exists_intro,
      -- apply s_exists_intro,
      -- apply s_imp_of_eq, simp [embed_eq_emp h₂,s_and_assoc],
      admit },
    { intro, simp, rw [s_and_emp] }, },
end

def list_reverse_dup (p : pointer) : program pointer :=
list_reverse_dup_aux p 0

lemma list_reverse_dup_spec (p : pointer) (vs : list word)
: sat (list_reverse_dup p)
      { pre := is_list p vs,
        post := λ q, is_list p vs :*: is_list q (list.reverse vs) } :=
begin
  unfold list_reverse_dup,
  apply adapt_spec (list_reverse_dup_aux_spec p p 0 [] vs []),
  { simp [segment,is_list,embed_eq_emp] },
  { intro r, simp }
end

inductive tree (α : Type u)
  | leaf {} : tree
  | node : tree → α → tree → tree

def is_tree : pointer → tree word → hprop
  | p tree.leaf := [| p = 0 |]
  | p (tree.node l x r) := ∃∃ lp rp : word,
          [| p ≠ 0 |] :*:
          p ↦* [lp,x,rp] :*:
          is_tree lp.to_ptr l :*:
          is_tree rp.to_ptr r

def free_tree : pointer → program unit :=
sorry

lemma free_tree_spec (p : pointer) (t : tree word)
: sat (free_tree p) { pre := is_tree p t
                    , post := λ _, emp } :=
sorry

end examples

end separation
