import data.bitvec
import data.dlist
import data.list.basic

import util.logic
import util.control.applicative
import util.control.monad.non_termination
import separation.heap
import separation.program
import separation.specification
import separation.tactics

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
  bind_step with t h,
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
  modify_nth p 0 2 (+1),
  p' ← read_nth p 1 2,
  map_list p'.to_ptr)

lemma map_list_def (p : pointer)
: map_list p =
  if p = 0 then return ()
  else do
    modify_nth p 0 2 (+1),
    p' ← read_nth p 1 2,
    map_list p'.to_ptr :=
begin
  unfold map_list,
  -- transitivity,
  admit -- rw [program.fix_unroll,dif_eq_if], refl
end

@[ptr_abstraction]
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
    extract_context h,
    rw embed_s_and_self,
    rw [map_list_def],
    simp [h],
    apply return.spec' },
  case cons x xs
  { unfold map is_list,
    s_intros nx Hp_nz,
    rw [map_list_def],
    rw if_neg Hp_nz, simp,
    bind_step,
    bind_step with _ h,
    unfold replace nth_le at *,
    last_step (ih_1 nx.to_ptr), }
end

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

lemma list_reverse_aux.spec (p r : pointer) (xs ys : list word)
: sat (list_reverse_aux p r)
      { pre := is_list p xs :*: is_list r ys
      , post := λ r', is_list r' (reverse xs ++ ys) } :=
begin
  revert ys p r,
  induction xs ; intros ys p r,
  case nil
  { simp [is_list],
    extract_context h,
    rw [list_reverse_aux_def,if_pos h],
    last_step, },
  case cons x xs
  { simp [is_list],
    s_intros nx h,
    rw [list_reverse_aux_def,if_neg h],
    bind_step with p' h',
    bind_step, unfold replace const,
    last_step (ih_1 (x :: ys)), }
end

def list_reverse (p : pointer) : program pointer :=
list_reverse_aux p 0

lemma list_reverse.spec (p : pointer) (xs : list word)
: sat (list_reverse p)
      { pre := is_list p xs
      , post := λ r, is_list r (reverse xs) } :=
begin
  unfold list_reverse,
  apply precondition (is_list p xs :*: is_list 0 []),
  apply postcondition _ (list_reverse_aux.spec p 0 xs []),
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
  x  ← read_nth p 0 2,
  q' ← alloc [x,⟨ q ⟩],
  p' ← read_nth p 1 2,
  list_reverse_dup_aux p'.to_ptr q')

lemma list_reverse_dup_aux_def (p q : pointer)
: list_reverse_dup_aux p q =
  if p = 0 then return q
  else do
    x  ← read_nth p 0 2,
    new ← alloc [x,⟨ q ⟩],
    next ← read_nth p 1 2,
    list_reverse_dup_aux next.to_ptr new :=
sorry

def segment : pointer → pointer → list word → hprop
 | p q [] := [| p = q |]
 | p q (x :: xs) := [| p ≠ q |] :*: ∃∃ nx, p ↦* [x,nx] :*: segment nx.to_ptr q xs

lemma segment_nil (p : pointer) (xs : list word)
: segment p 0 xs = is_list p xs :=
sorry

@[ptr_abstraction]
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
  revert xs zs q r,
  induction ys ; intros xs zs q r,
  case nil
  { unfold is_list,
    extract_context h,
    rw [list_reverse_dup_aux_def],
    subst q, simp [segment_nil],
    apply postcondition _ (return.spec _ _),
    { intros, dsimp [list.reverse_nil], ac_refl } },
  case cons y ys
  { unfold is_list,
    extract_context h,
    s_exists nx,
    rw [list_reverse_dup_aux_def,if_neg h],
    bind_step with x  h₀,
    bind_step with new h₁,
    bind_step with next h,
    repeat { rw [← s_and_assoc] },
    have HH := (ih_1 (xs ++ [x]) (x :: zs) next.to_ptr new),
    -- last_step (ih_1 (xs ++ [y]) (y :: zs)),
    -- apply s_exists_elim_pre nx,
    -- apply s_exists_replace_pre word.to_word word.to_ptr,
    -- { intro, cases x, refl },
    -- have HH := (ih_1 (xs ++ [y]) (y :: zs) _),

    apply framing_spec' _ HH,
    { simp [segment_append,is_list],
      simp [s_exists_s_and_distr,s_and_s_exists_distr],
      apply s_exists_intro (word.to_word r),
      apply s_exists_intro,
      simp [embed_eq_emp h₁],
      -- ac_match',
      -- apply s_imp_of_eq, simp [embed_eq_emp h₂,s_and_assoc],
      admit, admit },
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

@[ptr_abstraction]
def is_tree : pointer → tree word → hprop
  | p tree.leaf := [| p = 0 |]
  | p (tree.node l x r) := ∃∃ lp rp : word,
          [| p ≠ 0 |] :*:
          p ↦* [lp,x,rp] :*:
          is_tree lp.to_ptr l :*:
          is_tree rp.to_ptr r

def free_tree : pointer → program unit :=
fix λ free_tree p, do
if p = 0 then return ()
else do
  l ← read_nth p 0 3,
  r ← read_nth p 2 3,
  free p 3,
  free_tree l.to_ptr,
  free_tree r.to_ptr

lemma free_tree_def (p : pointer)
: free_tree p =
  if p = 0 then return ()
  else do
    l ← read_nth p 0 3,
    r ← read_nth p 2 3,
    free p 3,
    free_tree l.to_ptr,
    free_tree r.to_ptr :=
sorry

lemma free_tree_spec (p : pointer) (t : tree word)
: sat (free_tree p) { pre := is_tree p t
                    , post := λ _, emp } :=
begin
  revert p,
  induction t ; intro p,
  case tree.leaf
  { unfold is_tree,
    rw free_tree_def,
    s_intros h,
    simp [h],
    apply return.spec', },
  case tree.node l x r
  { unfold is_tree,
    s_intros lp rp h,
    rw [free_tree_def,if_neg h],
    bind_step with l hl,
    bind_step with r hr,
    bind_step,
    bind_step ih_1,
    last_step ih_2 }
end

end examples

end separation
