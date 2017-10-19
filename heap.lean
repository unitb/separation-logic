import data.bitvec
import data.dlist
import data.list.perm
import util.logic
import util.control.applicative
import util.control.monad.non_termination
import util.data.option
import util.meta.tactic

universes u v w w'

open nat list (hiding bind) function

@[reducible]
def pointer := ℕ

structure word :=
to_word :: (to_ptr : ℕ)

instance : has_zero word := ⟨ ⟨ 0 ⟩ ⟩
instance : has_one word := ⟨ ⟨ 1 ⟩ ⟩
instance : has_add word := ⟨ λ x y, ⟨ x.to_ptr + y.to_ptr ⟩ ⟩

def heap := pointer → option word

namespace heap

def disjoint (h₀ h₁ : heap) :=
(∀ p, h₀ p = none ∨ h₁ p = none)

infix ` ## `:51 := disjoint

def part'  (h₀ h₁ : heap) (_ : h₀ ## h₁ . tactic.assumption) : heap
 | p := h₀ p <|> h₁ p

def maplet (p : pointer) (v : word) : heap
  | q :=
if p = q then some v else none

protected def emp : heap :=
λ _, none

@[simp]
lemma heap_emp_disjoint (h : heap)
: heap.emp ## h :=
by { dunfold disjoint heap.emp, intros, left, refl }

@[simp]
lemma disjoint_heap_emp (h : heap)
: h ## heap.emp :=
by { dunfold disjoint heap.emp, intros, right, refl }

@[simp]
lemma heap_emp_part'_eq_self (h : heap)
: part' heap.emp h (heap_emp_disjoint _) = h :=
begin
  apply funext, intro,
  unfold part',
  cases (h x) ; simp [heap.emp,has_orelse.orelse,option.orelse]
end

@[simp]
lemma part'_heap_emp_eq_self (h : heap)
: part' h heap.emp (disjoint_heap_emp _) = h :=
begin
  apply funext, intro,
  unfold part',
  cases (h x) ; simp [heap.emp,has_orelse.orelse,option.orelse]
end

protected def mk : pointer → list word → heap
| _ [] := heap.emp
| p (v :: vs) := λ q, maplet p v q <|> mk (p+1) vs q

lemma maplet_disjoint_heap_mk_of_lt {p q : pointer} (v : word) (vs : list word)
  (h : p < q)
: disjoint (maplet p v) (heap.mk q vs) :=
begin
  revert q v,
  induction vs with v vs ; intros q v h,
  { apply disjoint_heap_emp },
  { simp [(##)], intro ptr,
    simp_intros h₁ [or_iff_not_imp,heap.mk],
    split,
    { simp [maplet] at ⊢ h₁,
      ite_cases with h₀ at h₁ ⊢,
      { contradiction },
      rw [← h₀,if_neg],
      apply ne_of_gt, apply h  },
    { revert h₁, rw ← or_iff_not_imp,
      apply ih_1,
      transitivity q, assumption,
      apply lt_add_of_pos_right,
      apply zero_lt_one, } }
end

lemma maplet_disjoint_heap_mk (p : pointer) (v : word) (vs : list word)
: maplet p v ## heap.mk (p + 1) vs :=
begin
  apply maplet_disjoint_heap_mk_of_lt,
  apply lt_add_of_pos_right,
  apply zero_lt_one,
end

lemma heap_mk_cons (p : pointer) (v : word) (vs : list word)
:   heap.mk p (v :: vs)
  = part' (maplet p v) (heap.mk (p+1) vs) (maplet_disjoint_heap_mk p v vs) :=
by { funext x, simp [heap.mk,part'] }

def left_combine (h₀ h₁ : heap) : heap
 | p := h₀ p <|> h₁ p

protected def delete : pointer → ℕ → heap → heap
 | p 0 h q := h q
 | p (succ n) h q :=
if p = q then none
else delete (p+1) n h q

infix ` <+ `:54 := left_combine

@[symm]
lemma disjoint_symm {h₀ h₁ : heap}
  (h : h₀ ## h₁)
: h₁ ## h₀ :=
assume p, or.symm (h p)

lemma part'_comm {h₀ h₁ : heap}
  (h : h₀ ## h₁)
: part' h₀ h₁ = part' h₁ h₀ (disjoint_symm h) :=
begin
  funext p, unfold part',
  cases h p with h h ; simp [h],
end

lemma part_disjoint_assoc_left {h₀ h₁ h₂ : heap}
  (Hdisj : h₀ ## h₁)
  (Hdisj' : h₁ ## h₂)
  (h : part' h₀ h₁ Hdisj ## h₂)
: h₀ ## part' h₁ h₂ Hdisj' :=
begin
  intro p,
  cases h p with h' h' ; unfold part' at *,
  { rw or_else_eq_none_iff at h',
    simp [h'.left] },
  { simp [h',Hdisj p], },
end

lemma part_disjoint_assoc_right {h₀ h₁ h₂ : heap}
  (Hdisj : h₀ ## h₁)
  (Hdisj' : h₁ ## h₂)
  (h : h₀ ## part' h₁ h₂)
: part' h₀ h₁ ## h₂ :=
begin
  intro p,
  cases h p with h' h' ; unfold part' at *,
  { simp [h',Hdisj' p], },
  { rw or_else_eq_none_iff at h',
    simp [h'.right] },
end

@[simp]
lemma eq_emp_of_part' (hp a : heap)
  (h  : a ## hp)
: a = part' a hp ↔ hp = heap.emp :=
begin
  split ; intro h₀,
  { funext k,
    have h₁ : a k = part' a hp h k,
    { rw ← h₀, },
    clear h₀,
    dsimp [part',heap.emp,heap.disjoint] at *,
    specialize h k,
    cases h with h₂ h₂ ; simp [h₂] at h₁,
    rw h₁, rw h₂, },
  { simp [h₀], }
end

lemma part'_disjoint {h₁ h₂ h₃ : heap}
  {H₀ : h₂ ## h₃}
  (H₁ : h₁ ## h₃)
  (H₂ : h₁ ## h₂)
: part' h₂ h₃ ## h₁ :=
begin
  intro p,
  rw [or.comm,or_iff_not_imp,part',or_else_eq_none_iff],
  intros H₃,
  specialize H₁ p,
  specialize H₂ p,
  rw or_iff_not_imp at H₁ H₂,
  split
  ; xassumption
  ; xassumption,
end

lemma disjoint_part' {h₁ h₂ h₃ : heap}
  {H₀ : h₂ ## h₃}
  (H₁ : h₁ ## h₃)
  (H₁ : h₁ ## h₂)
: h₁ ## part' h₂ h₃ :=
by { apply disjoint_symm,
     apply part'_disjoint
     ; assumption }

lemma disjoint_of_part'_disjoint_right {h₁ h₂ h₃ : heap}
  (H₁ : h₂ ## h₃)
  (H₀ : part' h₂ h₃ ## h₁)
: h₃ ## h₁ :=
begin
  intro p,
  cases H₀ p with H₂ H₂,
  { unfold part' at H₂,
    rw or_else_eq_none_iff at H₂,
    simp [H₂.right] },
  { simp [H₂] }
end

lemma disjoint_of_part'_disjoint_left {h₁ h₂ h₃ : heap}
  (H₁ : h₂ ## h₃)
  (H₀ : part' h₂ h₃ ## h₁)
: h₂ ## h₁ :=
begin
  have H₁ := disjoint_symm H₁,
  apply disjoint_of_part'_disjoint_right H₁,
  rw part'_comm, apply H₀,
end

lemma disjoint_of_disjoint_part'_right {h₁ h₂ h₃ : heap}
  (H₁ : h₂ ## h₃)
  (H₀ : h₁ ## part' h₂ h₃)
: h₁ ## h₃ :=
begin
  intro p,
  rw or_iff_not_imp,
  intro H₂,
  specialize H₀ p,
  rw or_iff_not_imp at H₀,
  specialize H₀ H₂,
  simp [part'] at H₀,
  apply H₀.right,
end

lemma disjoint_of_disjoint_part'_left {h₁ h₂ h₃ : heap}
  (H₁ : h₂ ## h₃)
  (H₀ : h₁ ## part' h₂ h₃)
: h₁ ## h₂ :=
by { apply disjoint_of_disjoint_part'_right,
     rw part'_comm, apply H₀,
     symmetry, apply H₁, }

namespace tactic.interactive

open heap
open tactic tactic.interactive (ite_cases)
open lean lean.parser interactive interactive.types

meta def break_disjoint_asm_symm (l : expr)
: tactic unit :=
do t ← infer_type l,
   match t with
    | `(%%h₀ ## (%%h₁ : heap)) :=
      do h ← get_unused_name `h,
         to_expr ``(disjoint_symm %%l) >>= note h none,
         return ()
    | _ :=
         fail $ format! "expecting {l} of the form _ ## _"
   end

meta def break_disjoint_asm_r (l : expr)
: tactic (list expr) :=
do t ← infer_type l,
   match t with
    | `(%%h₀ ## part' %%h₁ %%h₂ %%h₃) :=
      do h ← get_unused_name `h,
         r ← to_expr ``(disjoint_of_disjoint_part'_right _ %%l) >>= note h none,
         h ← get_unused_name `h,
         r' ← to_expr ``(disjoint_of_disjoint_part'_left _ %%l) >>= note h none,
         try (tactic.clear l),
         return [r,r']
    | _ :=
         fail $ format! "expecting {l} of the form _ ## _"
   end
meta def break_disjoint_asm_l (l : expr)
: tactic (list expr) :=
do t ← infer_type l,
   match t with
    | `(part' %%h₁ %%h₂ %%h₃ ## %%h₀) :=
      do h ← get_unused_name `h,
         r ← to_expr ``(disjoint_of_part'_disjoint_right _ %%l) >>= note h none,
         h ← get_unused_name `h,
         r' ← to_expr ``(disjoint_of_part'_disjoint_left _ %%l) >>= note h none,
         try (tactic.clear l),
         return [r,r']
    | _ :=
         break_disjoint_asm_r l
   end

meta def break_disjoint_asm'
: expr → tactic unit
| l :=
do xs ← break_disjoint_asm_l l,
   xs.for_each (try ∘ break_disjoint_asm')

meta def break_disjoint_asm (l : parse ident)
: tactic (list expr) :=
do get_local l >>= break_disjoint_asm_l

meta def break_disjoint_asms
: tactic unit :=
do ls ← local_context,
   ls.for_each (try ∘ break_disjoint_asm'),
   ls ← local_context,
   ls.for_each (try ∘ break_disjoint_asm_symm)

meta def prove_disjoint'
: tactic unit :=
    assumption
<|> (`[ apply part'_disjoint ] ; assumption )
<|> (`[ apply disjoint_part' ] ; assumption )
<|> failed

meta def prove_disjoint
: tactic unit :=
do break_disjoint_asms,
   prove_disjoint'

run_cmd add_interactive [`prove_disjoint]

end tactic.interactive

lemma part'_assoc {h₀ h₁ h₂ : heap}
  (Hdisj₀ : h₀ ## h₁)
  (Hdisj₂ : part' h₀ h₁ ## h₂)
: part' (part' h₀ h₁) h₂ Hdisj₂ = part' h₀ (part' h₁ h₂
     (by prove_disjoint)) (by prove_disjoint) :=
by { funext p, simp [part'] }

lemma delete_disjoint_delete {p : pointer} {n : ℕ} {hp₀ hp₁ : heap}
  (h : hp₀ ## hp₁)
: heap.delete p n hp₀ ## heap.delete p n hp₁ :=
begin
  revert p,
  induction n with n ; intro p,
  { intro q,
    simp [heap.delete,h q], },
  { intro q,
    simp [heap.delete],
    ite_cases,
    apply ih_1, simp },
end

lemma delete_over_part' {p : pointer} {n : ℕ} {hp₀ hp₁ : heap}
  (h : hp₀ ## hp₁)
:   heap.delete p n (part' hp₀ hp₁)
  = part' (heap.delete p n hp₀) (heap.delete p n hp₁) (delete_disjoint_delete h) :=
begin
  revert p,
  induction n with n ; intro p,
  { funext q,
    refl },
  { funext q,
    simp [heap.delete],
    ite_cases with h',
    { simp [ih_1,part',heap.delete,if_neg,h'], },
    { simp [part',heap.delete,if_pos,h'], } }
end

lemma heap_delete_maplet (p q : pointer) (k : ℕ) (v : word)
  (h : p < q)
: heap.delete q k (maplet p v) = maplet p v :=
begin
  funext x,
  revert q,
  induction k with k ; intros q h, refl,
  { simp [heap.delete],
    ite_cases, apply @ih_1 (q + 1) _,
    { transitivity q, assumption,
      apply lt_succ_self },
    simp [maplet],
    subst x,
    rw if_neg,
    apply ne_of_lt h },
end

lemma delete_part'_heap_mk {p : pointer} {vs : list word} {hp : heap}
  (h : heap.mk p vs ## hp)
: heap.delete p (length vs) (part' (heap.mk p vs) hp) = hp :=
begin
  revert p,
  induction vs with v vs
  ; intros p h₀,
  { simp [heap.delete,heap.mk], funext q, refl },
  { funext q,
    simp [length,add_one,heap.delete],
    ite_cases,
    { simp [heap_mk_cons],
      have h₁ : heap.mk (p + 1) vs ## hp,
      { simp [heap.mk] at h₀,
        intro p',
        specialize h₀ p',
        rw or_iff_not_imp at h₀ ⊢,
        intros h₁, apply h₀,
        rw or_else_eq_none_iff,
        revert h₁, apply mt,
        apply and.elim_right, },
      have h₂ : heap.delete (succ p) (length vs) (maplet p v) = maplet p v,
      { apply heap_delete_maplet, apply lt_succ_self, },
      simp [part'_assoc,delete_over_part',ih_1 h₁,h₂,part',maplet,if_neg,h], },
  { have h₁ : maplet p v ## hp,
    { rw heap_mk_cons at h₀, prove_disjoint },
    simp [(##)] at h₁,
    specialize h₁ q, rw [or_comm,or_iff_not_imp] at h₁,
    symmetry, apply h₁,
    simp [maplet,if_pos,h], contradiction }, }
end

protected def insert (hp : heap) (p : pointer) (v : word) : heap
 | q := if p = q then some v else hp q

lemma part'_insert (hp hp' : heap) (p : pointer) (v : word)
  (h₀ : hp.insert p v ## hp')
  (h₁ : hp ## hp')
: part' (hp.insert p v) hp' = (part' hp hp').insert p v :=
begin
  funext x,
  simp [part',heap.insert],
  ite_cases,
  simp [some_or_else],
end

lemma maplet_insert_disjoint_iff (p : pointer) (v v' : word) (hp : heap)
: (maplet p v).insert p v' ## hp ↔ maplet p v ## hp :=
begin
  simp [disjoint,heap.insert],
  apply forall_congr,
  intro p',
  ite_cases,
  simp [maplet,if_pos,h],
  apply or_congr,
  refl,
  split ; intro ; contradiction
end

end heap
