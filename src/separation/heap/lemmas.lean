
import util.meta.tactic

import separation.heap.basic

namespace heap

open nat list (hiding bind)

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
      apply vs_ih,
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
  ; apply_assumption
  ; apply_assumption,
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
    apply n_ih, simp },
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
    { simp [n_ih,part',heap.delete,if_neg,h'], },
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
    ite_cases, apply @k_ih (q + 1) _,
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
      simp [part'_assoc,delete_over_part',vs_ih h₁,h₂,part',maplet,if_neg,h], },
  { have h₁ : maplet p v ## hp,
    { rw heap_mk_cons at h₀, prove_disjoint },
    simp [(##)] at h₁,
    specialize h₁ q, rw [or_iff_not_imp] at h₁,
    symmetry, apply h₁,
    simp [maplet,if_pos,h] }, }
end

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
end

@[simp]
lemma some_part'
  (hp₀ hp₁ : heap)
  (h : hp₀ ## hp₁)
: some (part' hp₀ hp₁) = part (some hp₀) (some hp₁) :=
by { simp [part,bind,option.bind,dif_pos, h], }

@[simp]
lemma heap_emp_part
  (hp : heap)
: part (some heap.emp) (some hp) = some hp :=
by simp [part]

@[simp]
lemma part_heap_emp
  (hp : heap)
: part (some hp) (some heap.emp) = some hp :=
by simp [part]

end heap

namespace tactic.interactive

open heap
open tactic tactic.interactive (ite_cases)
open lean lean.parser interactive interactive.types

meta def try_then (x y : tactic unit) : tactic unit :=
focus1 $
do (some ()) ← try_core x | tactic.skip,
   tactic.all_goals y

meta def expand_part_ite : tactic unit :=
do tactic.try `[ dsimp [part] ],
   tactic.reflexivity <|> try_then (ite_cases none $ loc.ns [none]) expand_part_ite

meta def contradict_asm
: tactic unit :=
do ls ← local_context,
   ls.any_of (λ e,
     do `(¬ %%t) ← infer_type e | failed ,
         exfalso, tactic.apply e, tactic.clear e)

end tactic.interactive

namespace heap

lemma part_assoc
  (a b c : option heap)
: part (part a b) c = part a (part b c) :=
begin
  cases a ; cases b ; cases c
  ; expand_part_ite,
   all_goals { {contradict_asm ; prove_disjoint} <|> rw part'_assoc },
end

lemma part_comm
  (a b : option heap)
: part a b = part b a :=
begin
  cases a ; cases b
  ; dsimp [part] ; try { refl }
  ; ite_cases with i
  ; ite_cases with i'
  ; try { contradict_asm, symmetry, assumption },
  rw part'_comm,
end

instance : is_associative (option heap) part :=
⟨ part_assoc ⟩
instance : is_commutative (option heap) part :=
⟨ part_comm ⟩

lemma disjoint_of_is_some_part
  {hp₀ hp₁ : heap}
  (h : (part (some hp₀) (some hp₁)).is_some)
: hp₀ ## hp₁ :=
by { dsimp [part] at h,
     ite_cases with h at h,
     contradiction,
     assumption }

lemma disjoint_of_part_eq_some
  {hp₀ hp₁ hp₂ : heap}
  (h : some hp₂ = (part (some hp₀) (some hp₁)))
: hp₀ ## hp₁ :=
by { apply disjoint_of_is_some_part, rw ← h, exact rfl }

lemma eq_part'_of_some_eq_part
  (hp₀ hp₁ hp : heap)
  (h : some hp = part (some hp₀) (some hp₁))
: hp = part' hp₀ hp₁ (disjoint_of_part_eq_some h) :=
by { apply @option.no_confusion _ _ (some hp) (some _) _ id,
     simp [h], }

lemma is_some_of_is_some_part_right
  (hp₀ : option heap) {hp₁ : option heap}
  (h : (part hp₀ hp₁).is_some)
: hp₁.is_some :=
by { cases hp₀ ; cases hp₁ ; try { contradiction },
     exact rfl }

lemma is_some_of_is_some_part_left
  {hp₀ : option heap} (hp₁ : option heap)
  (h : (part hp₀ hp₁).is_some)
: hp₀.is_some :=
by { cases hp₀ ; cases hp₁ ; try { contradiction },
     exact rfl }

@[simp]
lemma some_eq_some_iff (x y : heap)
: some x = some y ↔ x = y :=
by { split ; intro h, injection h, subst x }

def opt_apl : option heap → pointer → option word
 | (some hp) p := hp p
 | none _ := none

lemma opt_apl_some (hp : heap) (p : pointer)
: opt_apl (some hp) p = hp p :=
rfl

lemma opt_apl_part_maplet (hp : heap) (p : pointer) (v : word)
  (h : maplet p v ## hp)
: (opt_apl (part (some (maplet p v)) (some hp)) p) = some v :=
begin
  unfold part,
  rw [dif_pos] ; [ skip , apply h ],
  rw [opt_apl,part',maplet,if_pos rfl],
  refl,
end

@[simp]
lemma eq_emp_of_part (a : heap) (hp : option heap)
: some a = part (some a) hp ↔ hp = some heap.emp :=
begin
  cases hp ; dsimp [part],
  split ; intro h ; contradiction,
  ite_cases with h₀,
  split ; intros h₁,
  { contradiction },
  { injection h₁ with h₂, simp [h₂] at h₀,
    cases h₀, },
  split ; intro h₁ ; injection h₁ with h₂,
  { simp [eq_emp_of_part'] at h₂,
    simp [h₂] },
  { simp [h₂], }
end

@[simp]
lemma part'_eq_emp (a b : option heap)
: part a b = some heap.emp ↔ a = some heap.emp ∧ b = some heap.emp :=
begin
  split ; simp_intros h ;
  cases a ; cases b
  ; try { refl }
  ; try { cases h with h₀ h₁ }
  ; try { contradiction }
  ; try { rw [h₀,h₁,← some_part' _ _ (disjoint_heap_emp _)
             ,heap_emp_part'_eq_self] },
  { unfold part at h,
    revert h, ite_cases with h,
    contradiction,
    intro h₀,
    injection h₀ with h₁,
    have h₂ : ∀ p, part' a b h p = heap.emp p,
    { intro, rw h₁ },
    simp [part',heap.emp] at h₂,
    split ; congr ; funext p,
    { simp [(h₂ p).left], refl },
    { simp [(h₂ p).right], refl }, }
end

@[simp]
lemma emp_left_combine (hp : heap)
: heap.emp <+ hp = hp :=
by { funext y, simp [left_combine,heap.emp], }

@[simp]
lemma left_combine_emp (hp : heap)
: hp <+ heap.emp = hp :=
by { funext y, simp [left_combine,heap.emp], }

@[simp]
lemma heap_mk_nil_eq_emp (p : pointer)
: heap.mk p [] = heap.emp := by simp [heap.mk]

lemma some_insert_left_eq_part {hp₀ hp₁ : heap}
  (h : hp₀ ## hp₁)
: some (hp₀ <+ hp₁) = part (some hp₀) (some hp₁) :=
sorry

end heap
