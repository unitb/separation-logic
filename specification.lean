import data.bitvec
import data.dlist
import util.logic
import util.data.option
import util.control.applicative
import util.control.monad.non_termination
import util.control.monad.state
import util.meta.tactic.monotonicity
import separation.heap
import separation.heap2
import separation.program

import logic.basic

universes u v w w'

open nat list function

namespace separation

structure hprop :=
  (apply : heap → Prop)

def embed (p : Prop) : hprop :=
⟨ λ h, p ∧ h = heap.emp ⟩

notation `[| `p` |]` := embed p

def s_and (p q : hprop) : hprop :=
⟨ λ h, ∃ hp₀ hp₁,
         some h = part_ (some hp₀) (some hp₁) ∧
         p.apply hp₀ ∧
         q.apply hp₁ ⟩

infix ` :*: `:55 := s_and

def emp : hprop :=
⟨ λ h, h = heap.emp ⟩

@[simp]
protected lemma apply_emp (hp : heap)
: emp.apply hp ↔ hp = heap.emp :=
by refl

lemma exists_congr_elim {α : Sort u} {p : α → Prop} {q : Prop} (x : α)
  (h : ∀ y, p y ↔ y = x ∧ q)
: (∃ y, p y) ↔ q :=
by simp [h]

@[simp]
lemma s_and_emp (p : hprop)
: p :*: emp = p :=
by { cases p, simp [s_and], }

lemma s_and_comm (p q : hprop)
: p :*: q = q :*: p :=
begin
  cases p, cases q, simp [s_and],
  congr, funext ihp,
  apply iff.to_eq,
  split ; simp,
  { intros hp₀ h₀ hp₁ h₁ hh,
    existsi [hp₁,hp₀,h₀,h₁],
    rw hh, ac_refl, },
  { intros hp₀ hp₁ h₁ h₀ hh,
    existsi [hp₁,h₁,hp₀,h₀],
    rw hh, ac_refl, }
end

@[simp]
lemma emp_s_and (p : hprop)
: emp :*: p = p :=
by rw [s_and_comm,s_and_emp]

def points_to (p : ℕ) (val : word) : hprop :=
⟨ λ h, h = maplet p val ⟩

infix ` ↦ `:60 := points_to

def points_to_multiple : ∀ (p : ℕ), list word → hprop
 | _ [] := emp
 | p (x :: xs) := p ↦ x :*: points_to_multiple (p+1) xs

infix ` ↦* `:60 := points_to_multiple

structure spec (r : Type u) :=
  (pre : hprop)
  (post : r → hprop)

def sat {α} (p : program α) (s : spec α) : Prop :=
∀ (σ : hstate) hp₀ hp₁,
   some σ.heap = part_ (some hp₀) (some hp₁) →
   s.pre.apply hp₀ →
(∃ r σ' hp', p σ ~> (r, σ') ∧
            some σ'.heap = part_ (some hp') (some hp₁) ∧
            (s.post r).apply hp')

lemma s_and_part {hp₀ hp₁ : heap} {p₀ p₁ : hprop}
  (h : hp₀ ## hp₁)
  (Hp₀ : p₀.apply hp₀)
  (Hp₁ : p₁.apply hp₁)
: (p₀ :*: p₁).apply (part' hp₀ hp₁) :=
begin
  cases p₀, cases p₁, simp [s_and],
  split, split, assumption,
  split, split, assumption,
  simp,
end

lemma embed_eq_emp {p : Prop}
  (hp : p)
: [| p |] = emp :=
by simp [embed,emp,eq_true_intro hp]

@[simp]
lemma embed_s_and_apply {p : Prop} {q : hprop}
  (hp : heap)
: ([| p |] :*: q).apply hp ↔ p ∧ q.apply hp :=
begin
 simp [s_and,embed],
 apply and_congr_right,
 intros h, split,
 { simp, intros hp₀ hp₁ h₁ h₀ hh,
   simp [h₀] at hh, simp [hh,h₁], },
 { intros h',
   existsi [heap.emp,hp,h',rfl],
   simp, }
end

def hexists {α : Type u} (p : α → hprop) : hprop :=
⟨ λ ptr, ∃ i, (p i).apply ptr ⟩

notation `∃∃` binders `, ` r:(scoped P, hexists P) := r

def h_imp (p q : hprop) : Prop :=
∀ h, p.apply h → q.apply h

infix ` =*> `:41 := h_imp

lemma s_and_assoc (p q r : hprop)
: (p :*: q) :*: r = p :*: (q :*: r) :=
begin
  cases p with p, cases q with q, cases r with r,
  simp [s_and],
  congr, funext hp,
  apply iff.to_eq,
  split ; simp,
  { intros hp_pq hp_r Hr Hd_pqr,
    intros hp_p Hp hp_q Hq Hpq,
    have Hd_qr : hp_q ## hp_r,
    { apply disjoint_of_is_some_part_,
      apply is_some_of_is_some_part__right (some hp_p),
      apply is_some_of_eq_some hp,
      simp [Hd_pqr,Hpq], ac_refl },
    existsi [hp_p,Hp,part' hp_q hp_r Hd_qr],
    simp [Hd_pqr,Hpq],
    split, ac_refl,
    let hp_qr := part' hp_q hp_r,
    existsi [hp_q,Hq,hp_r,Hr], refl, },
  { intros hp_p Hp hp_qr Hd_pqr,
    intros hp_q Hq hp_r Hr H_qr,
    have Hd_pq : hp_p ## hp_q,
    { apply disjoint_of_is_some_part_,
      apply is_some_of_is_some_part__right (some hp_r),
      apply is_some_of_eq_some hp,
      simp [Hd_pqr,H_qr], ac_refl },
    let hp_pq := part' hp_p hp_q,
    existsi [hp_pq,hp_r,Hr],
    split, simp [Hd_pqr,H_qr], ac_refl,
    existsi [hp_p,Hp,hp_q,Hq], simp },
end

instance : is_associative hprop s_and := ⟨ s_and_assoc ⟩
instance : is_commutative hprop s_and := ⟨ s_and_comm ⟩

lemma embed_s_and_embed (p q : Prop)
: [| p |] :*: [| q |] = [| p ∧ q |] :=
begin
  unfold embed emp s_and, apply congr_arg,
  apply funext, intro, simp [-and_comm],
end

@[simp]
lemma embed_s_and_self (p : Prop)
: [| p |] :*: [| p |] = [| p |] :=
by simp [embed_s_and_embed]

@[refl]
lemma s_imp_refl (p : hprop)
: p =*> p :=
by { intros x h, apply h }

@[trans]
lemma s_imp_trans {p : hprop} (q : hprop) {r : hprop}
  (h₀ : p =*> q)
  (h₁ : q =*> r)
: p =*> r :=
by { intros x h, apply h₁, apply h₀ _ h }

lemma s_exists_intro  {α : Type u}
  {p : hprop} {q : α → hprop} (x : α)
  (h : p =*> q x)
: p =*> ∃∃ x, q x :=
begin
  unfold h_imp hexists at *,
  intros hp h',
  specialize h hp h',
  existsi x, assumption,
end

lemma s_exists_elim  {α : Type u}
  {p : α → hprop} {q : hprop} (x : α)
  (h : ∀ x, p x =*> q)
: (∃∃ x, p x) =*> q :=
begin
  simp [h_imp,hexists] at *,
  intros hp x, apply h,
end

lemma s_imp_of_eq {p q : hprop}
  (h : p = q)
: p =*> q :=
begin
  unfold h_imp,
  rw h,
  intros, assumption
end

@[congr]
lemma s_exists_congr {α : Type u}
  {p q : α → hprop}
  (h : ∀ x, p x = q x)
: hexists p = hexists q :=
begin
  unfold hexists,
  congr,
  simp [h],
end

lemma s_exists_s_and_distr {α : Type u}
  (p : α → hprop) (q : hprop)
: (∃∃ x, p x) :*: q = (∃∃ x, p x :*: q) :=
begin
  simp [s_and,hexists],
  congr, funext hp,
  apply iff.to_eq,
  split ; simp ; intros,
  { split, split, split,
    existsi a,
    existsi a_1,
    assumption },
  { split, split,
    existsi a,
    split, split, assumption,
    assumption },
end

lemma s_and_s_exists_distr {α : Type u}
  (p : α → hprop) (q : hprop)
: q :*: (∃∃ x, p x) = (∃∃ x, q :*: p x) :=
begin
  rw [s_and_comm,s_exists_s_and_distr], congr,
  funext hp, ac_refl
end

section

variables {α β : Type}
variables {P : program α}
variable {P' : α → program β}
variables {p p₀ p₁ q : hprop}
variables {r r₁ : α → hprop}
variables {r' : β → hprop}
variable {s : spec α}

lemma framing_right (q : hprop)
  (h : sat P { pre := p, post := r })
: sat P { pre := p :*: q, post := λ x, r x :*: q } :=
begin
  unfold sat spec.pre spec.post,
  introv Hpart Hpre,
  cases Hpre with hp₂ Hpre, cases Hpre with hp₃ Hpre,
  rw Hpre.left at Hpart,
  cases Hpre with Hpre₀ Hpre₁, cases Hpre₁ with Hpre₁ Hpre₂,
  simp [Hpart],
  have h' : hp₃ ## hp₁,
  { apply disjoint_of_is_some_part_,
    apply is_some_of_is_some_part__right (some hp₂),
    apply is_some_of_eq_some σ.heap,
    simp [Hpart], ac_refl },
  specialize h σ hp₂ (part' hp₃ hp₁),
  simp [Hpart] at h, specialize h (by ac_refl) Hpre₁,
  revert h,
  intros_mono rr σ',
  simp, intros hp' Hr H_yield H_p',
  have Hd_p'_p₃ : hp' ## hp₃,
  { apply disjoint_of_is_some_part_,
    apply is_some_of_is_some_part__right (some hp₁),
    apply is_some_of_eq_some σ'.heap,
    simp [H_p'], ac_refl },
  existsi [part' hp' hp₃,s_and_part _ Hr Hpre₂,H_yield],
  simp [H_p'], ac_refl,
end

lemma framing_left (q : hprop)
  (h : sat P { pre := p, post := r })
: sat P { pre := q :*: p, post := λ x, q :*: r x } :=
begin
  have h := framing_right q h,
  apply eq.mp _ h,
  apply congr_arg,
  apply congr, ac_refl,
  funext x,
  ac_refl,
end

lemma bind_spec (r : α → hprop)
  (h  : sat P { pre := p, post := r })
  (h' : ∀ x, sat (P' x) { pre := r x, post := r' })
: sat (P >>= P') { pre := p, post := r' } :=
begin
  unfold sat, introv h₂ h₃,
  specialize h σ hp₀ hp₁ h₂ h₃,
  cases h with x h,
  cases h with σ' h,
  cases h with hp' h,
  cases h with Hspec₀ h,
  cases h with Hspec₁ Hspec₂, simp at Hspec₂,
  specialize h' x σ' hp' hp₁ Hspec₁ Hspec₂,
  revert h',
  intros_mono r'' σ'' hp'',
  apply and.imp, intros h₀,
  apply nonterm.yields_bind _ _ Hspec₀,
  apply h₀, apply id,
end

lemma postcondition (r : α → hprop)
 (Hspec : sat P { pre := p, post := r })
 (Hside : ∀ x, r x = r₁ x)
: sat P { pre := p, post := r₁ } :=
begin
  apply eq.mp _ Hspec,
  congr, funext x,
  apply Hside,
end

lemma postcondition' (r : α → hprop)
 (Hspec : sat P { pre := p, post := r })
 (Hside : ∀ x, r x =*> r₁ x)
: sat P { pre := p, post := r₁ } :=
begin
  intros _ _ _ H₀ H₁,
  specialize Hspec _ _ _ H₀ H₁,
  revert Hspec,
  intros_mono x hp₀ hp₁ _ _,
  apply Hside,
end

lemma precondition (p : hprop)
 (Hspec : sat P { pre := p, post := r })
 (Hside : p = q)
: sat P { pre := q, post := r } :=
by { subst q, apply Hspec }

lemma precondition' (p : hprop)
 (Hspec : sat P { pre := p, post := r })
 (Hside : q =*> p)
: sat P { pre := q, post := r } :=
begin
  revert Hspec, unfold sat,
  apply forall_imp_forall _, intro σ,
  apply forall_imp_forall _, intro hp₀,
  apply forall_imp_forall _, intro hp₁,
  apply forall_imp_forall _, intro,
  intros h₀ h₁, apply h₀,
  apply Hside _ h₁,
end

lemma bind_framing_left (p₁ : hprop)
  (H₀ : sat P { pre := p₀, post := r })
  (H₂ : p = p₀ :*: p₁)
  (H₁ : ∀ x, sat (P' x) { pre := r x :*: p₁, post := r' } )
: sat (P >>= P') { pre := p, post := r' } :=
begin
  apply precondition _ _ H₂.symm,
  apply bind_spec (λ x, r x :*: p₁),
  { apply framing_right _ H₀, },
  apply H₁,
end

lemma bind_framing_right (p₀ : hprop)
  (H₀ : sat P { pre := p₁, post := r })
  (H₂ : p = p₀ :*: p₁)
  (H₁ : ∀ x, sat (P' x) { pre := p₀ :*: r x, post := r' } )
: sat (P >>= P') { pre := p, post := r' } :=
begin
  simp [s_and_comm p₀ _] at H₁,
  apply bind_framing_left p₀ H₀ _ H₁,
  rw H₂, ac_refl
end

lemma s_exists_intro_pre {α : Type u} {P : program β} {r : α → hprop}
  (H : ∀ x, sat P { pre := r x, post := r' })
: sat P { pre := (∃∃ x, r x), post := r' } :=
begin
  intros _ _ _ H₀ H₁,
  cases H₁ with x H₁,
  apply H x _ _ _ H₀ H₁,
end

lemma s_exists_elim_pre {α : Type u} {P : program β} {r : α → hprop} (x : α)
  (H : sat P { pre := (∃∃ x, r x), post := r' })
: sat P { pre := r x, post := r' } :=
begin
  intros _ _ _ H₀ H₁,
  apply H _ _ _ H₀ ⟨_,H₁⟩,
end

lemma s_exists_replace_pre {t : Type w} {α : Type w'} {r : α → hprop} {P : program β}
  (f : t → α) (g : α → t) (I : left_inverse f g)
  (H : sat P { pre := (∃∃ x, r (f x)), post := r' })
: sat P { pre := (∃∃ x, r x), post := r' } :=
begin
  apply s_exists_intro_pre,
  intro x,
  rw ← I x,
  apply s_exists_elim_pre (g x) H
end

lemma s_exists_intro_post {P : program β} {b : α → β → hprop} (x : α)
  (H : sat P { pre := p, post := b x })
: sat P { pre := p, post := λ r, ∃∃ x, b x r } :=
begin
  intros _ _ _ H₀ H₁,
  specialize H _ _ _ H₀ H₁,
  revert H,
  intros_mono y hp hp' _ _,
  apply Exists.intro x
end

lemma adapt_spec
  (h : sat P { pre := p₁, post := r₁ })
  (Hpre : p = p₁)
  (Hpost : ∀ x, r x = r₁ x)
: sat P { pre := p, post := λ x, r x } :=
by simp [Hpre,Hpost,h]

lemma adapt_spec'
  (h : sat P { pre := p₁, post := r₁ })
  (Hpre : p =*> p₁)
  (Hpost : ∀ x, r x = r₁ x)
: sat P { pre := p, post := λ x, r x } :=
begin
  apply precondition' _ _ Hpre,
  apply postcondition r₁ h,
  intro, symmetry, apply Hpost
end

lemma framing_spec'  (q : hprop)
  (h : sat P { pre := p₁, post := r₁ })
  (Hpre : p =*> p₁ :*: q)
  (Hpost : ∀ x, r₁ x :*: q =*> r x)
: sat P { pre := p, post := λ x, r x } :=
begin
  apply precondition' _ _ Hpre,
  apply postcondition' _ _ Hpost,
  apply framing_right _ h,
end

lemma framing_spec  (q : hprop)
  (h : sat P { pre := p₁, post := r₁ })
  (Hpre : p = p₁ :*: q)
  (Hpost : ∀ x, r x = r₁ x :*: q)
: sat P { pre := p, post := λ x, r x } :=
begin
  simp [Hpre,Hpost],
  apply framing_right _ h
end

lemma context_left (p : Prop)
 (H : p → sat P { pre := q, post := r })
: sat P { pre := [| p |] :*: q, post := r } :=
begin
  intros _ _ _ H₀ H₁,
  simp at H₁,
  apply H H₁.1 _ _ _ H₀ H₁.2,
end

lemma context_right (p : Prop)
 (H : p → sat P { pre := q, post := r })
: sat P { pre := q :*: [| p |], post := r } :=
begin
  rw s_and_comm,
  apply context_left _ H
end

lemma return.spec {α : Type} (x : α) (p : α → hprop)
: sat (return x) { pre := p x, post := λ y, p y } :=
begin
  intros _ _ _ H₀ H₁,
  existsi [x,σ,hp₀,nonterm.pure_yields _,H₀],
  assumption
end

lemma return.spec' {α : Type} (x : α) (p : hprop)
: sat (return x) { pre := p, post := λ _, p } :=
return.spec _ _

lemma read.spec (p : pointer) (v : word)
: sat (read p) { pre := p ↦ v
               , post := λ r, [| r = v |] :*: p ↦ v } :=
begin
  intros _ _ _ H₀ H₁,
  existsi [v,σ,hp₀],
  simp at *,
  split,
  { assumption },
  { simp [read,state_t.read,has_bind.bind,state_t_bind],
    existsi H₀,
    apply nonterm.yields_bind,
    apply nonterm.pure_yields,
    simp [points_to] at H₁,
    simp [state_t_bind._match_1,state_t.lift],
    simp [H₁] at H₀,
    rw [← opt_apl_some (σ.heap) p,H₀,opt_apl_part__maplet],
    simp [monad.pure_bind],
    apply nonterm.pure_yields,
    apply disjoint_of_is_some_part_,
    apply is_some_of_eq_some σ.heap H₀, },
end

lemma read_head.spec (p : pointer) (v : word) (vs : list word)
: sat (read p) { pre := p ↦* v :: vs
               , post := λ r, [| r = v |] :*: p ↦* v :: vs } :=
begin
  simp [points_to_multiple,s_and_assoc],
  apply framing_spec (p + 1 ↦* vs) (read.spec p v),
  { ac_refl },
  intro, ac_refl,
end

lemma read_nth.spec (p : pointer) (i : ℕ) (vs : list word)
  (H : i < vs.length)
: sat (read_nth p i _ H)
      { pre := p ↦* vs,
        post := λ r, [| r = nth_le vs i H |] :*: p ↦* vs } :=
begin
  revert p i,
  induction vs with x xs ; introv,
  { cases not_lt_zero _ H },
  cases i with i,
  { simp [read_nth,points_to_multiple],
    apply framing_spec (p+1 ↦* xs),
    apply read.spec _ x, refl,
    intros r,
    rw [← s_and_assoc], },
  { simp [read_nth,points_to_multiple],
    rw [add_succ,← succ_add],
    apply framing_spec (p ↦ x),
    { specialize ih_1 (p+1) i (lt_of_succ_lt_succ H),
      simp [add_one,read_nth] at ih_1,
      rw [add_comm] at ih_1, apply ih_1 },
    { rw s_and_comm },
    intro r, rw [s_and_comm  (p ↦ x), ← s_and_assoc],
    congr, }
end

lemma write.spec (p : pointer) (v v' : word)
: sat (write p v') { pre := p ↦ v, post := λ r, p ↦ v' } :=
begin
  intros _ _ _ H₀ H₁,
  unfold write,
  existsi (),
  split, existsi (hp₀.insert p v'),
  simp [state_t.read_bind],
  split,
  { change _ = _ at H₁,
    change _ = _, rw H₁,
    funext x,
    by_cases p = x with h ;
    simp [heap.insert,maplet,h], },
  rw [and_comm], split,
  { rw [dif_pos,state_t.write],
    apply nonterm.pure_yields,
    simp [points_to] at H₁,
    rw [← opt_apl_some σ.heap,H₀,H₁,opt_apl_part__maplet ],
    exact rfl,
    subst hp₀,
    apply disjoint_of_part__eq_some H₀ },
  { have H := disjoint_of_part__eq_some H₀,
    rw [← some_part',part'_insert _ _ _ _ _ H],
    rw ← some_part' _ _ H at H₀, injection H₀,
    simp, rw [h_1],
    { change _ = _ at H₁, subst hp₀,
      rw maplet_insert_disjoint_iff,
      assumption }, }
end

def replace {α} (f : α → α) : ℕ → list α → list α
  | i [] := []
  | 0 (x :: xs) := f x :: xs
  | (succ i) (x :: xs) := x :: replace i xs

lemma write_head.spec (p : pointer) (v v' : word) (vs : list word)
: sat (write p v') { pre := p ↦* v :: vs, post := λ _, p ↦* v' :: vs } :=
begin
  simp [(↦*)],
  apply framing_right,
  apply write.spec,
end

lemma write_nth.spec (p : pointer) (v' : word) (i : ℕ) (vs : list word)
  (H : i < vs.length)
: sat (write_nth p i _ v' H)
   { pre := p ↦* vs
   , post := λ _, p ↦* replace (const _ v') i vs } :=
begin
  revert p i,
  induction vs with v vs ; intros p i H,
  { cases not_lt_zero _ H },
  cases i with i,
  { simp [write_nth],
    apply write_head.spec },
  { simp [write_nth,add_succ,replace,(↦*)],
    rw ← succ_add,
    apply framing_left,
    apply ih_1,
    apply lt_of_succ_lt_succ H, }
end

lemma modify.spec (p : pointer) (f : word → word) (v : word)
: sat (modify p f) { pre := p ↦ v, post := λ _, p ↦ f v } :=
begin
  unfold modify,
  apply bind_spec _ (read.spec p v),
  intro x, simp [function.comp],
  apply context_left,
  intro, subst x,
  apply write.spec
end

lemma modify_head.spec (p : pointer) (f : word → word) (v : word) (vs : list word)
: sat (modify p f) { pre := p ↦* v :: vs, post := λ _, p ↦* f v :: vs } :=
begin
  unfold points_to_multiple,
  apply framing_right,
  apply modify.spec,
end

lemma modify_nth.spec (p : pointer) (f : word → word) (i : ℕ) (vs : list word)
  (H : i < vs.length)
: sat (modify (p+i) f) { pre := p ↦* vs, post := λ _, p ↦* replace f i vs } :=
begin
  revert i p,
  induction vs with v vs
  ; intros i p H,
  { cases nat.not_lt_zero _ H, },
  cases i,
  case zero
  { simp [replace],
    apply modify_head.spec },
  case succ i
  { simp [replace,points_to_multiple],
    apply framing_left,
    rw [add_succ,add_succ,← succ_add,add_zero],
    apply ih_1 i (succ p),
    apply lt_of_succ_lt_succ H, }
end

lemma alloc.spec (vs : list word)
: sat (alloc vs) { pre := emp, post := λ r, [| r ≠ 0 |] :*: r ↦* vs } :=
sorry

lemma alloc1.spec (v : word)
: sat (alloc1 v) { pre := emp, post := λ r, [| r ≠ 0 |] :*: r ↦ v } :=
begin
  have h := alloc.spec [v],
  unfold points_to_multiple at h,
  simp [s_and_emp] at h,
  apply h
end

lemma free.spec (p : pointer) (n : ℕ) (vs : list word)
  (h : n = length vs)
: sat (free p n) { pre := p ↦* vs, post := λ r, emp } :=
begin
  unfold sat,
  introv H₀ H₁,
  existsi [()],
  split, existsi heap.emp,
  simp [free,state_t.read,state_t.write],
  rw and_comm,
  split, simp [(>>=)],
  simp [state_t_bind,monad.pure_bind],
  apply nonterm.pure_yields,
  simp, subst n,
  admit
end

lemma free1.spec (p : pointer) (v : word)
: sat (free1 p) { pre := p ↦ v, post := λ r, emp } :=
begin
  have h := free.spec p 1 [v] rfl,
  simp [points_to_multiple] at h,
  apply h,
end

lemma copy.spec (p q : pointer) (v₀ v₁ : word)
: sat (copy p q) { pre := p ↦ v₀ :*: q ↦ v₁
                 , post := λ _, p ↦ v₁ :*: q ↦ v₁ } :=
begin
  apply bind_spec (λ r, p ↦ v₀ :*: ([| r = v₁ |] :*: q ↦ v₁)),
  { apply framing_left, apply read.spec },
  { intro r, simp,
    apply precondition (p ↦ v₀ :*: q ↦ v₁ :*: [| r = v₁ |]),
    { apply context_right, intro, subst r,
      apply framing_right,
      apply write.spec },
    { ac_refl } }
end

end

end separation
