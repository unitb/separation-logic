import data.bitvec
import data.dlist
import util.logic
import util.control.applicative
import util.control.monad.non_termination
import separation.heap
import separation.program

universes u v w w'

open nat list function

namespace separation

structure hprop :=
  (apply : heap → Prop)

def embed (p : Prop) : hprop :=
⟨ λ h, p ∧ h = heap.emp ⟩

notation `[| `p` |]` := embed p

def s_and (p q : hprop) : hprop :=
⟨ λ h, ∃ h₀ h₁ d, h = part' h₀ h₁ d ∧ p.apply h₀ ∧ q.apply h₁ ⟩

infix ` :*: `:55 := s_and

def emp : hprop :=
⟨ λ h, h = heap.emp ⟩

@[simp]
lemma s_and_emp (p : hprop)
: p :*: emp = p :=
sorry

@[simp]
lemma emp_s_and (p : hprop)
: emp :*: p = p :=
sorry

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
∀ (σ : hstate) h₀ h₁,
   some σ.heap = part h₀ h₁ →
   s.pre.apply h₀ →
(∃ r σ' h', p σ ~> (r, σ') ∧
            some σ'.heap = part h₁ h' ∧
            (s.post r).apply h')

lemma s_and_part {h₀ h₁ : heap} {p₀ p₁ : hprop}
  (h : h₀ ## h₁)
  (Hp₀ : p₀.apply h₀)
  (Hp₁ : p₁.apply h₁)
: (p₀ :*: p₁).apply (part' h₀ h₁ h) :=
sorry

lemma embed_eq_emp {p : Prop}
  (hp : p)
: [| p |] = emp :=
by simp [embed,emp,eq_true_intro hp]

def hexists {α : Type u} (p : α → hprop) : hprop :=
⟨ λ ptr, ∃ i, (p i).apply ptr ⟩

notation `∃∃` binders `, ` r:(scoped P, hexists P) := r

def h_imp (p q : hprop) : Prop :=
∀ h, p.apply h → q.apply h

infix ` =*> `:41 := h_imp

lemma s_and_comm (p q : hprop)
: p :*: q = q :*: p := sorry

lemma s_and_assoc (p q r : hprop)
: (p :*: q) :*: r = p :*: (q :*: r) := sorry

instance : is_associative hprop s_and := ⟨ s_and_assoc ⟩
instance : is_commutative hprop s_and := ⟨ s_and_comm ⟩

lemma embed_s_and_embed (p q : Prop)
: [| p |] :*: [| q |] = [| p ∧ q |] :=
begin
  unfold embed emp s_and, apply congr_arg,
  apply funext, intro, simp [-and_comm],
  apply iff.to_eq,
  simp [heap_emp_disjoint],
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
sorry

lemma s_exists_elim  {α : Type u}
  {p : α → hprop} {q : hprop} (x : α)
  (h : ∀ x, p x =*> q)
: (∃∃ x, p x) =*> q :=
sorry

lemma s_imp_of_eq {p q : hprop}
  (h : p = q)
: p =*> q :=
sorry

lemma s_exists_s_and_distr {α : Type u}
  (p : α → hprop) (q : hprop)
: (∃∃ x, p x) :*: q = (∃∃ x, p x :*: q) :=
sorry

lemma s_and_s_exists_distr {α : Type u}
  (p : α → hprop) (q : hprop)
: q :*: (∃∃ x, p x) = (∃∃ x, q :*: p x) :=
sorry

@[congr]
lemma s_exists_congr {α : Type u}
  {p q : α → hprop}
  (h : ∀ x, p x = q x)
: hexists p = hexists q :=
sorry

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
  cases Hpre with h₂ Hpre, cases Hpre with h₃ Hpre,
  cases Hpre with d Hpre,
  rw Hpre.left at Hpart,
  cases Hpre with Hpre₀ Hpre₁, cases Hpre₁ with Hpre₁ Hpre₂,
  have Hdisj := disjoint_disjoint d (disjoint_of_part Hpart),
  have h' := h σ h₂ (part' h₁ h₃ Hdisj) _ Hpre₁, unfold spec.pre spec.post at h',
  { rw part_comm at Hpart,
    cases h' with x h', cases h' with σ' h', cases h' with h' h''',
    existsi x, existsi σ',
    have Hdisj' : h' ## h₃, admit,
    cases h''' with hP Ph₁, cases Ph₁ with Ph₁ Ph₂,
    existsi part' h' h₃ Hdisj',
    split, assumption,
    split,
    { rw [part'_part_assoc _ _,part_comm' (disjoint_symm Hdisj')] at Ph₁,
      apply Ph₁ },
    { apply s_and_part _ Ph₂ Hpre₂, } },
  { rw [part'_part_assoc _ (disjoint_symm Hdisj),part_comm'] at Hpart,
    apply Hpart, },
end

lemma framing_left (q : hprop)
  (h : sat P { pre := p, post := r })
: sat P { pre := q :*: p, post := λ x, q :*: r x } :=
sorry

lemma bind_spec (r : α → hprop)
  (h  : sat P { pre := p, post := r })
  (h' : ∀ x, sat (P' x) { pre := r x, post := r' })
: sat (P >>= P') { pre := p, post := r' } :=
sorry

lemma postcondition (r : α → hprop)
 (Hspec : sat P { pre := p, post := r })
 (Hside : ∀ x, r x = r₁ x)
: sat P { pre := p, post := r₁ } :=
sorry

lemma precondition (p : hprop)
 (Hspec : sat P { pre := p, post := r })
 (Hside : p = q)
: sat P { pre := q, post := r } :=
by { subst q, apply Hspec }

lemma precondition' (p : hprop)
 (Hspec : sat P { pre := p, post := r })
 (Hside : q =*> p)
: sat P { pre := q, post := r } :=
sorry

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
sorry

lemma s_exists_elim_pre {α : Type u} {P : program β} {r : α → hprop} (x : α)
  (H : sat P { pre := (∃∃ x, r x), post := r' })
: sat P { pre := r x, post := r' } :=
sorry

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
sorry

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
sorry

lemma framing_spec  (q : hprop)
  (h : sat P { pre := p₁, post := r₁ })
  (Hpre : p = p₁ :*: q)
  (Hpost : ∀ x, r x = r₁ x :*: q)
: sat P { pre := p, post := λ x, r x } :=
begin
  simp [Hpre,Hpost],
  apply framing_right _ h
end

lemma framing_spec'  (q : hprop)
  (h : sat P { pre := p₁, post := r₁ })
  (Hpre : p =*> p₁ :*: q)
  (Hpost : ∀ x, r₁ x :*: q =*> r x)
: sat P { pre := p, post := λ x, r x } :=
sorry

lemma context_left (p : Prop)
 (H : p → sat P { pre := q, post := r })
: sat P { pre := [| p |] :*: q, post := r } := sorry

lemma context_right (p : Prop)
 (H : p → sat P { pre := q, post := r })
: sat P { pre := q :*: [| p |], post := r } := sorry

lemma option.get_eq_of_is_some {x : option α}
  (h : option.is_some x)
: x = some (option.get h) :=
sorry

lemma return.spec' {α : Type} (x : α) (p : hprop)
: sat (return x) { pre := p, post := λ _, p } :=
sorry

lemma return.spec {α : Type} (x : α) (p : α → hprop)
: sat (return x) { pre := p x, post := λ y, p y } :=
sorry

lemma read.spec (p : pointer) (v : word)
: sat (read p) { pre := p ↦ v, post := λ r, [| r = v |] :*: p ↦ v } :=
sorry

lemma read_head.spec (p : pointer) (v : word) (vs : list word)
: sat (read p) { pre := p ↦* v :: vs, post := λ r, [| r = v |] :*: p ↦* v :: vs } :=
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
sorry

lemma write.spec (p : pointer) (v v' : word)
: sat (write p v') { pre := p ↦ v, post := λ r, p ↦ v' } :=
sorry

def replace {α} (f : α → α) : ℕ → list α → list α
  | i [] := []
  | 0 (x :: xs) := f x :: xs
  | (succ i) (x :: xs) := x :: replace i xs

lemma write_head.spec (p : pointer) (v v' : word) (vs : list word)
: sat (write p v') { pre := p ↦* v :: vs, post := λ _, p ↦* v' :: vs } :=
sorry

lemma write_nth.spec (p : pointer) (v' : word) (i : ℕ) (vs : list word)
  (H : i < vs.length)
: sat (write_nth p i _ v' H)
   { pre := p ↦* vs
   , post := λ _, p ↦* replace (const _ v') i vs } :=
sorry

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
sorry

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
