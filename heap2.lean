import separation.heap

universes u

section classical

local attribute [instance] classical.prop_decidable

noncomputable def part_  : option heap → option heap → option heap
| (some hp₀) (some hp₁) :=
if h : hp₀ ## hp₁
then some $ part' hp₀ hp₁
else none
| _ _ := none

end classical

@[simp]
lemma some_part'
  (hp₀ hp₁ : heap)
  (h : hp₀ ## hp₁)
: some (part' hp₀ hp₁) = part_ (some hp₀) (some hp₁) :=
by { simp [part_,bind,option.bind,dif_pos, h], }

@[simp]
lemma heap_emp_part_
  (hp : heap)
: part_ (some heap.emp) (some hp) = some hp :=
sorry

@[simp]
lemma part__heap_emp
  (hp : heap)
: part_ (some hp) (some heap.emp) = some hp :=
sorry

lemma part__assoc
  (a b c : option heap)
: part_ (part_ a b) c = part_ a (part_ b c) :=
sorry

lemma part__comm
  (a b : option heap)
: part_ a b = part_ b a :=
sorry

instance : is_associative (option heap) part_ :=
⟨ part__assoc ⟩
instance : is_commutative (option heap) part_ :=
⟨ part__comm ⟩

lemma disjoint_of_is_some_part_
  {hp₀ hp₁ : heap}
  (h : (part_ (some hp₀) (some hp₁)).is_some)
: hp₀ ## hp₁ :=
sorry

lemma disjoint_of_part__eq_some
  {hp₀ hp₁ hp₂ : heap}
  (h : some hp₂ = (part_ (some hp₀) (some hp₁)))
: hp₀ ## hp₁ :=
sorry

lemma eq_part'_of_some_eq_part_
  (hp₀ hp₁ hp : heap)
  (h : some hp = part_ (some hp₀) (some hp₁))
: hp = part' hp₀ hp₁ (disjoint_of_part__eq_some h) :=
by { apply @option.no_confusion _ _ (some hp) (some _) _ id,
     simp [h], }

lemma is_some_of_is_some_part__right
  (hp₀ : option heap) {hp₁ : option heap}
  (h : (part_ hp₀ hp₁).is_some)
: hp₁.is_some :=
sorry

lemma is_some_of_is_some_part__left
  {hp₀ : option heap} (hp₁ : option heap)
  (h : (part_ hp₀ hp₁).is_some)
: hp₀.is_some :=
sorry

@[simp]
lemma some_eq_some_iff (x y : heap)
: some x = some y ↔ x = y :=
sorry

def opt_apl : option heap → pointer → option word
 | (some hp) p := hp p
 | none _ := none

lemma opt_apl_some (hp : heap) (p : pointer)
: opt_apl (some hp) p = hp p :=
rfl

lemma opt_apl_part__maplet (hp : heap) (p : pointer) (v : word)
  (h : maplet p v ## hp)
: (opt_apl (part_ (some (maplet p v)) (some hp)) p) = some v :=
begin
  unfold part_,
  rw [dif_pos] ; [ skip , apply h ],
  rw [opt_apl,part',maplet,if_pos rfl],
  refl,
end

@[simp]
lemma eq_emp_of_part_ (a : heap) (hp : option heap)
: some a = part_ (some a) hp ↔ hp = some heap.emp :=
sorry

@[simp]
lemma part'_eq_emp (a b : option heap)
: part_ a b = some heap.emp ↔ a = some heap.emp ∧ b = some heap.emp :=
sorry

def heap.le (hp₀ hp₁ : heap) : Prop :=
∃ hp, some hp₁ = part_ (some hp₀) hp

instance : has_le heap :=
⟨ heap.le ⟩

instance : partial_order heap :=
{ le := heap.le
, le_refl := by { intro x, existsi (some heap.emp), simp, }
, le_trans := by { introv,
                   simp [has_le.le,heap.le],
                   intros hp₀ h₀ hp₁ h₁,
                   -- have : hp₀ ## hp₁, admit,
                   existsi part_ hp₀ hp₁,
                   simp [h₁,h₀], ac_refl }
, le_antisymm := by { introv,
                      simp [has_le.le,heap.le],
                      intros hp₀ h₀ hp₁ h₁,
                      simp [h₀,part__assoc] at h₁,
                      simp [h₁.left] at h₀,
                      subst b, }
}

lemma part'_delete_maplet (p : pointer) (v : word) (hp : heap)
  (h : heap.delete p 1 hp ## maplet p v)
  (h' : maplet p v ≤ hp)
: part' (heap.delete p 1 hp) (maplet p v) = hp :=
begin
  funext p',
  by_cases (p = p') with h,
  { simp [part', heap.delete, maplet, if_pos, h],
    unfold has_le.le heap.le at h',
    cases h' with hp' h', cases hp' with hp',
    { contradiction },
    have h₂ := eq_part'_of_some_eq_part_ _ _ _ h',
    rw [h₂,part',maplet,if_pos h],
    simp },
  { simp [part', heap.delete, maplet, if_neg, h] }
end
