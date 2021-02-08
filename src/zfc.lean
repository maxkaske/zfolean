import fol
import data.set

open fol

namespace zfc
universe variable u

local infix ` >> ` := insert

inductive pred_symb : ℕ → Type u
| elem : pred_symb 2

inductive func_symb : ℕ → Type u

def L : language := { functions := func_symb , predicates := pred_symb }

-- single predicate for membership
@[simp] def memb (t₁ t₂: term L): formula L := papp (papp (pred pred_symb.elem) t₁) t₂
infix ` ∈' `:100 := memb

-- predicates in our meta language
def subset (x y : term L) : (formula L) := ∀' ((#0 ∈' (x ↑ 1 ＠  0)) →' (#0 ∈' (y ↑ 1 ＠  0)))
infix ` '⊆ `:100 := subset

def is_successor_of( x y: term L ) : formula L 
  := ∀'( (#0 ∈' (x ↑ 1 ＠ 0 )) ↔' ((#0 ∈' (y ↑ 1 ＠  0)  ∨' (#0 =' (y ↑ 1 ＠  0) ))))
infix ` is_successor_of' `:100 := is_successor_of

def is_empty (x : term L) : formula L := ∀' ( (#0 ∈' x ↑₀ 1 ) ↔' ¬'(#0 =' #0) )
postfix ` is_empty'`:100 := is_empty 

def is_inductive  (x : term L) : formula L := (∀' (#0 is_empty' →' (#0 ∈' (x ↑₀ 1))))      
  ∧' ( ∀'(#0 ∈' (x ↑₀ 1) →' (∀' (( #0 is_successor_of' #1) →' (#0 ∈' (x ↑₀ 2))))))
postfix ` is_inductive'`:100 := is_inductive 

@[simp] def unique_in_var0 (φ: formula L) : formula L 
  :=  ∀' ∀' (  (φ  ↑ 1 ＠ 1 ) ∧' ( φ ↑ 1 ＠ 0 ) →' (#0 =' #1) )

@[simp] def unique_ex (φ : formula L) : formula L 
  := (∃'φ) ∧' (unique_in_var0 φ)
prefix `∃!`:110 := unique_ex 

-- some notation for the pretty printer to make debugging easier
-- before
#check  #1 ∈' #2                        -- #1 ∈' #2 : formula L
#reduce #1 ∈' #2                        -- ((pred pred_symb.elem).papp #1).papp #2
#reduce (#0 ∈' #2 ∧' #1 ∈' #2) ↑ 1 ＠ 1 -- ((pred pred_symb.elem).papp #0).papp #3 ∧' ((pred pred_symb.elem).papp #2).papp #3
notation s ` '∈ `:100 t := papp (papp (pred pred_symb.elem) s) t
-- after
#check  #1 ∈' #2                        -- #1 ∈' #2 : formula L
#reduce #1 ∈' #2                        -- #1 ∈ #2
#reduce (#0 ∈' #2 ∧' #1 ∈' #2) ↑ 1 ＠ 1 -- (#0 ∈ #3) ∧' #2 ∈ #3
-- much better

-- all things axiom scheme of separation
namespace separation

@[simp] def formula (φ : formula L): formula L 
  := ∀' ∃' ∀' ((#0 ∈' #1)  ↔' (#0 ∈' #2 ∧' (φ  ↑ 1 ＠  1)))

lemma closed{k} {φ} (H: closed (k+2) φ) : closed k (formula φ)  :=
begin
  have h₁: ¬ k + 3 ≤ 2, by linarith,
  have h₂: 1 ≤ k+2, by linarith,
  have h₃:  φ ↑  1 ＠  1 ↑ 1  ＠ (k + 3) = φ ↑ 1 ＠ 1,
    begin  rw ←(lift_lift φ 1 1 h₂), congr, exact H, end,
  simp[h₁, h₃, memb, fol.iff],
end

@[simp] def sentence (φ  : fol.formula L) {k : ℕ} (H: fol.formula.closed (k+2) φ) : fol.formula L 
    := alls k (formula φ)

lemma is_sentence {k : ℕ} (φ  : fol.formula L) (H: fol.formula.closed (k+2) φ) :
  (sentence φ H) is_sentence' := begin exact closure_is_sentence (closed H) end

lemma mem {Γ:set $ fol.formula L} (φ) (k) (φ_h: formula.closed (k+2) φ) 
  {ψ} (h : ψ = sentence φ φ_h) (H: (sentence φ φ_h) ∈ Γ) : ψ ∈ Γ :=
begin subst h, exact H, end 

lemma lift_sentence (φ) (k) (φ_h: fol.formula.closed (k+2) φ) (m i) 
  : (sentence φ φ_h) ↑ m ＠  i = sentence φ φ_h := lift_sentence_id (is_sentence _ _)

def scheme : set $ fol.formula L := 
  { (sentence φ φ_h) |  (φ : fol.formula L) (k: ℕ) (φ_h : formula.closed (k+2) φ) } 

lemma mem_scheme (φ : fol.formula L) {k : ℕ} (φ_h: fol.formula.closed (k+2) φ)
  : sentence φ φ_h ∈ scheme := begin existsi [φ, k, φ_h], refl end
 
end separation



-- all things axiom scheme of replacement
namespace replacement

@[simp] def formula (φ: formula L) := 
  (∀'( ∀'(#0 ∈' #1 →' ∃!φ) →' ( ∃' ∀' ( #0 ∈' #2 →' (∃' (#0 ∈' #2 ∧' (φ ↑ 1 ＠ 2))))))) 

lemma closed {k} {φ} (H: closed (k+3) φ) : closed k (formula φ) :=
begin
    have : ¬ k+4 ≤ 3, by linarith,
    have : ¬ k+4 ≤ 2, by linarith,
    have : ¬ k+3 ≤ 2, by linarith,
    have h₁ : 0 ≤ k+3, from (k+3).zero_le,
    have h₂ : 1 ≤ k+3, by linarith,
    have h₃ : 2 ≤ k+3, by linarith,
    have H₁ : (φ ↑ 1 ＠ 0) ↑ 1 ＠  (k + 4) = φ  ↑  1 ＠ 0, from
      begin rw ←(lift_lift φ 1 1 h₁), congr, exact H, end,
    have H₂: (φ ↑ 1 ＠ 1) ↑ 1 ＠ (k + 4) = φ ↑ 1 ＠ 1, from
      begin rw ←(lift_lift φ 1 1 h₂), congr, exact H, end,
    have H₃: (φ ↑ 1 ＠ 2) ↑ 1 ＠ (k + 4) = φ ↑ 1 ＠ 2, from
      begin rw ←(lift_lift φ 1 1 h₃), congr, exact H, end,
    rw closed at H, clear h₂,
    simp[*, closed],
end 

def sentence  (φ : fol.formula L) {k : ℕ} (H: formula.closed (k+3) φ) : fol.formula L 
  := alls k (formula φ)

lemma is_sentence  (φ : fol.formula L) {k : ℕ} (H: fol.formula.closed (k+3) φ) :
  (sentence φ H) is_sentence' := begin exact closure_is_sentence (closed H) end

lemma mem {Γ:set $ fol.formula L} {ψ} (φ) {k} (φ_h: formula.closed (k+3) φ) 
  (h : ψ = sentence φ φ_h) (H: (sentence φ φ_h) ∈ Γ) : ψ ∈ Γ :=
begin subst h, exact H end 

def scheme : set $ fol.formula L := 
  { (sentence φ φ_h) |  (φ : fol.formula L) (k: ℕ) (φ_h : fol.formula.closed (k+3) φ) }

lemma mem_scheme (φ : fol.formula L) {k : ℕ} (φ_h: fol.formula.closed (k+3) φ)
  : sentence φ φ_h ∈ scheme := begin existsi [φ, k, φ_h], refl, end

end replacement




-- we need unique existential quantification for replacement, i.e. ∃! φ  = ∃x: φ(x) ∧ ∀x ∀y φ(x) ∧ φ(y) → x = y
-- this requires us to lift the formulas to ensure we don't accidentially bind our dB variables

@[simp] def extensionality : formula L  := ∀' ∀' ( (∀' (#0 ∈' #1 ↔' #0 ∈' #2)) →' (#0 =' #1) )
@[simp] def pair_ax : formula L         := ∀' ∀' ∃' ∀' ( (#0 =' #2) ∨' (#0 =' #3) →' (#0 ∈' #1))
@[simp] def union_ax : formula L           := ∀' ∃' ∀' ( (∃'( #1 ∈' #0 ∧' #0 ∈' #3)) →' (#0 ∈' #1) )
@[simp] def power_ax : formula L        := ∀' ∃' ∀' ((#0 '⊆ #2) →' (#0 ∈' #1))
@[simp] def infinity_ax : formula L := ∃' (#0 is_inductive')
@[simp] def regularity : formula L := ∀' (∃'(#0 ∈' #1) →' (∃' ( (#0 ∈' #1) ∧' ¬' ∃'(#0 ∈' #1 ∧' #0 ∈' #2))))
@[simp] def separation_ax := separation.sentence
@[simp] def replacement_ax := replacement.sentence
@[simp] def axiom_of_choice : formula L :=
  ∀' ( ∀' ∀' ( #0 ∈' #2 ∧' #1 ∈' #2 →' ∃' (#0 ∈' #1) ∧' ( #0 =' #1 ∨'  ∀' ( ¬'( (#0 ∈' #1 ∧' #0 ∈' #2 )))))
      →' ∃' ∀' ( #0 ∈' #2 →' ∃' ( ∀'  (#0 ∈' #2 ∧' #0 ∈' #3 →' #0 =' #1))))

lemma extensionality_mem {Γ: set $ formula L}{φ}(h: φ = extensionality)(H: extensionality ∈ Γ) : φ ∈ Γ :=
begin subst h, exact H end
lemma pair_ax_mem {Γ: set $ formula L} {φ} (h: φ = pair_ax) (H: pair_ax ∈ Γ)  : φ ∈ Γ :=
begin subst h, exact H end
lemma union_ax_mem {Γ: set $ formula L} {φ} (h: φ = union_ax) (H: union_ax ∈ Γ)  : φ ∈ Γ :=
begin subst h, exact H end
lemma power_ax_mem {Γ: set $ formula L} {φ} (H: power_ax ∈ Γ) (h: φ = power_ax) : φ ∈ Γ :=
begin subst h, exact H end
lemma infinity_ax_mem {Γ: set $ formula L} {φ} (h: φ = infinity_ax) (H: infinity_ax ∈ Γ)  : φ ∈ Γ :=
begin subst h, exact H end
lemma regularity_mem {Γ: set $ formula L}{φ}(h: φ = regularity)(H: regularity ∈ Γ) : φ ∈ Γ :=
begin subst h, exact H end
lemma aoc_mem {Γ: set $ formula L}{φ}(h: φ = axiom_of_choice)(H: axiom_of_choice ∈ Γ) : φ ∈ Γ :=
begin subst h, exact H end

-- -- #0 is a chain in x
-- def is_chain (x : term L) : formula L := (#0 '⊆ x ) ∧' ∀' ∀' ( (#0 ∈' #2) ∧' (#1 ∈' #2) →' (#0 '⊆ #1) ∨' (#1 '⊆ #0))
-- -- #0 has an upper bound in x
-- def has_upper_bound (x: term L) : formula L  := ∃' ( #0 ∈' (x ↑  1 ＠ 0 ) ∧' ∀'( #0 ∈' #2 →' #0 '⊆ #1)) 
-- -- #0 has a maximal element
-- def has_maximal : formula L := ∃' ∀'( (#0 ∈' #2) →' (#0 '⊆ #1) →' (#0 =' #1)) 

-- def zorn_lemma : formula L := ∀' (∀' ( (is_chain #1 →' has_upper_bound #1) →' (has_maximal)))

def zfc_ax : set $ formula L := { extensionality, pair_ax, union_ax, power_ax, infinity_ax, regularity, axiom_of_choice} 
                                    ∪ separation.scheme
                                    ∪ replacement.scheme

lemma zfc_ax_set_of_sentences: ∀ x ∈ zfc_ax, (x is_sentence') :=
begin
    intros φ  h,
    repeat{cases h,};
    try {unfold sentence closed, refl, },
    { cases h_h with n hn,
      cases hn with h hh,
      subst hh, apply separation.is_sentence, },
    { cases h_h with n hn,
      cases hn with h hh,
      subst hh, apply replacement.is_sentence, },
end

lemma lift_zfc_ax {m i} : (λ ϕ: formula L, ϕ ↑ m ＠ i) '' zfc_ax = zfc_ax 
  := lift_set_of_sentences_id zfc_ax_set_of_sentences

lemma extensionality_mem_zfc_ax : extensionality ∈ zfc_ax := by simp[-extensionality, zfc_ax]
lemma pair_ax_mem_zfc_ax : pair_ax ∈ zfc_ax := by simp[-pair_ax, zfc_ax]
lemma union_ax_mem_zfc_ax : union_ax ∈ zfc_ax := by simp[-union_ax, zfc_ax]
lemma power_ax_mem_zfc_ax : power_ax ∈ zfc_ax := by simp[-power_ax, zfc_ax]
lemma infinity_ax_mem_zfc_ax : infinity_ax ∈ zfc_ax := by simp[-infinity_ax, zfc_ax]

namespace separation
lemma mem_zfc_ax (φ k) (φ_h: formula.closed (k+2) φ) : sentence φ φ_h ∈ zfc_ax :=
begin simp[-sentence, zfc_ax, mem_scheme], end
end separation

namespace replacement
lemma mem_zfc_ax (φ k) (φ_h: formula.closed (k+3) φ) : sentence φ φ_h ∈ zfc_ax :=
begin simp[-sentence, zfc_ax, mem_scheme], end
end replacement



-- Lemma: There exists a set.
-- ⊢ ∃ x ( x = x )
def let_there_be_light : (∅ : set $ formula L) ⊢ ∃' (#0 =' #0) :=
begin
  apply exI #0,
  apply eqI,
end

-- {pair, separation} ⊢ ∀ a ∀ b ∃ X ∀ x ( x ∈ X ↔ x=b ∨ x = a ) 
def pairset_ex: zfc_ax ⊢ ∀' ∀' ∃' ∀' ( (#0 ∈' #1) ↔' (#0 =' #2) ∨' (#0 =' #3)) :=
begin
  apply allI, -- given a
  apply allI, -- given b
  apply exE ∀'( (#0 =' #2) ∨' (#0 =' #3) →' (#0 ∈' #1)), -- let A be a set containing b and a,
  { -- such a set exists pair pairing: 
    apply allE' _ #0,         -- bind b   --(∃' ∀'( (#0 =' #2) ∧' (#0 =' #4) →' (#0 ∈' #1))) #0,
    apply allE' _ #1,         -- bind a  --( ∀' ∃' ∀'( (#0 =' #2) ∧' (#0 =' #3) →' (#0 ∈' #1))) #1,
    apply hypI,               -- this is a hypothesis
    simp only [lift_zfc_ax],
    apply pair_ax_mem_zfc_ax,
    simp[zfc_ax],
    all_goals { simp } },
  { -- now we can use A and its defining property for further arguments
    -- reminder: sets (in order) a b A
    apply exE (∀'( #0 ∈' #1 ↔' (#0 ∈' #2) ∧' (#0 =' #3 ∨' #0 =' #4))), -- let {b,a} be the set {x | x ∈ A ∧ (x=b ∨ x=a)}
    { -- such a set exists by separation:
      apply allE' _ #0,                                           -- bind A
      apply allE' _ #1,                                           -- bind b
      apply allE' _ #2,                                           -- bind a
      apply hypI,                                                 -- this is a hypothesis
      apply separation.mem (#0 =' #2 ∨' #0 =' #3) 2 (rfl) (rfl),   -- an instance of separation
      -- (more) reasoning on the metalevel
      simp only [lift_zfc_ax],
      right, apply separation.mem_zfc_ax,
      all_goals{ simp[alls] }, refl },
    { -- variables (in order) a b A { x | x ∈ A ∧ (x=b ∨ x=a)}
      apply exI #0, -- put X := {b,a}:= { x | x ∈ A ∧ (x=b ∨ x=a)} , we need to show that it satisfies the defining property
      apply allI,
      -- stack : a b A {b,a} x
      apply andI, 
      { -- ⊢ x ∈ {b,a} → x=b ∨ x=a
        apply impI, -- assume x ∈ {b,a} we want to show x=b ∨ x=a
        apply andE₂ (#0 ∈' #2), -- it suffices to show  x ∈ A ∧ (x=b ∨ x=a)
        apply impE_insert,  -- moreover it suffices to show x ∈ {b,a} →  x ∈ A ∧ (x=b ∨ x=a)
        apply iffE_r,      -- it suffices to show  x ∈ {b,a} ↔ x ∈ A ∧ (x=b ∨ x=a)
        apply allE_var0,   -- bind x
        apply hypI,         -- then this is a hypothesis, namely the defining property of  { x | x ∈ A ∧ (x=b ∨ x=a)
        -- meta
        simp only [set.image_insert_eq], 
        apply set.mem_insert, },
      { -- ⊢ x ∈ {b,a} ← x=b ∨ x=a
        apply impI,             -- assume x=b ∨ x=a, we need to show x ∈ {b,a}
        apply impE (#0 ∈' #2),  -- it suffices to show x ∈ A and x ∈ A → x ∈ {b,a}
        { -- first we show x ∈ A
          apply impE ((#0 =' #3) ∨' (#0 =' #4)), -- it suffices to show x = b ∨ x=a and x = b ∨ x=a → x ∈ A
          { -- we show x = b ∨ x = a
            apply hypI1 },  -- which is true by assumption
          { -- we show  x = b ∨ x = a → x ∈ A
            apply allE_var0, -- if we bind x
            apply hypI,       -- then this is how A was defined
            -- meta
            simp only [set.image_insert_eq],
            right, right, apply set.mem_insert } },
        { -- next we show x ∈ A → x ∈ {b,a}
          apply impI,   -- assume x ∈ A
          apply impE (#0 ∈' #2 ∧' ((#0 =' #3) ∨' (#0 =' #4))), -- then it suffices to show ...
          { -- x ∈ A ∧ x=0 ∨ x=b 
            apply andI, -- we need to show ...
            { -- ⊢ x ∈ A
              apply hypI1 }, -- by assumption
            
            { -- ⊢ x = 0 ∨ x=b
              apply hypI2 } },-- by assumption
          { -- ⊢ x ∈ A ∧ x=0 ∨ x=b → x ∈ {b,a}
            apply iffE_l, -- it suffices to show x ∈ {b,a} ↔ x ∈ A ∧ x=0 ∨ x=b 
            apply allE_var0,  -- binding x
            apply hypI,        -- this how we defined {b,a} in the first place
            -- meta
            simp only [set.image_insert_eq], 
            right, right, apply set.mem_insert } } } } },
end


-- Lemma : There exists an empty set.
-- zfc ⊢ ∃X ∀x ( x ∈ X ↔ ¬ (x = x) ) 
def emptyset_ex : zfc_ax ⊢ ∃' (#0 is_empty'):=
begin
  -- consinder the set { x | x ∈ A ∧ ¬'(#0 =' #0 ) }
  apply exE ∀'(#0 ∈' #1 ↔' #0 ∈' #2 ∧' ¬'(#0 =' #0 )),
  { -- such a set exists by separation
      apply allE_var0,           -- bind A
      apply hypI,                 -- then this is true by separation
      apply separation.mem (¬'(#0 =' #0 )) 0 (rfl) (rfl),
      apply separation.mem_zfc_ax, },
  { -- ⊢ ∃X ∀x ( x ∈ X ↔ ¬ (x = x) ) 
    apply exI #0, -- Put X:={ x | x ∈ A ∧ ¬'(#0 =' #0 ) }
    apply allI,   -- given x
    apply andI,
    { -- ⊢  x ∈ X → ¬ (x = x)
      apply impI,
      apply andE₂ _,
      apply impE_insert,
      apply iffE_r,
      apply allE_var0,
      apply hypI,
      -- meta
      simp only [set.image_insert_eq],
      left, refl },
    { -- ⊢ ¬ (x = x) →  x ∈ X 
      apply impI,
      apply botE,
      apply impE (#0 =' #0),
      apply eqI,
      apply hypI,
      -- meta
      left, refl } },
end

-- Lemma: For all a there exists a set {a}.
-- zfc ⊢ ∀ x ∃X (x ∈ X ↔ x = a) 
def singleton_ex : zfc_ax ⊢ ∀' ∃' ∀' ( #0 ∈' #1 ↔' #0 =' #3) :=
begin
  apply allI, --given a
  apply exE ∀' ( #0 ∈' #1 ↔' #0 =' #3 ∨' #0 =' #3), -- the set {a,a} exists
  { -- show existence 
    apply allE' _ #1,
    apply allE' _ #1,
    rw lift_zfc_ax,
    apply pairset_ex,
    -- meta
    dsimp, refl,
    dsimp, refl },
  { -- ∃ X ∀x (x ∈ X ↔ x= a)
    apply exI #0, -- put X:={a,a}
    apply allI,   -- given x
    apply andI,
    { -- ⊢ x ∈ {a,a} → x = a
      apply impI,
      apply orE (#0 =' #3) (#0 =' #3), -- suffices to show (x = a) ∨ ( x = a)
      { -- ⊢ x = a ∨ x = a
        apply impE_insert,
        apply iffE_r,
        apply allE_var0,
        apply hypI,
        -- meta
        simp only [set.image_insert_eq], 
        left, refl },
      { -- ⊢ x = a
        apply hypI1 },
      { -- ⊢ x = a
        apply hypI1 } },
    { -- ⊢ x = a → x ∈ {a,a}
      apply impI,
      apply impE ((#0 =' #3) ∨' (#0 =' #3)),
      { -- ⊢ x=a ∨ x=a
        apply orI₁,
        apply hypI1 },
      { -- ⊢ x=a ∨ x=a → x ∈ {a,a}
        apply iffE_l,
        apply allE_var0,
        apply hypI,
        -- meta
        simp only [set.image_insert_eq], 
        right, left, refl } } }
end

def extensionality_implies_uniqueness (φ : formula L)
  : {extensionality} ⊢ unique_in_var0 ∀'(#0 ∈' #1 ↔' (φ ↑ 1 ＠ 1)) :=
begin
  apply allI, -- y_1
  apply allI, -- y_0
  apply impI,
  apply impE (∀' (#0 ∈' #1 ↔' #0 ∈' #2)),
  { apply allI, -- x
    -- stack a b y_1 y_0 x
    apply iffI_trans (φ ↑ 2 ＠  1), 
    { apply allE_var0, 
      apply andE₁ _ , 
      apply hypI, 
      -- meta argument
      simp [set.image_insert_eq],
      simp [subst_var0_for_0_lift_by_1, lift_lift_merge φ 1] },
    { apply iffI_symm, 
      apply allE_var0, 
      apply andE₂ _ , 
      apply hypI,
      -- meta argument
      simp [set.image_insert_eq] } },
  { apply allE_var0,
    apply allE' _ #1,
    apply weak1,
    apply hypI, 
    -- meta argument
    simp,
    simp, },
end

def extensionality_implies_uniqueness' {Γ} (φ) {ψ} (h: ψ = ∀'(#0 ∈' #1 ↔' (φ ↑ 1 ＠ 1) ) ) (H: extensionality ∈ Γ)  
  : Γ ⊢ unique_in_var0 ψ :=
begin
  subst h,
  apply weak_singleton extensionality (extensionality_implies_uniqueness φ),
  exact H,
end

def extensionality_implies_uniqueness_alls  (n)  (φ : formula L)
  : {extensionality} ⊢ alls n (unique_in_var0 ∀'(#0 ∈' #1 ↔' (φ ↑ 1 ＠ 1))) :=
begin
  apply allsI,
  apply extensionality_implies_uniqueness' φ (rfl),
  rw set.mem_image,
  use extensionality,
  exact ⟨ set.mem_singleton _ , rfl ⟩,
end

def pairset_unique_ex : zfc_ax ⊢ (∀' ∀' ∃! ∀' ((#0 ∈' #1) ↔' (#0 =' #2) ∨' (#0 =' #3))) := 
begin
  apply allI,
  apply allI,
  simp only [lift_zfc_ax],
  apply andI,
  { apply allE' _ #0,
    apply allE' _ #1,
    exact pairset_ex,
    simp, simp },
  { apply extensionality_implies_uniqueness' (#0 =' #1 ∨' #0 =' #2) (rfl),
    simp[-extensionality, zfc_ax] },
end

def emptyset_unique_ex : zfc_ax ⊢ ∃! (#0 is_empty') := 
begin
  apply andI,
  { exact emptyset_ex, },
  { apply extensionality_implies_uniqueness' (¬'(#0 =' #0)) (rfl),
    simp[-extensionality, zfc_ax] },
end

def singleton_unique_ex : zfc_ax ⊢ ∀' ∃! ∀' ( #0 ∈' #1 ↔' #0 =' #3) :=
begin
  apply allsI 1,
  apply andI,
  { apply allsE' 1,
    exact singleton_ex, },
  { apply extensionality_implies_uniqueness' (#0 =' #2) (rfl),
    simp only [lift_zfc_ax],
    simp[-extensionality, zfc_ax] },
end

def separation_proof_scheme 
  (φ k) (φ_h₁: closed (k+2) φ)         -- given a formula φ(x_1,...,x_{k+1})
  (φ_h₂ : ∃ ϕ : formula L , φ = ϕ ↑ 1 ＠ 1) -- such that the x₂ is not among its free variables
  {Γ} (h : separation_ax φ φ_h₁ ∈ Γ)        -- ...
  (H : Γ ⊢ alls k ∃' ∀'(φ →' (#0 ∈' #1)))
  : Γ ⊢ alls k (∃' ∀'((#0 ∈' #1) ↔' φ)) :=
begin
  apply allsI,
  apply exE ∀'( φ →' (#0 ∈' #1)),
  { apply allsE',
    exact H },
  { apply exE (∀'( (#0 ∈' #1) ↔' ( (#0 ∈' #2) ∧' (φ   ↑ 1 ＠  1) ))),
    { apply weak1, 
      apply allsE' 1,
      apply allsE' k,
      rw [alls,alls],
      apply hypI,
      apply separation.mem φ k φ_h₁ (rfl),
      assumption, },
    { apply exI #0,
      apply allI,
      apply andI,
      { 
        apply impI,
        apply andE₂ (#0 ∈' #2),
        apply impE_insert,
        apply iffE_r,
        apply allE_var0,
        apply hypI,
        -- meta
        rw set.image_insert_eq,
        left,
        cases φ_h₂ with ψ ψ_h,
        subst ψ_h,
        rw [subst_var0_lift_by_1, subst_var0_lift_by_1],
        rw [←lift_lift ψ _ _ (le_refl 1)], 
        refl },
      { apply impI,
        apply impE (#0 ∈' #2),
        { apply impE (φ ↑ 1 ＠ 1),
          {
            apply hypI,
            left,
            cases φ_h₂ with ψ ψ_h,
            subst ψ_h,
            rw [subst_var0_lift_by_1, ←lift_lift ψ _ _ (le_rfl)] },
          {
            apply allE_var0, 
            apply hypI,
            -- meta
            simp only [set.image_insert_eq],
            right, right, left, refl } },
        { apply impI,
          apply impE (#0 ∈' #2 ∧' (φ ↑ 1 ＠ 1)),
          { apply andI, 
            { apply hypI1 },
            { apply hypI,
              right, left,
              cases φ_h₂ with ψ ψ_h,
              subst ψ_h,
              rw [subst_var0_lift_by_1, lift_lift ψ _ _ (le_rfl)] } },
          { apply iffE_l, 
            apply allE_var0, 
            apply hypI,
            --meta
            simp only [set.image_insert_eq], 
            right, right, left,
            simp } } } } }
end

def separation_proof_scheme'  (φ) (k) (φ_h: closed (k+2) (φ ↑ 1 ＠ 1))
  {ψ : formula L} (ψ_h : ψ = alls k ∃' ∀'((#0 ∈' #1) ↔' (φ  ↑ 1 ＠ 1)))
  {Γ} (h : separation.sentence (φ ↑ 1 ＠ 1) φ_h ∈ Γ)
  (H: Γ ⊢ alls k ∃' ∀'( φ  ↑ 1 ＠ 1  →' (#0 ∈' #1))) 
  : Γ ⊢ ψ  :=
begin
  subst ψ_h,
  apply separation_proof_scheme (φ ↑ 1 ＠ 1) k φ_h (by use φ) h H,
end

def union_ex : zfc_ax ⊢ ∀' ∃' ∀' ( (#0 ∈' #1) ↔' ∃'(#1 ∈' #0 ∧' #0 ∈' #3) ):=
begin
  apply separation_proof_scheme' (∃'(#1 ∈' #0 ∧' #0 ∈' #2)) 1,
  { refl, },
  { apply separation.mem_zfc_ax, },
  { apply hypI,
    apply union_ax_mem_zfc_ax },
  { dsimp, refl, },
end

def union_unique_ex : zfc_ax ⊢ ∀' ∃! ∀' ( (#0 ∈' #1) ↔' ∃'(#1 ∈' #0 ∧' #0 ∈' #3) ) := 
begin
  apply allI,
  simp only [lift_zfc_ax],
  apply andI,
  { apply allE' _ #0,
    exact union_ex,
    simp, },
  { apply extensionality_implies_uniqueness' (∃'(#1 ∈' #0 ∧' #0 ∈' #2)) (rfl),
    simp[-extensionality, zfc_ax] },
end

def powerset_ex: zfc_ax ⊢ ∀' ∃' ∀' ((#0 ∈' #1) ↔' ( #0 '⊆ #2)) :=
begin
  apply separation_proof_scheme' (#0 '⊆ #1) 1,
  { refl },
  { apply separation.mem_zfc_ax, },
  { apply hypI,
    apply power_ax_mem_zfc_ax, },
  { dsimp, refl, },
end

def powerset_unique_ex : zfc_ax ⊢ ∀' ∃! ∀' ((#0 ∈' #1) ↔' ( #0 '⊆ #2)) := 
begin
  apply allI,
  simp only [lift_zfc_ax],
  apply andI,
  { apply allE_var0,
    exact powerset_ex, },
  { apply extensionality_implies_uniqueness' (#0 '⊆ #1) (rfl),
    simp[-extensionality, zfc_ax] },
end

def binary_union_ex : zfc_ax ⊢ ∀' ∀' ∃' ∀' (#0 ∈' #1 ↔' #0 ∈' #2 ∨' #0 ∈' #3) :=
begin
  apply separation_proof_scheme' (#0 ∈' #1 ∨' #0 ∈' #2) 2,
  { refl, },
  { apply separation.mem_zfc_ax, },
  { apply allI,
    apply allI,
    apply exE ∀'((#0 ∈' #1) ↔' (#0 =' #2) ∨' (#0 =' #3)),
    { apply allE' _ #0,
      apply allE' _ #1,
      simp only [lift_zfc_ax],
      exact pairset_ex,
      simp, simp },
    { apply exE  ∀'( (#0 ∈' #1) ↔' ∃'(#1 ∈' #0 ∧' #0 ∈' #3)),
      { apply allE' _ #0,
        simp only [lift_zfc_ax],
        apply weak1,
        exact union_ex,
        simp },
      { apply exI #0,
        apply allI,
        apply impI,
        apply orE (#0 ∈' #3)  (#0 ∈' #4),
        { apply hypI1 },
        { -- case : x ∈ b
          apply impE (∃'(#1 ∈' #0 ∧' #0 ∈' #3)),
          { apply exI #3, 
            apply andI,
            { apply hypI1, },
            { apply impE (#3 =' #3 ∨' #3 =' #4),
              { apply orI₁, 
                apply eqI, },
              { apply iffE_l,
                apply allE' _ #3,
                apply hypI,
                simp only [set.image_insert_eq],
                right, right, right, left, refl,
                simp } } },
          { apply iffE_l,
            apply allE_var0,
            apply hypI,
            simp only [set.image_insert_eq],
            right, right, left, refl } },
        { -- case : x ∈ a
          apply impE (∃'(#1 ∈' #0 ∧' #0 ∈' #3)),
          { apply exI #4, 
            apply andI,
            { apply hypI1, },
            { apply impE (#4 =' #3 ∨' #4 =' #4),
              { apply orI₂, 
                apply eqI, },
              { apply iffE_l,
                apply allE' _ #4,
                apply hypI,
                simp only [set.image_insert_eq],
                right, right, right, left, refl,
                simp } } },
          { apply iffE_l,
            apply allE_var0,
            apply hypI,
            simp only [set.image_insert_eq],
            right, right, left, refl } } } } },
  { dsimp, refl, },
end

def binary_union_unique_ex : zfc_ax ⊢ ∀' ∀' ∃! ∀' (#0 ∈' #1 ↔' #0 ∈' #2 ∨' #0 ∈' #3) := 
begin
  apply allsI 2,
  apply andI,
  { apply allsE' 2,
    exact binary_union_ex,},
  { apply extensionality_implies_uniqueness' (#0 ∈' #1 ∨' #0 ∈' #2) (rfl),
    simp only [lift_zfc_ax],
    simp[-extensionality, zfc_ax] }
end

def successor_ex : zfc_ax ⊢ ∀' ∃' (#0 is_successor_of' #1) :=
begin
  apply separation_proof_scheme' (#0 ∈' #1  ∨' (#0 =' #1)) 1,
  { refl, },
  { apply separation.mem_zfc_ax, },
  { apply allI,
    apply exE ∀' (#0 ∈' #1 ↔' #0 =' #2),
    { apply allE' _ #0,
      simp only [lift_zfc_ax],
      exact singleton_ex, 
      dsimp, refl, },
    apply exE ∀'(#0 ∈' #1 ↔' #0 ∈' #3 ∨' #0 ∈' #2),
    { apply allE' _ #1,
      apply allE' _ #0,
      simp only [lift_zfc_ax],
      apply weak1,
      exact binary_union_ex,
      simp, dsimp, refl },
    apply exI #0,
    apply allI,
    apply impI,
    apply orE (#0 ∈' #3) (#0 =' #3),
    { apply hypI1, },
    { -- case x ∈ a
      apply impE (#0 ∈' #3 ∨' #0 ∈' #2),
      { apply orI₁, apply hypI1,},
      { apply iffE_l, 
        apply allE_var0,
        apply hypI,
        simp only [set.image_insert_eq],
        right, right, left, refl } },
    { -- case x = a
      apply impE (#0 ∈' #3 ∨' #0 ∈' #2),
      { apply orI₂, 
        apply impE_insert,
        apply iffE_l,
        apply allE_var0,
        apply hypI,
        simp only [set.image_insert_eq],
        right, right, left, refl },
      { 
        apply iffE_l,
        apply allE_var0,
        apply hypI,
        simp only [set.image_insert_eq],
        right, right, left, refl } } },
  { dsimp, refl, },
end

def successor_unique_ex : zfc_ax ⊢ ∀' ∃! (#0 is_successor_of' #1) := 
begin
  apply allsI 1,
  apply andI,
  { apply allsE' 1,
    exact successor_ex, },
  { apply extensionality_implies_uniqueness' (#0 ∈' #1  ∨' (#0 =' #1)) (rfl),
    simp only [lift_zfc_ax],
    simp[-extensionality, zfc_ax] },
end

def omega_ex : zfc_ax ⊢ ∃' ∀' ( #0 ∈' #1 ↔' ∀' (#0 is_inductive' →' #1 ∈' #0)) :=
begin
  apply separation_proof_scheme' (∀' (#0 is_inductive' →' #1 ∈' #0)) 0,
  { refl, },
  { apply separation.mem_zfc_ax, },
  { apply exE (#0 is_inductive'), -- let x be an inductive set 
  { apply hypI, 
    exact infinity_ax_mem_zfc_ax }, -- this exists because of the axiom of infinity
  { apply exE ∀'(#0 ∈' #1 ↔' #0 ∈' #2  ∧'  ∀' (#0 is_inductive' →' #1 ∈' #0)),
    { apply allE_var0,
      apply hypI,
      simp only [lift_zfc_ax],
      right,
      apply separation.mem_zfc_ax (∀'(#0 is_inductive' →' #1 ∈' #0)) 0,
      dsimp, refl },
    -- stack: #1 := w₀ (infinite/inductive set)
    --        #0 := ω  (elements of #1 contained in all inductive)
    --        ⊢  ∀ x ( x ∈ ω ↔ (∀ w ( w inductive → x ∈ w)))
    { apply exI #0,
      apply allI,
      -- stack: #2 := w₀ (infinite/inductive set)
      --        #1 := ω  (elements of #1 contained in all inductive)
      --        #0 := x
      --        ⊢ (∀ w ( w inductive → x ∈ w))) → x ∈ ω
      apply impI,
      -- new info: (∀ w ( w inductive → x ∈ w)))
      apply iffE₁ (#0 ∈' #2 ∧' ∀' (#0 is_inductive' →' #1 ∈' #0)),
      { apply andI,
        { apply impE (#2 is_inductive'),
        -- ( ( ∀' (#0 is_empty' →' (#0 ∈' #3)) ) ∧'      -- 0 ∈ x
        --                ( ∀'( #0 ∈' #3 →' ( ∀' ( ( #0 is_successor_of' #1) →' (#0 ∈' #4)))))),
          { apply hypI,
            simp only [set.image_insert_eq],
            right, right, left,
            simp[is_inductive, is_empty, is_successor_of] },
          { 
            apply allE' _ #2,
            apply hypI,
            left, refl, dsimp, refl } },
        { apply hypI1, } },
      {
        apply allE_var0,
        apply hypI,
        simp only [set.image_insert_eq],
        right, left, refl } } } },
  { dsimp, refl }
end 

def omega_unique_ex : zfc_ax ⊢ ∃! ∀' ( #0 ∈' #1 ↔' ∀' (#0 is_inductive' →' #1 ∈' #0)) :=
begin
  apply andI,
  { exact omega_ex, },
  { apply extensionality_implies_uniqueness' (∀' (#0 is_inductive' →' #1 ∈' #0)) (rfl),
    simp[-extensionality, zfc_ax] },
end

def omega_subset_all_inductive : 
  zfc_ax ⊢ ∀' (∀' ( #0 ∈' #1 ↔' ∀' (#0 is_inductive' →' #1 ∈' #0)) →' ∀' (#0 is_inductive' →' #1 '⊆ #0) )  :=
begin
  apply allI,
  apply impI,
  apply allI,
  apply impI,
  apply allI,
  apply impI,
  apply impE (#1 is_inductive'),
  { apply hypI, simp only [set.image_insert_eq], right, left, refl},
  { apply allE' _ #1,
    apply iffE₂ ( #0 ∈' #2),
    { apply hypI1, },
    { apply allE_var0,
      apply hypI,
      simp only [set.image_insert_eq], 
      right, right, left, refl },
    { dsimp, refl, } },
end

def omega_inductive :  zfc_ax ⊢ ∀' (∀'( #0 ∈' #1 ↔' ∀' (#0 is_inductive' →' #1 ∈' #0)) →' (#0 is_inductive')) :=
begin
  apply allI,
  apply impI,
  apply andI,
  { apply allI,
    apply impI,
    apply iffE₁ ∀'(#0 is_inductive' →' #1 ∈' #0),
    { apply allI,
      apply impI,
      apply impE (#1 is_empty'),
      { apply hypI, 
        simp only [set.image_insert_eq], 
        right, left, refl, },
      { apply allE' _ #1,
        apply andE₁,
        apply hypI1,
        unfold is_empty, refl } },
    { apply allE_var0,
      apply hypI,
      simp only[set.image_insert_eq],
      right, left, refl } },
  { apply allI,
    apply impI,
    apply allI,
    apply impI,
    -- #2 = ω + def
    -- #1 = x + x ∈ ω
    -- #0 = y + y = S(x)
    apply impE ∀'(#0 is_inductive' →' #1 ∈' #0),
    { apply allI,
      apply impI,
      apply impE (#2 ∈' #0),
      { apply impE (#2 ∈' #3),
        { apply hypI, 
          simp only [set.image_insert_eq], 
          right, right, left, refl },
        { apply allE' (#0 ∈' #4 →' #0 ∈' #1)  #2,
          { apply impE (#0 is_inductive'),
            { apply hypI1  },
            { apply allE_var0,
              { apply impE (∀' ( #0 ∈' #4 ↔' ∀' (#0 is_inductive' →' #1 ∈' #0))),
                { apply hypI,
                  simp only [set.image_insert_eq],
                   right, right, right, left, refl },
                {
                  apply allE' _ #3,
                  { apply weak zfc_ax,
                    { exact omega_subset_all_inductive, },
                    { simp only [set.image_insert_eq, lift_zfc_ax],  
                      assume y yh, simp[yh] } },
                  { unfold is_inductive, refl, } } } } },
          { refl, } } },
      { apply impI,
        apply impE (#1 is_successor_of' #2),
        { apply hypI, 
          simp only [set.image_insert_eq],
          right, right, left, 
          dsimp[is_successor_of], refl },
        { 
          apply allE' _ #1,
          { apply impE (#2 ∈' #0),
            { apply hypI1, },
            { apply allE' _ #2,
              { apply andE₂, apply hypI, 
                simp only[set.image_insert_eq],
                right, left, refl, },
              { unfold is_successor_of, refl } } },
          { unfold is_successor_of, 
            refl } } } },
    {
      apply iffE_l,
      apply allE_var0,
      apply hypI,
      simp only [set.image_insert_eq],
      right, right, left, refl } },
end

#lint
end zfc