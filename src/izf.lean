import fol
import data.set

open fol

namespace izf
universe variable u

local infix ` >> ` := insert

inductive pred_symbols : ℕ → Type u
| elem : pred_symbols 2
--| subset : pred_symbols 2

inductive func_symbols : ℕ → Type u
| empty : func_symbols 0
| omega : func_symbols 0
| union : func_symbols 1
| power : func_symbols 1
| pair  : func_symbols 2
--| succ  : func_symbols 1
 
def L : language := { functions := func_symbols , predicates := pred_symbols }

-- functions
@[simp]def emptyset : term L := (func func_symbols.empty : term L)
@[simp]def omegaset : term L := (func func_symbols.omega : term L)
@[simp]def unionset (t: term L) : term L :=  fapp (func func_symbols.union) t
@[simp]def powerset (t : term L) : term L := fapp (func func_symbols.power) t
@[simp]def pairset (t₁ t₂ : term L) : term L := fapp (fapp (func func_symbols.pair) t₁) t₂
--def successorset (t: term L) : term L :=  fapp (func func_symbols.succ) t

notation `⌀`:= emptyset 
notation `ω` := omegaset
prefix ⋃  := unionset
prefix 𝒫  := powerset
--prefix S:max := successorset
notation ⦃ a ` , ` b ⦄ := pairset a b  
 notation ⦃ a ⦄ := pairset a a

-- #check {' ω , 𝒫⌀ }'

/- 
  still only a single predicate; but for a good reason: 
  as it turns out, making the subset relation part of our meta language
  makes it much more convenient to proof things 
-/
@[simp] def memb (t₁ t₂: term L): formula L := papp (papp (pred pred_symbols.elem) t₁) t₂
infix ` ∈' `:100 := memb

-- def subset (t₁ t₂: term L): formula L := papp (papp (pred_symbols pred_symbols.subset) t₁) t₂
@[simp] def subset (t₁ t₂: term L): formula L := ∀'( #0 ∈' (t₁ ↑ 1 ＠  0) →' #0 ∈' (t₂ ↑ 1 ＠  0))
infix ` ⊆' `:100 := subset

@[simp] def successor_set (t: term L) : term L := ⋃⦃ t , ⦃ t ⦄ ⦄
prefix `S`:max := successor_set

@[simp] def is_inductive (t : term L) 
  := ⌀ ∈' t ∧' ∀' (#0 ∈' (t ↑ 1 ＠  0) →' S #0 ∈' (t ↑ 1 ＠  0))
postfix ` is_inductive`:max := is_inductive

@[simp] def unique_in_var0 (φ: formula L) : formula L 
  :=  ∀' ∀' (  (φ  ↑ 1 ＠ 1 ) ∧' ( φ ↑ 1 ＠ 0 ) →' (#0 =' #1) )

@[simp] def unique_ex (φ : formula L) : formula L 
  := (∃'φ) ∧' (unique_in_var0 φ)
prefix `∃!`:110 := unique_ex 

-- reducing terms helps with evaluating lifts and substituions
-- however, pred_symbols and func_symbols will make more difficult:                        
#reduce (⌀ ∈' ω  ∧' ⦃ ⌀, S⦃ #3 ⦄ ⦄∈' 𝒫#1) ↑ 1 ＠ 1                   
/-
((pred pred_symbols.elem).papp (func func_symbols.empty)).papp (func func_symbols.omega) ∧'
  ((pred pred_symbols.elem).papp
     (((func func_symbols.pair).fapp (func func_symbols.empty)).fapp
        ((func func_symbols.unionset_ax).fapp
           (((func func_symbols.pair).fapp (((func func_symbols.pair).fapp #4).fapp #4)).fapp
              (((func func_symbols.pair).fapp (((func func_symbols.pair).fapp #4).fapp #4)).fapp
                 (((func func_symbols.pair).fapp #4).fapp #4)))))).papp
    ((func func_symbols.power).fapp #2)
-/

-- this seems to makes reduced terms and formulas much easier to read
notation `'⌀` := func func_symbols.empty
notation `'ω` := func func_symbols.omega
notation `'⋃` t :=  fapp (func func_symbols.union) t
notation `'𝒫` t := fapp (func func_symbols.power) t 
--notation `'S` t := fapp (func func_symbols.succ) t
notation `'{ ` a ` , `b` }` := fapp (fapp (func func_symbols.pair) a) b
notation s ` '∈ `:100 t := papp (papp (pred pred_symbols.elem) s) t
notation s ` '⊆ `:100 t := papp (papp (pred pred_symbols.subset) s) t

-- after
#reduce (⌀ ∈' ω  ∧' ⦃ ⌀, S⦃ #3 ⦄ ⦄∈' 𝒫#1) ↑ 1 ＠ 1      
/-
('⌀ '∈ 'ω) ∧' '{ '⌀ , '⋃'{ '{ #4 , #4 } , '{ '{ #4 , #4 } , '{ #4 , #4 } } } } '∈ '𝒫#2
-/
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
  simp[h₁, h₃],
end

@[simp] def sentence (φ  : fol.formula L) {k : ℕ} (H: fol.formula.closed (k+2) φ) : fol.formula L 
    := alls k (formula φ)

lemma is_sentence {k : ℕ} {φ  : fol.formula L} (H: fol.formula.closed (k+2) φ) :
  (sentence φ H) is_sentence' := begin exact closure_is_sentence (closed H) end

lemma mem_of {Γ:set $ fol.formula L} (φ) (k) (φ_h: formula.closed (k+2) φ) 
  {ψ} (h : ψ = sentence φ φ_h) (H: (sentence φ φ_h) ∈ Γ) : ψ ∈ Γ :=
begin subst h, exact H, end 

lemma lift_sentence (φ) (k) (φ_h: fol.formula.closed (k+2) φ) (m i) 
  : (sentence φ φ_h) ↑ m ＠  i = sentence φ φ_h := lift_sentence_id (is_sentence _)

def scheme : set $ fol.formula L := 
  { (sentence φ φ_h) |  (φ : fol.formula L) (k: ℕ) (φ_h : formula.closed (k+2) φ) } 

lemma mem_scheme (φ : fol.formula L) {k : ℕ} (φ_h: fol.formula.closed (k+2) φ)
  : sentence φ φ_h ∈ scheme := begin existsi [φ, k, φ_h], refl end
 
end separation

@[simp] def separation := separation.sentence

-- all things axiom scheme of replacement
namespace replacement

@[simp] def formula (φ: formula L) := 
  (∀'( ∀'(#0 ∈' #1 →' ∃!φ) →' ( ∃' ∀' ( #0 ∈' #2 →' (∃' (#0 ∈' #2 ∧' (φ ↑ 1 ＠ 2))))))) 

lemma closed  {φ} {k} (H: closed (k+3) φ) : closed k (formula φ) :=
begin
    have : ¬ k+4 ≤ 3, by linarith,
    have : ¬ k+4 ≤ 2, by linarith,
    have : ¬ k+3 ≤ 2, by linarith,
    have h₁ : 0 ≤ k+3, from (k+3).zero_le,
    have h₂ : 1 ≤ k+3, by linarith,
    have h₃ : 2 ≤ k+3, by linarith,
    have H₁ : (φ ↑ 1 ＠ 0) ↑ 1 ＠ (k + 4) = φ  ↑  1 ＠ 0, from
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

lemma is_sentence  {φ : fol.formula L} {k : ℕ} (H: fol.formula.closed (k+3) φ) :
  (sentence φ H) is_sentence' := begin exact closure_is_sentence (closed H) end

lemma mem_of {Γ:set $ fol.formula L} {ψ} {k} (φ) (φ_h: formula.closed (k+3) φ) 
  (h : ψ = sentence φ φ_h) (H: (sentence φ φ_h) ∈ Γ) : ψ ∈ Γ :=
begin subst h, exact H end 

def scheme : set $ fol.formula L := 
  { (sentence φ φ_h) |  (φ : fol.formula L) (k: ℕ) (φ_h : fol.formula.closed (k+3) φ) }

lemma mem_scheme (φ : fol.formula L) {k : ℕ} (φ_h: fol.formula.closed (k+3) φ)
  : sentence φ φ_h ∈ scheme := begin existsi [φ, k, φ_h], refl, end

end replacement

@[simp] def replacement := replacement.sentence


-- @[simp] def subset_ax   : formula L := ∀' ∀' ( #0 ⊆' #1  ↔' ∀' (#0 ∈' #1 →' #0 ∈' #2) )
@[simp] def extensionality : formula L := ∀' ∀' ( (∀' (#0 ∈' #1 ↔' #0 ∈' #2)) →' (#0 =' #1) )
@[simp] def emptyset_ax : formula L := ∀' (#0 ∈' ⌀ ↔' ¬'(#0 =' #0) )
@[simp] def pairset_ax  : formula L := ∀' ∀' ∀' ( #0 ∈' ⦃ #1 , #2 ⦄ ↔' (#0 =' #1 ∨' #0 =' #2))
@[simp] def unionset_ax : formula L := ∀' ∀' ( #0 ∈' ⋃#1 ↔' ∃'( #1 ∈' #0 ∧' #0 ∈' #2))
@[simp] def powerset_ax : formula L := ∀' ∀' (#0 ∈' 𝒫#1 ↔' #0 ⊆' #1)
@[simp] def omega_ax    : formula L := ∀' (#0 ∈' ω ↔' ∀'( (#0 is_inductive) →' #1 ∈' #0))
@[simp] def mem_induction  (φ  : formula L){k : ℕ} (H: closed (k+1) φ) : formula L  
  := alls k (∀'(∀'(#0 ∈' #1 →' (φ →' (φ ↑ 1 ＠ 0)))) →' (∀'φ))
@[simp] def separation_ax (φ  : formula L){k : ℕ} (H: closed (k+2) φ) : formula L 
  := separation φ H
@[simp] def replacement_ax {k : ℕ} (φ : formula L) (H: closed (k+3) φ) : formula L 
  := replacement φ H

lemma extensionality_mem {Γ: set $ formula L}{φ}(h: φ = extensionality)(H: extensionality ∈ Γ) : φ ∈ Γ :=
begin subst h, exact H end
lemma emptyset_ax_mem {Γ: set $ formula L} {φ} (h: φ = emptyset_ax) (H: emptyset_ax ∈ Γ)  : φ ∈ Γ :=
begin subst h, exact H end
lemma pairset_ax_mem {Γ: set $ formula L} {φ} (h: φ = pairset_ax) (H: pairset_ax ∈ Γ)  : φ ∈ Γ :=
begin subst h, exact H end
lemma unionset_ax_mem {Γ: set $ formula L} {φ} (h: φ = unionset_ax) (H: unionset_ax ∈ Γ)  : φ ∈ Γ :=
begin subst h, exact H end
lemma powerset_ax_mem {Γ: set $ formula L} {φ} (H: powerset_ax ∈ Γ) (h: φ = powerset_ax) : φ ∈ Γ :=
begin subst h, exact H end
lemma omega_ax_mem {Γ: set $ formula L} {φ} (h: φ = omega_ax) (H: omega_ax ∈ Γ) : φ ∈ Γ :=
begin subst h, exact H end
lemma mem_induction_mem {Γ:set $ fol.formula L} {ψ} (φ k) (φ_h: closed (k+1) φ) 
  ( h : ψ = mem_induction φ φ_h) (H: (mem_induction φ φ_h) ∈ Γ) : ψ ∈ Γ := 
begin subst h, exact H end


def mem_induction_scheme : set $ fol.formula L
  := { (mem_induction φ φ_h) |  (φ : formula L) (k: ℕ) (φ_h : closed (k+1) φ) }

lemma mem_induction_is_sentence  {φ} {k} (φ_h: closed (k+1) φ) 
  : (mem_induction φ φ_h) is_sentence' :=
begin
  apply closure_is_sentence,
  have : φ ↑ 1 ＠ 0 ↑ 1 ＠ (k + 1 + 1) = φ ↑ 1 ＠ 0,
    begin rw ←lift_lift φ, congr, exact φ_h, exact zero_le (k + 1), end,
  have :  φ ↑ 1 ＠ (k + 1 + 1) = φ,
    begin apply trivial_lift_monotone φ_h, exact (k + 1).le_succ, end,
  simp[*], 
  exact φ_h,
end

def izf_ax : set $ formula L := { extensionality, emptyset_ax, pairset_ax, 
                                  unionset_ax, powerset_ax, omega_ax } 
                                  ∪ mem_induction_scheme
                                  ∪ separation.scheme
                                  ∪ replacement.scheme

lemma izf_ax_set_of_sentences : ∀ ϕ ∈ izf_ax , sentence ϕ :=
begin
  intros φ h,
  repeat {cases h,};
  try {unfold sentence closed, refl, },
  all_goals { cases h_h with k H,
              cases H with ϕ_closed,
              subst H_h },
  exact mem_induction_is_sentence ϕ_closed,
  exact separation.is_sentence ϕ_closed,
  exact replacement.is_sentence ϕ_closed,
end

lemma lift_izf_ax {m i : ℕ}: (λ (ϕ: formula L) , ϕ ↑ m ＠ i) '' izf_ax = izf_ax 
  := lift_set_of_sentences_id izf_ax_set_of_sentences


def extensionality_implies_uniqueness (φ : formula L)
  : {extensionality} ⊢ unique_in_var0  ∀'(#0 ∈' #1 ↔' (φ ↑ 1 ＠ 1)) :=
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
      apply separation.mem_of φ k φ_h₁ (rfl),
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

def singleton_def: {pairset_ax} ⊢ ∀' ∀' (#0 ∈' ⦃ #1 ⦄ ↔' #0 =' #1) :=
begin
  apply allI,
  apply allI,
  apply andI,
  { apply impI,
    apply orE (#0 =' #1) (#0 =' #1),
    { apply impE_insert,
      apply andE₁,
      apply allE' _ #0,
      apply allE' _ #1,
      apply allE' _ #1,
      apply hypI,
      apply pairset_ax_mem (rfl),
      all_goals {simp [set.image_singleton] } },
    { apply hypI1, },
    { apply hypI1, },
  },
  { apply impI,
    apply impE (#0 =' #1 ∨' #0 =' #1),
    { apply orI₁, 
      apply hypI1, },
    { apply andE₂, 
      apply allE' _ #0,
      apply allE' _ #1,
      apply allE' _ #1,
      apply hypI,
      apply pairset_ax_mem (rfl),
      all_goals {simp [set.image_singleton] } } }
end

def singleton_def' {Γ} {φ : formula L} (h₁: φ = ∀' ∀' (#0 ∈' ⦃ #1 ⦄ ↔' #0 =' #1)) (h₂ : pairset_ax ∈ Γ ) :
  Γ  ⊢ φ  :=
begin
  subst h₁,
  apply weak_singleton pairset_ax,
  apply singleton_def,
  assumption,
end

def binary_union_def : {pairset_ax, unionset_ax} ⊢ ∀' ∀' ∀' (#0 ∈' ⋃ ⦃ #1, #2 ⦄ ↔' #0 ∈' #1 ∨' #0 ∈' #2) :=
begin
  apply allI,
  apply allI,
  apply allI,
  apply andI,
  { apply impI,
    apply exE (#1 ∈' #0 ∧' #0 ∈' ⦃#2 , #3⦄),
    { apply impE_insert, 
      apply iffE_r, 
      apply allE' _ #0,
      apply allE' _ ⦃#1 , #2⦄,
      apply hypI,
      apply unionset_ax_mem (rfl),
      all_goals { try { simp[set.image_insert_eq], }, },
      split; refl },
    { apply impE (#0 =' #2 ∨' #0 =' #3),
      { apply impE (#0 ∈'  ⦃#2 , #3⦄ ),
        { apply andE₂, 
          apply hypI1 },
        { apply iffE_r ,
          apply allE' _ #0,
          apply allE' _ #2,
          apply allE' _ #3,
          apply hypI,
          apply pairset_ax_mem (rfl),
          all_goals { try { simp[set.image_insert_eq] } },
          split; refl } },
      { apply impI,
        apply orE (#0 =' #2) (#0 =' #3),
        { apply hypI1, },
        { apply orI₁,
          apply eqE' #0 #2 (#2 ∈' #0),
          { apply hypI1, },
          { apply andE₁,
            apply hypI, 
            simp[set.image_insert_eq] },
          { refl } },
        { 
          apply orI₂,
          apply eqE' #0 #3 (#2 ∈' #0),
          { apply hypI1, },
          { apply andE₁,
            apply hypI, 
            simp[set.image_insert_eq] },
          { refl } } } } },
  { apply impI,
    apply orE (#0 ∈' #1)  (#0 ∈' #2),
    { apply hypI1 },
    { -- case : x ∈ a
      apply impE (∃'(#1 ∈' #0 ∧' #0 ∈'  ⦃#2 , #3⦄)),
      { apply exI #1, 
        apply andI,
        { apply hypI1, },
        { apply impE (#1 =' #1 ∨' #1 =' #2),
          { apply orI₁, apply eqI, },
          { apply iffE_l,
            apply allE' _ #1,
            apply allE' _ #1,
            apply allE' _ #2,
            apply hypI,
            apply pairset_ax_mem (rfl),
            all_goals { try { simp[set.image_insert_eq], }, },
            split; refl } } },
      { apply andE₂ _ ,
        apply allE' _ #0,
        apply allE' _ ⦃ #1 , #2 ⦄,
        apply hypI,
        apply unionset_ax_mem (rfl),

        all_goals{ try { simp[set.image_insert_eq],}, },
        split; refl } },
    { -- case : x ∈ b
      apply impE (∃'(#1 ∈' #0 ∧'  #0 ∈'  ⦃#2 , #3⦄)),
      { apply exI #2, 
        apply andI,
        { apply hypI1, },
        { apply impE (#2 =' #1 ∨' #2 =' #2),
          { apply orI₂, apply eqI, },
          { apply andE₂ _,
            apply allE' _ #2,
            apply allE' _ #1,
            apply allE' _ #2,
            apply hypI,
            apply pairset_ax_mem (rfl),
            all_goals { try { simp[set.image_insert_eq], }, },
            split; refl } } },
      { apply andE₂ _ ,
        apply allE' _ #0,
        apply allE' _ ⦃ #1 , #2 ⦄,
        apply hypI,
        apply unionset_ax_mem (rfl),
        all_goals { try { simp[set.image_insert_eq] } },
        split; refl } } }
end

def binary_union_def' {Γ} {φ : formula L} (h₁: φ = ∀' ∀' ∀'(#0 ∈' ⋃ ⦃ #1, #2 ⦄ ↔' #0 ∈' #1 ∨' #0 ∈' #2) )
  (h₂: pairset_ax ∈ Γ ) (h₃ : unionset_ax ∈ Γ) : Γ  ⊢ φ :=
begin
  subst h₁,
  apply weak {pairset_ax, unionset_ax},
  apply binary_union_def,
  intros x h,
  cases h,
  { subst h,
    exact h₂ },
  { rw set.mem_singleton_iff at h,
    subst h,
    exact h₃ }
end

def successor_def : {pairset_ax, unionset_ax} ⊢ ∀' (#0 ∈' S#1 ↔' #0 ∈' #1 ∨' #0 =' #1) :=
begin
  apply allI,
  apply andI,
  { apply impI,
    apply impE (#0 ∈' #1 ∨' #0 ∈' ⦃ #1 ⦄),
    { apply impE (#0 ∈' S#1),
      { apply hypI1, },
      { apply andE₁ _ ,
        apply allE' _ #0,
        apply allE' _ #1,
        apply allE' _ ⦃ #1 ⦄,
        apply binary_union_def' (rfl),
        all_goals{ simp[set.image_insert_eq] } } },
    { apply impI,
      apply orE (#0 ∈' #1) ( #0 ∈' ⦃ #1 ⦄),
      { apply hypI1, },
      { --case x∈a  
        apply orI₁,
        apply hypI1 },
      { --case x∈{a} 
        apply orI₂,
        apply impE_insert,
        apply andE₁ _ ,
        apply allE' _ #0,
        apply allE' _ #1,
        apply singleton_def' (rfl),
        all_goals{ simp[set.image_insert_eq] } } } },
  { apply impI,
    apply orE (#0 ∈' #1) (#0 =' #1),
    { apply hypI1, },
    { -- case x ∈ a
      apply impE (#0 ∈' #1 ∨' #0 ∈' ⦃ #1 ⦄),
      { apply orI₁, apply hypI1,},
      { apply iffE_l, 
        apply allE' _ #0,
        apply allE' _ #1,
        apply allE' _ ⦃ #1 ⦄, 
        apply binary_union_def' (rfl),
        all_goals{ simp[set.image_insert_eq] } } },
    { -- case x = a
      apply impE (#0 ∈' #1 ∨' #0 ∈' ⦃ #1 ⦄),
      { apply orI₂, 
        apply impE_insert,
        apply iffE_l,
        apply allE' _ #0,
        apply allE' _ #1,
        apply singleton_def' (rfl),
        all_goals{ simp[set.image_insert_eq] } },
      { 
        apply iffE_l,
        apply allE' _ #0,
        apply allE' _ #1,
        apply allE' _ ⦃ #1 ⦄,
        apply binary_union_def' (rfl),
        all_goals{ simp[set.image_insert_eq] } } } }
end

def omega_unique 
  : {omega_ax, extensionality} ⊢ ∃! ∀' (#0 ∈' #1 ↔' ∀'( (#0 is_inductive) →' #1 ∈' #0)) := 
begin
  apply andI,
  { -- ∃ case is trivial
    apply exI ω,
    apply hypI,
    simp },
  { -- uniqueness
    apply extensionality_implies_uniqueness' (∀'(#0 is_inductive →' #1 ∈' #0)) (rfl),
    simp }
end

def omega_subset_inductive: 
  {omega_ax} ⊢  ∀' (#0 is_inductive →' (ω ⊆' #0))   :=
begin
  apply allI,
  apply impI,
  apply allI,
  apply impI,
  apply impE (#1 is_inductive),
  { apply hypI, 
    simp [set.image_insert_eq] },
  { apply allE' (#0 is_inductive →' #1 ∈' (#0)) #1,
    apply iffE₂ (#0 ∈' ω),
    { apply hypI1 },
    { apply allE_var0,
      apply hypI,
      apply omega_ax_mem,
      all_goals {simp[set.image_insert_eq] } },
    { refl } }
end

def omega_subset_inductive' {Γ} (h: omega_ax ∈ Γ) : 
  Γ ⊢  ∀' (#0 is_inductive →' (ω ⊆' #0))   :=
begin
  apply weak {omega_ax},
  exact omega_subset_inductive,
  exact set.singleton_subset_iff.mpr h,
end

def omega_inductive :  {omega_ax} ⊢ ω is_inductive :=
begin
  apply andI,
  { apply impE ∀'(#0 is_inductive →' ⌀ ∈' #0), 
    { apply allI,
      apply impI,
      apply andE₁,
      apply hypI,
      simp },
    { apply iffE_l,
      apply allE' _ ⌀,
      apply hypI,
      apply omega_ax_mem (rfl),
      all_goals { simp } } },
  { apply allI,
    apply impI,
    apply impE (∀'(#0 is_inductive →' S#1 ∈' #0)),
    { apply allI,
      apply impI,
      apply impE (#1 ∈' #0),
      { apply impE (#1 ∈' ω),
        { apply hypI,
          simp[set.image_insert_eq] },
        { apply allE' (#0 ∈' ω →' #0 ∈' #1) #1,
          apply impE_insert,
          apply allE_var0,
          apply omega_subset_inductive',
          { simp [set.image_insert_eq] },
          { refl } } },
      { -- unfold is_inductive,
        apply allE' (#0 ∈' #1 →' S #0 ∈' #1) #1 _ (rfl),
        apply andE₂ _ ,
        apply hypI1 } },
    { apply iffE_l,
      apply allE' _ S#0,
      apply hypI,
      { simp [set.image_insert_eq] },
      { simp, } } }
end

def omega_inductive' {Γ} (h: omega_ax ∈ Γ) : Γ  ⊢ ω is_inductive :=
begin
  apply weak_singleton omega_ax,
  exact omega_inductive,
  exact h,
end

def omega_inductive_izf :  izf_ax ⊢ ω is_inductive :=
begin
  apply omega_inductive',
  simp[izf_ax],
end

end izf 