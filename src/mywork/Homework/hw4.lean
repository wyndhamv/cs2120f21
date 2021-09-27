-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro,

  --forwards
    assume npaq,
    have ponp := classical.em P,
    have qonq := classical.em Q,

    apply or.elim ponp,
      --assume p
        assume p,
        apply or.elim qonq,
          --assume q
            assume q,
            have f : false := npaq (and.intro p q),
            contradiction,
          --assume not q
            assume nq,
            apply or.intro_right,
            exact nq,
      --assume not p
        assume np,
        apply or.intro_left,
        exact np,

  --backwards
    assume nponq,
    have ponp := classical.em P,
    have qonq := classical.em Q,

    apply or.elim ponp,
      --assume p
        assume p,
        apply or.elim qonq,
          --assume q
            assume q,
            assume paq,
            apply or.elim nponq,
              --assume not p
                assume np,
                contradiction,
              --assume not q
                assume nq,
                contradiction,
          --assume not q
            assume nq,
            assume paq,
            have q := and.elim_right paq,
            contradiction,
      --assume not p
        assume np,
        assume paq,
        have p := and.elim_left paq,
        contradiction,
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume npoq,
  have ponp := classical.em P,

  apply or.elim ponp,
    --assume p
      assume p,
      have poq := or.intro_left Q p,
      have f : false := npoq poq,
      contradiction,
    --assume np
      assume np,
      have qonq := classical.em Q,
      apply or.elim qonq,
        --assume q
          assume q,
          have poq := or.intro_right P q,
          have f := npoq poq,
          contradiction,
        --assume not q
          assume nq,
          exact and.intro np nq,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro,

  --forwards
    assume ponpaq,
    apply or.elim ponpaq,

    --assume p 
      assume p,
      apply or.intro_left Q p,

    --assume not p and q
      assume npaq,
      have q := and.elim_right npaq,
      apply or.intro_right P q,

  --backwards
    assume poq,
    apply or.elim poq,

    --assume p
      assume p,
      apply or.intro_left (¬P ∧ Q) p,

    --assume q
      assume q,
      have ponp := classical.em P,
      apply or.elim ponp,

      --assume p
        assume p,
        apply or.intro_left,
        exact p,

      --assume not p
        assume np,
        apply or.intro_right,
        apply and.intro,
        exact np,
        exact q,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro,

  --forwards
    assume poqapor,
    have poq := and.elim_left poqapor,
    have por := and.elim_right poqapor,
    apply or.elim poq,

      --p
        assume p,
        apply or.intro_left (Q ∧ R) p,

      --q
        assume q,
        apply or.elim por,

        --p
          assume p,
          apply or.intro_left (Q ∧ R) p,
        
        --r
          assume r,
          apply or.intro_right,
          apply and.intro q r,

  --backwards
    assume poqar,
    apply or.elim poqar,

      --p
        assume p,
        have poq := or.intro_left Q p,
        have por := or.intro_left R p,
        apply and.intro,
        exact poq,
        exact por,

      --qar
        assume qar,
        have q := and.elim_left qar,
        have r := and.elim_right qar,
        apply and.intro,
        apply or.intro_right P q,
        apply or.intro_right P r,
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro,
  
  --forwards
  assume poqaros,
  have poq := and.elim_left poqaros,
  have ros := and.elim_right poqaros,
  show (P ∧ R) ∨ ((P ∧ S) ∨ ((Q ∧ R) ∨ (Q ∧ S))),
  -- (P ∧ R) OR {(P ∧ S) OR [(Q ∧ R) OR (Q ∧ S)]}
  apply or.elim poq,
    --assume p
      assume p,
      apply or.elim ros,
        --assume r
          assume r,
          apply or.intro_left,
          exact and.intro p r,
        --assume s
          assume s,
          apply or.intro_right,
          apply or.intro_left,
          exact and.intro p s,
    --assume q
      assume q,
      apply or.elim ros,
        --assume r
          assume r,
          apply or.intro_right,
          apply or.intro_right,
          apply or.intro_left,
          exact and.intro q r,
        --assume s
          assume s,
          apply or.intro_right,
          apply or.intro_right,
          apply or.intro_right,
          exact and.intro q s,

  --backwards
  assume paropasoqaroqas,
  apply or.elim paropasoqaroqas,
    --assume par
      assume par,
      have p := and.elim_left par,
      have r := and.elim_right par,
      apply and.intro,
      apply or.intro_left Q p,
      apply or.intro_left S r,
    --assume pasoqaroqas
      assume pasoqaroqas,
      apply or.elim pasoqaroqas,
        --assume pas
          assume pas,
          have p := and.elim_left pas,
          have s := and.elim_right pas,
          apply and.intro,
          apply or.intro_left Q p,
          apply or.intro_right R s,
        --assume qaroqas
          assume qaroqas,
          apply or.elim qaroqas,
            --assume qar
              assume qar,
              have q := and.elim_left qar,
              have r := and.elim_right qar,
              apply and.intro,
              apply or.intro_right P q,
              apply or.intro_left S r,
            --assume qas
              assume qas,
              have q := and.elim_left qas,
              have s := and.elim_right qas,
              apply and.intro,
              apply or.intro_right P q,
              apply or.intro_right R s,
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/

lemma not_all_nats_are_zero : ∃ (n : ℕ), n ≠ 0 :=
begin
  apply exists.intro 4 _,
  assume fez,
  cases fez,
end 

#check ℕ

#check ∃ (n : ℕ), n ≠ 0
-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro,

  --forwards
    assume piq,
    have ponp := classical.em P,
    apply or.elim ponp,
      --p
        assume p,
        have q : Q := piq p,
        apply or.intro_right,
        exact q,
      --not p
        assume np,
        apply or.intro_left,
        exact np,

  --backwards
    assume npoq,
    assume p,
    apply or.elim npoq,

      --not p
        assume np,
        contradiction,

      --q
        assume q,
        exact q,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume piq,
  assume nq,
  have ponp := classical.em P,

  apply or.elim ponp,
    --assume p
      assume p,
      have q := piq p,
      contradiction,

    --assume np
      assume np,
      exact np,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume npinq,
  assume q,
  have ponp := classical.em P,

  apply or.elim ponp,
    --assume p
      assume p,
      exact p,

    --assume np,
      assume np,
      have nq := npinq np,
      contradiction,
end

