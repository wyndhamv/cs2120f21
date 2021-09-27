
/-
A simple predicate.
-/
def ev (n : ℕ) : Prop := n%2=0

def np5d12 (n : ℕ) : Prop := (n+5)%12 = 0


/-
Introduction rule for exists
-/
example : exists (n : ℕ), ev n :=
begin
end

example : exists n, ev n := _


example : exists (a b c : ℕ), a*a + b*c = c*c := 
begin
  
end


example : ∀ (n : ℕ), ∃ (m : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro _,
end

example : ∀ (m : ℕ), ∃ (n : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro (2*m),
end

example : (∃ (n : nat), ev n) → true :=
begin
assume h,
cases h with v pf,
intros,
end