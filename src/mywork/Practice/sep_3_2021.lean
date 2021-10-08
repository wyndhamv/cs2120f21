/-

Theorem: Equality is symmetric. In other words, 
∀ (T : Type) (x y : T), x = y → y = x

x and y are arbitrary objects of a type T. If we have a proof that x equals y,
then we can use the axiom of substitutability to rewrite x as y. Then, 
reflexitivity proves the theorem.

Proof: First we'll assume that T is any tyep and we have objects x and y of this type. 
What remains to be shown is that x = y → y = x. To prove this, we'll assue the premise, that 
x = y, and in this context what remains is to prove y = x. But by the axiom of substitutability 
of equals, and using the fact x = y, we can rewrite x in the goal as y, yielding y = y as our new 
proof goal. This is true by the reflexivity of equality. QED.
Theorem: ∀ (T : Type)



-/

/-
Prove that equality is transitive.

-/

theorem eq_trans : 
  ∀ (T: Type) (x y z : T), x = y → y = z → x = z := 
  begin
    assume (T : Type),
    assume ( x y z : T),
    assume (e1 : x = y),
    assume (e2 : y = z),
    rw e1,
    rw e2,
  end


/-theorem eq_symm : 
  ∀ (T : Type) (x y : T), x = y → y = x := 
  begin
    assume (T : Type),
    assume (x y : T),
    assume (e : x = y),
    rw e,
  end
-/