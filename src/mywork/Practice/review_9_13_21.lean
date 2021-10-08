namespace implies
axioms (P Q : Prop)

/-P and Q are arbitrary propositions, they could have more complex names -/

def if_P_is_true_then_so_is_Q : Prop := P → Q

axiom p : P
--assume P is true
--assume we have a proof of P (p)

axiom pq : P → Q
--assume that we have a proof, pq, of P → Q

-- intro for implies: assume premise, show conclusion
-- elimination rile for implies: 

#check pq


/-
Suppose P and Q are propositions and you know that P → Q and that 
P are both true. Show that Q is true.

Proof: Apply the truth of P → Q to the truth of P
to derive the truth of Q.

Proof: By the elimination rule for → with pq applied to p.

Proof: By "modus ponens". QED.
-/

end implies

/- 
FOR ALL
-/
namespace all

axioms 
  (T : Type)
  (P : T → Prop)
  (t : T)
  (a : ∀ (x : T), P x)

end all