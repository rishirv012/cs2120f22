
/-
This is the CS2120 (Sullivan) midterm exam. 

The exam has 100 points total distributed over four
multi-part questions. There's an extra credit question
at the end. Points for each part are indicated.
-/

-- ****************** #1 [30 points] *******************

/- A. [5 points] 

Is it true in predicate logic that  
(false → true) ∧ (false → false)?
Answer: Yes, this is true because when you start with false, any statement can be true,
so false implies true is true since false can imply anything and false implies false is 
also true meaning this ∧ is checking true ∧ true. The predicate logic rule for this would 
be false elimination if it was written in formal logic.


-/

/- B. [10 points] 

Give a formal proof by completing the 
following "example" in Lean, or state 
in English that there is no such proof.

-/

example : (false → true) ∧ (true → true) :=
begin
apply and.intro,
assume f,
apply false.elim,
exact f,
assume t,
exact t,
end


/- C [15 points]. 

Give an English language proof of the proposition. 
Identify each inference  rule you use at each point
in your argument. For example, at a certain point 
you might say something like this: By the ____ rule, 
it will suffice to show ____. Then you would go on
to show that what remains to be proved is valid. 


Answer:
To start, you need to split the and apart using and.intro which will turn the proposition
into false → true and true → true. Then, to prove false → true, you can just apply false
elimination which shows that with a proof of false anything else is true. There is no 
formal proof needed for the second part since it is just saying that true implies itself
which can be shown by assuming the first true and seeing that the result is the same as
the assumption
-/


-- ****************** #2 [30 points] *******************


/- 
"Resolution" is an inference rule that we 
haven't talked about before. It's valid in
propositional, classical, and constructive
predicate logic. We will present the rule,
in both propositional and predicate logic,
and will ask you to prove that is's valid
in each case.


In propositional logic, the resolution rule 
is ¬P ∨ Q, P ⊢ Q. To check its validity, we 
can write it as  (¬P ∨ Q) ∧ P → Q. Note: ∧ 
has higher precedence than →, so there are 
implicit parentheses around (¬P ∨ Q) ∧ P, 
making the overall proposition an implication.
-/


/- A. [5 points].

Give a brief English language explanation why this
inference rules makes sense: not a rigorous proof,
just an explanation of why Q has to be true under
the conditions give by the assumptions/premises.

Answer: The rule states that P is true, and that out of ¬P and Q, at least one must be true, 
Since it is telling us that P is true, that must mean that ¬P is false and therefore Q has 
to be true to satisfy the ∨ 
-/



/- B. [5 points]

Prove that this inference rule is valid in
propositional logic by giving a truth table for it. 
We'll give you a start. Fill in the rows then state
how you know from the truth table that the overall
proposition is valid.

P   Q   (¬P ∨ Q)    (¬P ∨ Q) ∧ P    ((¬P ∨ Q) ∧ P) → Q
------------------------------------------------------
f   f   t           f               t
f   t   t           f               t
t   f   f           f               t
t   t   t           t               t


Statement: 
The truth table shows that the proposition of (¬P ∨ Q) ∧ P will always imply Q no matter
what the values of P and Q are so the overall proposition of ((¬P ∨ Q) ∧ P) → Q is always
true, proving the validity of the proposition
-/  


/- C. [10 points] 

Give a formal proof that the inference rule is 
valid in our constructive predicate logic. Fill
in a proof script here to construct your proof.
Hint: remember that the cases tactic applied to
a proof of a conjunction applied and.elim both
left and right, and when applied to a proof of 
a disjunction gives you two cases to consider,
where you need to show that the remining goal
is true in either case. 
-/

example : ∀ (P Q : Prop), (¬P ∨ Q) ∧ P → Q :=
begin
assume P Q,
assume h,
apply or.elim (classical.em P),
assume p,
cases h with npq p,

apply or.elim npq,
assume np,
contradiction,
assume q,
exact q,
assume np,
cases h with pq p,
contradiction,
end


/-
D. [10 points] Give an informal (English) proof 
that the inference rule is valid in predicate logic. 
Name each inference rule you use in your reasoning.

Answer: Use the law of excluded middle ot create two cases for the proposition then use
case analysis to seperate the cases. Use the or elimination rule to create a contradiction
for the case where P implies Q and use case analysis to create another contradiction for the 
case where not P implies Q.
-/


-- ****************** #3 [20 points] *******************


/- 
A. [10 points]. Write formally (in constructive logic) 
the proposition that, for any propositions P and Q, if 
P is equivalent to Q (iff), then if P is true, then Q
is true.  Hint: put parentheses around your ↔ expression. 
-/

-- Don't try to write a proof here; just the proposition
def if_p_iff_q_then_if_also_p_then_q : Prop :=
    ∀ (P Q : Prop), (P ↔ Q) ∧ P → Q


/-
B. [10 points] Give *either* a precise, complete English
language proof that this proposition is valid, naming 
each inference you you use in your reasoning, *or* give 
a formal proof of it using Lean. You do not have to give
both. 
-/
/-
Option #2: Formal proof. Reminders: the iff elim
rules are called iff.mp and iff.mpr in Lean; or you
can use "cases" to apply the two elimination rules 
to a proof of a bi-implication automatically.
-/

example : if_p_iff_q_then_if_also_p_then_q :=
begin
unfold if_p_iff_q_then_if_also_p_then_q,
assume P Q,
assume h,
cases h with bi p,
apply iff.mp bi,
exact p,
end




-- ****************** #4 [20 points] *******************

/- #



A. [10 points] Suppose P is any proposition. In plain
English give a step by step explanation of how you would 
go about proving ¬P using proof *by negation*. 

Answer: In order to prove ¬P by negation, you need to show that P implies false. You do this
by assuming P from ¬P leaving the theorem as P → false from which you can usually get 
some sort of contradiction since you cannot create proofs of false. 


-/


/- B. [10 points] 

In plain English explain each step in a proof of P
*by contradiction*. Identify where a proof by negation 
(¬ introduction) occurs in the proof by contradiction. 
Explain what classical rule of inference you need to 
use to finish off such a proof. 

Answer: 
To do a proof by contradiction you start by assuming the opposite of what you want to prove,
so in this case you can start by assuming P as false. You then show how this will lead to
a contradiction which would mean that P has to be true to satisfy the condition. You need
the law of excluded middle to create cases which you can then solve into contradiction

-/



/- Extra Credit [10 points for all three answers correct]

Suppose that "if it's sunny, it's hot, and also that if 
it's not sunny, it's hot. 


A. Is it hot in classical logic? 

Answer: Yes because this states that it will always be hot whether or not it is funny. 


B. Is it hot "constructively?" Briefly explain your answer. 
    
Answer: In constructive logic you can derive a proof of y from a proof of x but since
we don't know whether its sunny or not sunny, we cant derive a proof that its hot because
the statments creates a logical fallacy. 


C. Give a formal proof of your answer to the classical question. 
Use S and H as names to stand for the propositions, "it's sunny" 
and "it's hot," where S stands for "it's sunny" and H stands for
"it's hot."
-/

-- it's hot
example : ∀ (S H : Prop), (S → H) → (¬S → H) → H :=
begin
assume S H,
assume sh nsh,


end

