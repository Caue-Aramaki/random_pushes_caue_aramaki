
(*I will introduce you to how to operate with Coq
in the very basic steps

 Coq as a language is very raw and with not many
 in built structures.

 Instead, Coq allows for more control by the user
 (even the equalities are defined by the user!)

 Coq works with Inductive, Module, Definition and a
 proof mode.

 Already implemented Types are: nat naturals, bool booleans,
 Prop propositions, Set set.

 Let us work first on Prop.
*)

Check Prop. Check 2 = 1. Check True -> True.

Check False -> False. Eval compute in 10 + 10.

Eval compute in true. Compute false. Compute True -> True.

(* We enter proof mode by defining a goal/theorem
 about a proposition. the followint is the structure of a
 well written proof.*)

Goal forall (A:Prop), A -> A. (* Goal, definition of A, Prop.*)
Proof. (*Start of your proof.*)
  intros A. (*Introduces A as a given fact.*)
  intros Hypoth. (*Same as above*)
  (*We now know that A is a given fact because of Hypoth,
   and that we want to prove A.*)
  exact Hypoth. (* "Same as Hypoth"*)
  (*Now we can close our proof with Qed.*)
Qed.

Goal forall A B : Prop, (A -> A) /\ (B -> B).
Proof.
  intros. (*This command introduces everything automatically.*)
  (*Well, we met this: (A -> A) /\ (B -> B) which is "And".*)
  refine(conj _ _). (*This separates 1 goal into 2.*)
  (*In Coq, we always prove the topmost subgoals first.
  If you want to skip any of them for the time being, you
  can call the "admit." command, and it eliminates the
  topmost goal.*)
  admit.
  intro H.
  exact H.
  (*At this point, the following message displays:
  No more subgoals, but there are some goals you gave up:

  A -> A

  You need to go back and solve them.
  Let us end our proof and do it the right way.*)
  Admitted.
  (*The command Admitted. closes an entire proof under 
  the assumption that it is an axiom/unfinished proof.*)

Goal forall A B : Prop, (A -> A) /\ (B -> B).
Proof.
  intros.
  refine(conj _ _).
  trivial.
  auto.
Qed.

Theorem n_equals_n : forall n:nat, n = n.
Proof.
  (*Whenever we have "forall", it is a good idea to 
  introduce the variables/facts.*)
  intros.
  (*To prove this, you can use auto/trivial/intuition etc.
  The ideal argument instead is "reflexivity.". Let us use
  that.*)
  reflexivity.
Qed.

Goal forall n m:nat, n = n /\ m = m.
Proof.
  intros.
  refine(conj _ _).
  (*We can use flexibility again, but let use our recently
  proven theorem/lemma.*)
  apply n_equals_n.
  (*Or, we can introduce our lemma for later.*)
  pose proof n_equals_n as theorem.
  (* pose [args]. takes some arguments and generates a new
  fact object which we can use later.*)
  apply theorem.
Qed.

Goal true = true.
Proof.
  (*We could just use reflex. or apply a previous theorem,
  but let me show you another strategy.*)
  
  pose(x := true). (*Declares "obj" defined as "true".*)
  (*We can create facts which will be added as a subgoal,
  and we will need to prove such fact.*)
  assert(x = true). trivial.
  (*Now, we can rewrite our goal.*)
  rewrite <- H.
  pose proof n_equals_n as T.
  trivial.
Qed.

Goal 5 < 6.
Proof.
  intuition.
Qed.

Goal 5 <> 6. (* 5 not equal 6*)
Proof.
  (*reflexivity here fails. lets try unfolding this.*)
  unfold not. (*you can try autounfold.*)
  intro H.
  (*We ended up in false. It means one of our Props is
  false by nature, and we need to check which one.
  Thankfully, since the statement H is simple enough,
  we use discriminate.*)
  discriminate.
Qed.

Goal False -> False.
Proof.
  intro.
  (*One of our facts is false, let us use that.*)
  exact H.
Qed.

Goal forall a b:Prop, a -> b \/ a.
Proof.
  intros.
  pose (H0 := or_intror H : b \/ a).
  Check H0.
  (*We created a fact "b \/ a" with the argument H. Only
  demanding part was "or_intro(l/r)".*)
  exact H0.
Qed.
  
(*Here is a nice exercise:*)
Goal (forall A B : Prop, A -> (A->B) -> B).
Proof.
 intros A.
 intros B.
 intros proof_of_A.
 intros A_implies_B.
 pose (proof_of_B := A_implies_B proof_of_A).
 (*pose (proof_of_B := proof_of_A A_implies_B).
  this is the incorrect order.*)
 exact proof_of_B.
Qed.

Goal (forall A B : Prop, A\/B -> B\/A).
Proof.
  intros.
  case H.

    intro.
    refine(or_intror _).
    exact H0.
    
    intro.
    refine(or_introl _). (*this one is different from above*)
    exact H0.
Qed.

Goal forall (a b:Prop), exists x:Prop, x -> (a->b) -> b.
Proof.
  intros.
  (*We have an existence question. we can either prove it,
  with an example, prove it in a shady way, or disprove it.*)
  pose(example := a).
  (*We have our example, let us substitute in our goal.*)
  refine(ex_intro _ example _).
  (*refine(ex_intro function example _). more on documentation*)

  (*We eliminated the existencial condition. we proceed.*)
  intros.
  pose(H1 := H0 H).
  exact H1.
Qed.

(*We will need the following knowledge.*)
Goal True.
Proof. exact I. Qed.

(*Let us make a tiny exercise.*)
Lemma x_not_false_and_x_true : forall x:Prop, x <> False /\ x -> True.
Proof.
  intros.
  destruct H as [].
  exact I.
Qed.

(*Little challenge for you.*)
Theorem a_true_false : forall a:Prop, ((a->True)/\(a->False))->False.
Proof.
  (*Write proof here*)
Admitted. 


Goal ~exists x:Prop, 
  x <> False /\ x -> False.
Proof.
  intros.

  (*It may not tell you, but the negation of existence is
  for all. Let us use that.*)
  
  pose proof x_not_false_and_x_true as H.
  unfold not.
  
  intro.
  case H0.
  unfold not in H.
  (*Okay, now our lemma comes in place to help us.
  we will use the last two lemmas.*)
  
  intros.

  pose proof a_true_false as T. (*challenge lemma*)

  pose(s := ((x = False) -> False) /\ x). (*lets make a 
  variable substitution.*)
  assert(s = (((x = False) -> False) /\ x)). intuition.
  (*do not forget that we need to prove both are equal.*)
  (*we are rewriting so that we get the shape that
  lemma T requires.*)
  
  rewrite <- H2 in H1.
  (*since our prior lemma is for all x, we need to specify
  one x.*)
  assert((((x = False) -> False) /\ x) -> True). apply H.

  rewrite <- H2 in H3.
  (*we make more asserts to finish with T*)
  assert((s -> True) /\ (s -> False)). intuition.
  assert(((s -> True) /\ (s -> False))->False). apply T.

  pose(finale := H5 H4).
  exact finale.
Qed.


(*Since the last proof was on the heavy end of a simple
  proof, we shall have a break to explore the nat set.*)

Print nat.

(*Inductive nat : Set :=  
| O : nat 
| S : nat -> nat.*)

(*We define nat as an inductive type, which constructors
  are O and S (uppercase O, not zero.*)

Eval compute in 5 - 3.

(*Every simple natural operation except division is defined.
  With subtraction there is a catch, 3 - 5 = 0.*)

Eval  compute in 3 - 5.

Lemma sub_in_nat_is_weird : 3 - 5 = 0.
Proof.
  simpl. (*This simplifies an expression.*)
  reflexivity.
Qed.

(*Proving in naturals function the same way as we did
  before.*)

(*We define 3 as S(S(S(O))).*)

Goal S(S(S(0))) = 3.
Proof.
  reflexivity. Qed.

(*let us define a function that detects a zero.*)

Definition is_zero (n:nat) := (*parameters*)
match n with (*works in a similar fashion of switch case*)
| O => true (*if base constructor (aka 0), then true*)
| S n' => false (* if it is a sucessor of any number, false*)
end.

Eval compute in is_zero 0. Compute is_zero 11.

(*Let us create a definition*)
Definition n_not_0 : forall n:nat, is_zero n = false -> n > 0.
Admitted.

Goal is_zero 0 = true.
Proof.
  simpl.
  reflexivity.
Qed.

(*We can define recursive functions.*)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Eval compute in evenb 2. Compute evenb 4.

(*Let us define some facts.*)

Definition a0 : forall b:bool, negb b <> b.
Proof.
  intro b.
  autounfold.
  case b.
    simpl. intro. discriminate.
    simpl. intro. discriminate.
Qed.

Definition a0_1 : forall b:bool, b <> negb b.
Proof.
  intro b.
  autounfold.
  case b.
    simpl. intro. discriminate.
    simpl. intro. discriminate.
Qed.

Definition a1 : forall (n:nat), 
  evenb n = evenb (n+2).
Proof.
  (*Can you prove it?*)
Admitted.

Definition a2 : forall (n:nat),
  evenb n = negb (evenb(n+1)).
Proof.
  (*Yet again another challenge.*)
Admitted.

Definition a2_1 : forall (n:nat), evenb n <> evenb(n+1).
Proof.
  intro.
  pose proof a2 as a2.
  rewrite a2.
  pose proof a0 as a0.
  apply a0.
Qed.

Definition a2_2 : forall n:nat, 
evenb n = negb (evenb (n + 1)) <-> evenb n <> evenb(n+1).
Proof.
  intro.
  unfold iff.
  refine(conj _ _).

    intro.
    rewrite H.
    pose proof a0 as a0.
    apply a0.

    intro.
    autounfold in H.
    (*                    did not work for me.
    destruct H as [].
    pose proof a2 as a2.
    rewrite a2.
    pose proof a0 as a0.
    
    pose(x := evenb(n+1)).
    assert(x = evenb(n+1)).
    auto.
    rewrite <- H.
    case x.
      simpl.
      assert(false <> true). intuition. discriminate.*)
    pose proof a2.
    apply H0.
Qed.

Goal 6 = 6.
Proof.
  assert(forall x:nat, x = x). reflexivity.
  pose(x := 6).
  assert(6 = x). trivial.
  rewrite H0.
  apply H.
Qed.
  

Goal evenb 4 = evenb 6.
Proof.
  pose proof a1 as hyp_1.
  apply hyp_1.
Qed.

Goal evenb 4 = evenb 820.
Proof.
  pose proof a1 as hyp_1.
  apply hyp_1.
Qed.

Goal evenb 4 <> evenb 5.
Proof.
  pose proof a2_1 as hyp_2.
  apply hyp_2.
Qed.

Goal evenb 7 = false.
Proof.
  simpl.
  reflexivity.
Qed.

(*Here we start the real theorems!*)
Theorem two_n_is_even : forall n:nat, evenb(2*n) = true.
Proof.
  intro.
  elim n. simpl. reflexivity.
    intros.
    pose proof a1.
    rewrite H0 in H.
    assert(2* S n0 = 2*n0 + 2). auto.
    rewrite H1.
    exact H.
Qed.

(*This one will be really complicated to follow through.*)
Theorem a3_1 : forall n:nat, evenb(2*n + 1) = false.
Proof.
  intro.
  pose proof two_n_is_even as lem1.
  pose proof a2 as lem2.
  
  assert(forall n : nat, 
      evenb (2*n) = negb (evenb (2*n + 1))).
    intro.
    pose(x:=2*n0).
    assert(2*n0 = x). auto.
    rewrite H.
    apply lem2.
  
    assert(negb(evenb (2 * n + 1)) = true).
    rewrite <- H.
    apply lem1.
    
    assert(forall b:bool, negb b = true -> b = false).
    intro b.
    case b.
      auto.
      auto.
    
    pose(x:=2 * n + 1). assert(x = 2 * n + 1). auto.
    rewrite <- H2.
    assert(negb(evenb(x)) = true).
    rewrite H2.
    exact H0.
    apply H1.
    exact H3.
Qed.

(*If you could figure out what was happening there, please
  tell me!!*)

(*Let us stray away from evenb functions.*)

Require Import Arith.
(*We imported a library!*)

Compute 5 mod 3.

(*Now we can talk about notations. Let us define a notation.*)

Notation "x ! y" := (y mod x =0) (at level 35).

Compute 3 ! 7.

Goal 3 ! 6.
Proof.
  simpl.
  reflexivity.
Qed.

Goal ~ (3 ! 7).
Proof.
  simpl.
  unfold not.
  intro.
  discriminate.
Qed.

Goal forall (x:nat) (k:nat), x ! (k * x).
Proof.
  intros.
  elim k. simpl. 
    assert(x * 0 = 0). intuition. admit.
    intros. simpl.
    
    


















