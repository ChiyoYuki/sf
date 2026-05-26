(** * Sort: Insertion Sort *)

(** Sorting can be done in expected O(N log N) time by various
    algorithms (quicksort, mergesort, heapsort, etc.).  But for
    smallish inputs, a simple quadratic-time algorithm such as
    insertion sort can actually be faster.  It's certainly easier to
    implement -- and to verify. *)

(** If you don't recall insertion sort or haven't seen it in
    a while, see Wikipedia or read any standard textbook; for example:

    - Sections 2.0 and 2.1 of _Algorithms, Fourth Edition_, by
      Sedgewick and Wayne, Addison Wesley 2011; or

    - Section 2.1 of _Introduction to Algorithms, 3rd Edition_, by
      Cormen, Leiserson, and Rivest, MIT Press 2009. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From VFA Require Import Perm.

(* ################################################################# *)
(** * The Insertion-Sort Program *)

(** Insertion sort is usually presented as an imperative program
    operating on arrays.  But it works just as well as a functional
    program operating on linked lists. *)

(* [insert i l] inserts [i] into its sorted place in list [l].
   Precondition: [l] is sorted. *)
Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insert i t
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.

Example sort_pi :
  sort [3;1;4;1;5;9;2;6;5;3;5]
  = [1;1;2;3;3;4;5;5;5;6;9].
Proof. simpl. reflexivity. Qed.

(** What Sedgewick/Wayne and Cormen/Leiserson/Rivest don't acknowlege
    is that the arrays-and-swaps model of sorting is not the only one
    in the world.  We are writing _functional programs_, where our
    sequences are (typically) represented as linked lists, and where
    we do _not_ destructively splice elements into those lists. *)

(** As usual with functional lists, the output of [sort] may share
    memory with the input.  For example: *)

Compute insert 7 [1; 3; 4; 8; 12; 14; 18].
(* = [1; 3; 4; 7; 8; 12; 14; 18] *)

(** The tail of this list, [12 :: 14 :: 18 :: []], is not disturbed or
    rebuilt by the [insert] algorithm.  The head [1 :: 3 :: 4 :: 7 :: ...]
    contains new nodes constructed by [insert].  The first three nodes
    of the old list, [1 :: 3 :: 4 :: ...], will likely be
    garbage-collected if no other data structure is still pointing at
    them.  Thus, in this typical case,

     - Time cost = 4X

     - Space cost = (4-3)Y = Y

    where X and Y are constants, independent of the length of the
    tail.  The value Y is the number of bytes in one list node: 2 to 4
    words, depending on how the implementation handles
    constructor-tags.  We write (4-3) to indicate that four list nodes
    are constructed, while three list nodes become eligible for
    garbage collection.

    We will not prove such things about the time and space cost, but
    they are true anyway, and we should keep them in consideration. *)

(* ################################################################# *)
(** * Specification of Correctness *)

(** A sorting algorithm must rearrange the elements into a list
    that is totally ordered. There are many ways we might express that
    idea formally in Coq.  One is with an inductively-defined
    relation that says: *)

(** - The empty list is sorted.

    - Any single-element list is sorted.

    - For any two adjacent elements, they must be in the proper order. *)

Inductive sorted : list nat -> Prop :=
| sorted_nil :
    sorted []
| sorted_1 : forall x,
    sorted [x]
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Hint Constructors sorted : core.

(** This definition might not be the most obvious. Another
    definition, perhaps more familiar, might be: for any two elements
    of the list (regardless of whether they are adjacent), they should
    be in the proper order.  Let's try formalizing that.

    We can think in terms of indices into a list [lst], and say: for
    any valid indices [i] and [j], if [i < j] then [index lst i <=
    index lst j], where [index lst n] means the element of [lst] at
    index [n].  Unfortunately, formalizing this idea becomes messy,
    because any Coq function implementing [index] must be total: it
    must return some result even if the index is out of range for the
    list.  The Coq standard library contains two such functions: *)

Check nth : forall A : Type, nat -> list A -> A -> A.
Check nth_error : forall A : Type, list A -> nat -> option A.

(** These two functions ensure totality in different ways:

    - [nth] takes an additional argument of type [A] --a _default_
      value-- to be returned if the index is out of range, whereas

    - [nth_error] returns [Some v] if the index is in range and [None]
      --an error-- otherwise.

    If we use [nth], we must ensure that indices are in range: *)

Definition sorted'' (al : list nat) := forall i j,
    i < j < length al ->
    nth i al 0 <= nth j al 0.

(** The choice of default value, here 0, is unimportant, because it
    will never be returned for the [i] and [j] we pass.

    If we use [nth_error], we must add additional antecedents: *)

Definition sorted' (al : list nat) := forall i j iv jv,
    i < j ->
    nth_error al i = Some iv ->
    nth_error al j = Some jv ->
    iv <= jv.

(** Here, the validity of [i] and [j] are implicit in the fact
    that we get [Some] results back from each call to [nth_error]. *)

(** All three definitions of sortedness are reasonable.  In practice,
    [sorted'] is easier to work with than [sorted''] because it
    doesn't need to mention the [length] function. And [sorted] is
    easiest, because it doesn't need to mention indices. *)

(** Using [sorted], we specify what it means to be a correct sorting
    algorthm: *)

Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
    Permutation al (f al) /\ sorted (f al).

(** Function [f] is a correct sorting algorithm if [f al] is
    [sorted] and is a permutation of its input. *)

(* ################################################################# *)
(** * Proof of Correctness *)

(** In the following exercises, you will prove the correctness of
    insertion sort. *)

(** **** Exercise: 3 stars, standard (insert_sorted) *)

(* Prove that insertion maintains sortedness. Make use of tactic
   [bdestruct], defined in [Perm]. *)

Lemma insert_sorted:
  forall a l, sorted l -> sorted (insert a l).
Proof.
  intros a l S. induction S; simpl.
  - apply sorted_1.
  - bdestruct (a <=? x).
    + auto.
    + unfold gt in H. unfold lt in H. assert (H' : x <= a). { lia. } auto.
  - bdestruct (a <=? x).
    + auto.
    + simpl in IHS. bdestruct (a <=? y).
      * apply sorted_cons. lia. apply sorted_cons. lia. apply S.
      * apply sorted_cons. lia. apply IHS.
Qed. 

(** [] *)

(** **** Exercise: 2 stars, standard (sort_sorted) *)

(** Using [insert_sorted], prove that insertion sort makes a list
    sorted. *)

Theorem sort_sorted: forall l, sorted (sort l).
Proof.
  intros l.
  induction l as [| x l' IHl'].
  - auto.
  - simpl. apply insert_sorted. apply IHl'.
Qed.  

(** [] *)

(** **** Exercise: 3 stars, standard (insert_perm) *)

(** The following lemma will be useful soon as a helper. Take
    advantage of helpful theorems from the [Permutation] library. *)

Lemma insert_perm: forall x l,
    Permutation (x :: l) (insert x l).
Proof.
  intros x l.
  induction l as [| y l' IHl'].
  - auto.
  - simpl. bdestruct (x <=? y).
    + auto.
    + apply perm_trans with (y :: x :: l').
      apply perm_swap. apply perm_skip. apply IHl'.
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard (sort_perm) *)

(** Prove that [sort] is a permutation, using [insert_perm]. *)

Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
  intros l. induction l as [| x l IHl'].
  - auto.
  - simpl. apply perm_trans with (x :: sort l).
    + apply perm_skip. apply IHl'.
    + apply insert_perm.
Qed. 

(** [] *)

(** **** Exercise: 1 star, standard (insertion_sort_correct) *)

(** Finish the proof of correctness! *)

Theorem insertion_sort_correct:
    is_a_sorting_algorithm sort.
Proof.
  unfold is_a_sorting_algorithm. intros al. split.
  apply sort_perm. apply sort_sorted.
Qed.

(** [] *)

(* ################################################################# *)
(** * Validating the Specification (Advanced) *)

(** You can prove that a program satisfies a specification, but how
    can you prove you have the right specification?  Actually, you
    cannot.  The specification is an informal requirement in your
    mind.  As Alan Perlis quipped, "One can't proceed from the
    informal to the formal by formal means."

    But one way to build confidence in a specification is to state it
    in two different ways, then prove they are equivalent. *)

(** **** Exercise: 4 stars, advanced (sorted_sorted') *)
Lemma sorted_sorted': forall al, sorted al -> sorted' al.

(** Hint: Instead of doing induction on the list [al], do induction on
    the sortedness of [al]. This proof is a bit tricky, so you may
    have to think about how to approach it, and try out one or two
    different ideas.*)
Proof.
  intros al H. induction H; unfold sorted'; intros.
  - rewrite nth_error_nil in H0. discriminate.
  - destruct i, j; simpl in H0; simpl in H1;
    try rewrite nth_error_nil in H0; try rewrite nth_error_nil in H1;
    try discriminate; lia.
  - destruct i, j; simpl in H2; simpl in H3;
    try injection H2 as H2; try injection H3 as H3; try lia. 
    + unfold sorted' in IHsorted. apply Nat.le_trans with y; try lia.
      bdestruct (j =? 0); subst; simpl in *.
      * injection H3 as H3. lia.
      * apply (IHsorted 0 j); simpl in *; auto; lia. 
    + unfold sorted' in IHsorted. apply (IHsorted i j); auto; lia. 
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (sorted'_sorted) *)
Lemma sorted'_sorted : forall al, sorted' al -> sorted al.
Proof.
(** Here, you can't do induction on the sortedness of the list,
    because [sorted'] is not an inductive predicate. But the proof
    is less tricky than the previous. *)
  induction al.
  - intros H. apply sorted_nil.
  - induction al.
    + intros H. apply sorted_1.
    + intros H. apply sorted_cons.
      * unfold sorted' in H. specialize H with (i := 0) (j := 1). auto.
      * apply IHal. clear IHal. clear IHal0. unfold sorted' in *.
        intros. specialize H with (i := S i) (j := S j). 
        apply H; simpl; try lia; auto.
Qed.
  
(** [] *)

(* ################################################################# *)
(** * Proving Correctness from the Alternative Spec (Optional) *)

(** Depending on how you write the specification of a program, it can
    be harder or easier to prove correctness.  We saw that predicates
    [sorted] and [sorted'] are equivalent.  It is significantly
    harder, though, to prove correctness of insertion sort directly
    from [sorted'].

    Give it a try!  The best proof we know of makes essential use of
    the auxiliary lemma [nth_error_insert], so you may want to prove
    that first.  And some other auxiliary lemmas may be needed too.
    But maybe you will find a simpler appraoch!

    DO NOT USE [sorted_sorted'], [sorted'_sorted], [insert_sorted], or
    [sort_sorted] in these proofs.  That would defeat the purpose! *)

(** **** Exercise: 5 stars, standard, optional (insert_sorted') *)

Lemma nth_error_insert : forall l a i iv,
    nth_error (insert a l) i = Some iv ->
    a = iv \/ exists i', nth_error l i' = Some iv.
Proof.
  induction l as [| x l' IHl'].
  - simpl. intros. left. destruct i as [| i]; simpl in H.
    + injection H as H. apply H.
    + rewrite nth_error_nil in H. discriminate H.
  - simpl. intros. bdestruct (a <=? x); destruct i; simpl in *.
    + left. injection H as H. apply H.
    + right. exists i. apply H.
    + right. exists 0. auto.
    + apply IHl' in H. destruct H as [H | [i' H]].
      * left. apply H.
      * right. exists (S i'). simpl. apply H.
Qed.  

Lemma insert_sorted':
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
  intros a l. generalize dependent l. induction l as [| x l' IHl']; simpl;
  unfold sorted'; intros; destruct i, j; simpl in *; try bdestruct (a <=? x);
  try injection H1 as H1; try injection H2 as H2; subst; try lia;
  try rewrite nth_error_nil in H1; try rewrite nth_error_nil in H2;
  try discriminate.
  - apply Nat.le_trans with x. apply H3. bdestruct (j =? 0).
    + subst. simpl in H2. injection H2 as H2. lia.
    + apply (H 0 j); auto. lia.
  - apply nth_error_insert in H2. destruct H2 as [H2 | [j' H2]].
    + lia.
    + apply (H 0 (S j')); auto. lia.
  - apply (H i j); auto. lia.
  - assert (Hij: i < j). { lia. } 
    eapply IHl'; try (unfold sorted'; intros; apply (H (S i0) (S j0)));
    try apply Hij ; auto. lia.
Qed.
(** [] *)

Theorem sort_sorted': forall l, sorted' (sort l).
Proof.
  induction l.
  - unfold sorted'. intros. destruct i; inv H0.
  - simpl. apply insert_sorted'. auto.
Qed.

(** If you complete the proofs above, you will note that the proof of
    [insert_sorted] is relatively easy compared to the proof of
    [insert_sorted'], even though [sorted al <-> sorted' al].  So,
    suppose someone asked you to prove [sort_sorted'].  Instead of
    proving it directly, it would be much easier to design predicate
    [sorted], then prove [sort_sorted] and [sorted_sorted'].

    The moral of the story is therefore: _Different formulations of
    the functional specification can lead to great differences in the
    difficulty of the correctness proofs_. *)


(* 2026-01-06 11:59 *)
