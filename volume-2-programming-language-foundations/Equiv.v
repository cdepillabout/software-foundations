(** * Equiv: Program Equivalence *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.
From PLF Require Export Imp.

(** *** Before you Get Started:

    - Create a fresh directory for this volume. (Do not try to mix the
      files from this volume with files from _Logical Foundations_ in
      the same directory: the result will not make you happy.)

    - The new directory should contain at least the following files:
         - [Imp.v] (make sure it is the one from the PLF distribution,
           not the one from LF: they are slightly different);
         - [Maps.v] (ditto)
         - [Equiv.v] (this file)
         - [_CoqProject], containing the following line:

           -Q . PLF

    - Reminder: If you see errors like this...

             Compiled library PLF.Maps (in file
             /Users/.../plf/Maps.vo) makes inconsistent assumptions
             over library Coq.Init.Logic

      ... it may mean something went wrong with the above steps.
      Doing "[make clean]" (or manually removing everything except
      [.v] and [_CoqProject] files) may help. *)

(** *** Advice for Working on Exercises:

    - Most of the Coq proofs we ask you to do are similar to proofs
      that we've provided.  Before starting to work on exercises
      problems, take the time to work through our proofs (both
      informally and in Coq) and make sure you understand them in
      detail.  This will save you a lot of time.

    - The Coq proofs we're doing now are sufficiently complicated that
      it is more or less impossible to complete them by random
      experimentation or following your nose.  You need to start with
      an idea about why the property is true and how the proof is
      going to go.  The best way to do this is to write out at least a
      sketch of an informal proof on paper -- one that intuitively
      convinces you of the truth of the theorem -- before starting to
      work on the formal one.  Alternately, grab a friend and try to
      convince them that the theorem is true; then try to formalize
      your explanation.

    - Use automation to save work!  The proofs in this chapter can get
      pretty long if you try to write out all the cases explicitly. *)

(* ################################################################# *)
(** * Behavioral Equivalence *)

(** In an earlier chapter, we investigated the correctness of a very
    simple program transformation: the [optimize_0plus] function.  The
    programming language we were considering was the first version of
    the language of arithmetic expressions -- with no variables -- so
    in that setting it was very easy to define what it means for a
    program transformation to be correct: it should always yield a
    program that evaluates to the same number as the original.

    To talk about the correctness of program transformations for the
    full Imp language, in particular assignment, we need to consider
    the role of variables and state. *)

(* ================================================================= *)
(** ** Definitions *)

(** For [aexp]s and [bexp]s with variables, the definition we want is
    clear: Two [aexp]s or [bexp]s are _behaviorally equivalent_ if
    they evaluate to the same result in every state. *)

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

(** Here are some simple examples of equivalences of arithmetic
    and boolean expressions. *)

Theorem aequiv_example: aequiv <{ X - X }> <{ 0 }>.
Proof.
  intros st. simpl. lia.
Qed.

Theorem bequiv_example: bequiv <{ X - X = 0 }> <{ true }>.
Proof.
  intros st. Print beval. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

(** For commands, the situation is a little more subtle.  We can't
    simply say "two commands are behaviorally equivalent if they
    evaluate to the same ending state whenever they are started in the
    same initial state," because some commands, when run in some
    starting states, don't terminate in any final state at all!  What
    we need instead is this: two commands are behaviorally equivalent
    if, for any given starting state, they either (1) both diverge
    or (2) both terminate in the same final state.  A compact way to
    express this is "if the first one terminates in a particular state
    then so does the second, and vice versa." *)

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

Theorem cequiv_implies_both_diverge :
    forall c1 c2 st, cequiv c1 c2 ->
    (~ (exists st', st =[ c1 ]=> st')) -> 
    ~ (exists st'', st =[ c2 ]=> st'').
Proof.
  unfold cequiv.
  intros c1 c2 st Hceq.
  unfold not. intros Hnostc1 Hstc2.
  destruct Hstc2.
  apply Hnostc1.
  eexists.
  rewrite Hceq.
  eassumption.
  Qed.

(* ================================================================= *)
(** ** Simple Examples *)

(** For examples of command equivalence, let's start by looking at
    some trivial program transformations involving [skip]: *)

Theorem skip_left : forall c,
  cequiv
    <{ skip; c }>
    c.
Proof.
  (* WORKED IN CLASS *)
  intros c st st'.
  split; intros H.
  - (* -> *)
    inversion H. subst.
    inversion H2. subst.
    assumption.
  - (* <- *)
    apply E_Seq with st.
    apply E_Skip.
    assumption.
Qed.

(** **** Exercise: 2 stars, standard (skip_right)

    Prove that adding a [skip] after a command results in an
    equivalent program *)

Theorem skip_right : forall c,
  cequiv
    <{ c ; skip }>
    c.
Proof.
  intros c st st'. split; intros H.
  - inversion H. subst. inversion H5. subst. auto.
  - eapply E_Seq. eassumption. constructor.
  Qed.
(** [] *)

(** Similarly, here is a simple transformation that optimizes [if]
    commands: *)

Theorem if_true_simple : forall c1 c2,
  cequiv
    <{ if true then c1 else c2 end }>
    c1.
Proof.
  intros c1 c2.
  split; intros H.
  - (* -> *)
    inversion H; subst. assumption. discriminate.
  - (* <- *)
    apply E_IfTrue; auto. (* reflexivity. assumption. *)  Qed.

(** Of course, no (human) programmer would write a conditional whose
    guard is literally [true].  But they might write one whose guard
    is _equivalent_ to true:

    _Theorem_: If [b] is equivalent to [true], then [if b then c1
    else c2 end] is equivalent to [c1].
   _Proof_:

     - ([->]) We must show, for all [st] and [st'], that if [st =[
       if b then c1 else c2 end ]=> st'] then [st =[ c1 ]=> st'].

       Proceed by cases on the rules that could possibly have been
       used to show [st =[ if b then c1 else c2 end ]=> st'], namely
       [E_IfTrue] and [E_IfFalse].

       - Suppose the final rule in the derivation of [st =[ if b
         then c1 else c2 end ]=> st'] was [E_IfTrue].  We then have,
         by the premises of [E_IfTrue], that [st =[ c1 ]=> st'].
         This is exactly what we set out to prove.

       - On the other hand, suppose the final rule in the derivation
         of [st =[ if b then c1 else c2 end ]=> st'] was [E_IfFalse].
         We then know that [beval st b = false] and [st =[ c2 ]=> st'].

         Recall that [b] is equivalent to [true], i.e., forall [st],
         [beval st b = beval st <{true}> ].  In particular, this means
         that [beval st b = true], since [beval st <{true}> = true].  But
         this is a contradiction, since [E_IfFalse] requires that
         [beval st b = false].  Thus, the final rule could not have
         been [E_IfFalse].

     - ([<-]) We must show, for all [st] and [st'], that if
       [st =[ c1 ]=> st'] then
       [st =[ if b then c1 else c2 end ]=> st'].

       Since [b] is equivalent to [true], we know that [beval st b] =
       [beval st <{true}> ] = [true].  Together with the assumption that
       [st =[ c1 ]=> st'], we can apply [E_IfTrue] to derive
       [st =[ if b then c1 else c2 end ]=> st'].  []

   Here is the formal version of this proof: *)

Theorem if_true: forall b c1 c2,
  bequiv b <{true}>  ->
  cequiv
    <{ if b then c1 else c2 end }>
    c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - (* -> *)
    inversion H. subst.
    + (* b evaluates to true *)
      assumption.
    + (* b evaluates to false (contradiction) *)
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      discriminate.
  - (* <- *)
    apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    apply Hb. Qed.

(** **** Exercise: 2 stars, standard, especially useful (if_false) *)
Theorem if_false : forall b c1 c2,
  bequiv b <{false}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c2.
Proof.
  unfold bequiv. simpl. intros b c1 c2 Hbeq. split; intro H.
  - inversion H; subst.
    + rewrite Hbeq in H5. discriminate.
    + assumption.
  - apply E_IfFalse; try assumption. apply Hbeq.
  Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (swap_if_branches)

    Show that we can swap the branches of an [if] if we also negate its
    guard. *)

Theorem swap_if_branches : forall b c1 c2,
  cequiv
    <{ if b then c1 else c2 end }>
    <{ if ~ b then c2 else c1 end }>.
Proof.
  intros b c1 c2 st st'. split; intros H; inversion H; subst; simpl in H5.
  - apply E_IfFalse; auto. simpl. rewrite H5. auto.
  - apply E_IfTrue; auto. simpl. rewrite H5. auto.
  - apply E_IfFalse. now apply negb_true_iff in H5. auto.
  - apply E_IfTrue; auto. now rewrite negb_false_iff in H5.
  Qed.
(** [] *)

(** For [while] loops, we can give a similar pair of theorems.  A loop
    whose guard is equivalent to [false] is equivalent to [skip],
    while a loop whose guard is equivalent to [true] is equivalent to
    [while true do skip end] (or any other non-terminating program).
    The first of these facts is easy. *)

Theorem while_false : forall b c,
  bequiv b <{false}> ->
  cequiv
    <{ while b do c end }>
    <{ skip }>.
Proof.
  intros b c Hb. split; intros H.
  - (* -> *)
    inversion H. subst.
    + (* E_WhileFalse *)
      apply E_Skip.
    + (* E_WhileTrue *)
      rewrite Hb in H2. discriminate.
  - (* <- *)
    inversion H. subst.
    apply E_WhileFalse.
    apply Hb.  Qed.

(** **** Exercise: 2 stars, advanced, optional (while_false_informal)

    Write an informal proof of [while_false].

(* IN HERE *)
*)
(** [] *)

(** To prove the second fact, we need an auxiliary lemma stating that
    [while] loops whose guards are equivalent to [true] never
    terminate. *)

(** _Lemma_: If [b] is equivalent to [true], then it cannot be
    the case that [st =[ while b do c end ]=> st'].

    _Proof_: Suppose that [st =[ while b do c end ]=> st'].  We show,
    by induction on a derivation of [st =[ while b do c end ]=> st'],
    that this assumption leads to a contradiction. The only two cases
    to consider are [E_WhileFalse] and [E_WhileTrue], the others
    are contradictory.

    - Suppose [st =[ while b do c end ]=> st'] is proved using rule
      [E_WhileFalse].  Then by assumption [beval st b = false].  But
      this contradicts the assumption that [b] is equivalent to
      [true].

    - Suppose [st =[ while b do c end ]=> st'] is proved using rule
      [E_WhileTrue].  We must have that:

      1. [beval st b = true],
      2. there is some [st0] such that [st =[ c ]=> st0] and
         [st0 =[ while b do c end ]=> st'],
      3. and we are given the induction hypothesis that
         [st0 =[ while b do c end ]=> st'] leads to a contradiction,

      We obtain a contradiction by 2 and 3. [] *)

Lemma while_true_nonterm : forall b c st st',
  bequiv b <{true}> ->
  ~( st =[ while b do c end ]=> st' ).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st' Hb.
  intros H.
  remember <{ while b do c end }> as cw eqn:Heqcw.
  induction H;
  (* Most rules don't apply; we rule them out by inversion: *)
  inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for while loops: *)
  - (* E_WhileFalse *) (* contradictory -- b is always true! *)
    unfold bequiv in Hb.
    (* [rewrite] is able to instantiate the quantifier in [st] *)
    rewrite Hb in H. discriminate.
  - (* E_WhileTrue *) (* immediate from the IH *)
    apply IHceval2. reflexivity.  Qed.
    
Lemma while_true_nonterm2 : forall b c st st',
  bequiv b <{true}> ->
  ~( st =[ while b do c end ]=> st' ).
Proof.
  intros b c st st' Hb.
  intros H.
  remember <{ while b do c end}> eqn:Heqcw.
  induction H; try discriminate.
  - unfold bequiv in Hb. simpl in Hb. inversion Heqcw. subst. rewrite Hb in H. discriminate.
  - now apply IHceval2.
  Qed. 

(** **** Exercise: 2 stars, standard, optional (while_true_nonterm_informal)

    Explain what the lemma [while_true_nonterm] means in English.

(* IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (while_true)

    Prove the following theorem. _Hint_: You'll want to use
    [while_true_nonterm] here. *)

Theorem while_true : forall b c,
  bequiv b <{true}>  ->
  cequiv
    <{ while b do c end }>
    <{ while true do skip end }>.
Proof.
  intros b c Hb st st'.
  unfold bequiv in Hb. simpl in Hb.
  split; intros H; exfalso.
  - apply (while_true_nonterm b c st st' Hb H).
  - apply (while_true_nonterm <{ true }> <{skip}> st st' (fun _ => (@Logic.eq_refl bool true)) H).
  Qed.
(** [] *)

(** A more interesting fact about [while] commands is that any number
    of copies of the body can be "unrolled" without changing meaning.

    Loop unrolling is an important transformation in real compilers! *)

Theorem loop_unrolling : forall b c,
  cequiv
    <{ while b do c end }>
    <{ if b then c ; while b do c end else skip end }>.
Proof.
  (* WORKED IN CLASS *)
  intros b c st st'.
  split; intros Hce.
  - (* -> *)
    inversion Hce; subst.
    + (* loop doesn't run *)
      apply E_IfFalse. assumption. apply E_Skip.
    + (* loop runs *)
      apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  - (* <- *)
    inversion Hce; subst.
    + (* loop runs *)
      inversion H5; subst.
      apply E_WhileTrue with (st' := st'0).
      assumption. assumption. assumption.
    + (* loop doesn't run *)
      inversion H5; subst. apply E_WhileFalse. assumption.  Qed.

(** **** Exercise: 2 stars, standard, optional (seq_assoc) *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv <{(c1;c2);c3}> <{c1;(c2;c3)}>.
Proof.
  intros c1 c2 c3 st st'. split; intros H; inversion H; subst.
  - inversion H2; subst. apply E_Seq with st'1.
    * assumption.
    * apply E_Seq with st'0; assumption.
  - inversion H5. subst. apply E_Seq with st'1.
    * apply E_Seq with st'0; assumption.
    * assumption.
  Qed.
(** [] *)

(** Proving program properties involving assignments is one place
    where the fact that program states are treated
    extensionally (e.g., [x !-> m x ; m] and [m] are equal maps) comes
    in handy. *)

Theorem identity_assignment : forall x,
  cequiv
    <{ x := x }>
    <{ skip }>.
Proof.
  intros.
  split; intro H; inversion H; subst; clear H.
  - (* -> *)
    rewrite t_update_same.
    apply E_Skip.
  - (* <- *)
    assert (Hx : st' =[ x := x ]=> (x !-> st' x ; st')).
    { apply E_Asgn. reflexivity. }
    rewrite t_update_same in Hx.
    apply Hx.
Qed.

(** **** Exercise: 2 stars, standard, especially useful (assign_aequiv) *)
Theorem assign_aequiv : forall (x : string) a,
  aequiv x a ->
  cequiv <{ skip }> <{ x := a }>.
Proof.
  intros x a Ha st st'. unfold aequiv in Ha.
  split; intros H; inversion H; subst; clear H.
  - assert (st' =[ x := a ]=> (x !-> aeval st' a; st')).
    { apply E_Asgn. reflexivity. }
    rewrite <- Ha in H. simpl in H.
    rewrite t_update_same in H.
    assumption.
  - rewrite <- Ha.
    rewrite t_update_same.
    constructor.
  Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (equiv_classes) *)

(** Given the following programs, group together those that are
    equivalent in Imp. Your answer should be given as a list of lists,
    where each sub-list represents a group of equivalent programs. For
    example, if you think programs (a) through (h) are all equivalent
    to each other, but not to (i), your answer should look like this:

       [ [prog_a;prog_b;prog_c;prog_d;prog_e;prog_f;prog_g;prog_h] ;
         [prog_i] ]

    Write down your answer below in the definition of
    [equiv_classes]. *)

Definition prog_a : com :=
  <{ while ~(X <= 0) do
       X := X + 1
     end }>.

Definition prog_b : com :=
  <{ if (X = 0) then
       X := X + 1;
       Y := 1
     else
       Y := 0
     end;
     X := X - Y;
     Y := 0 }>.

Definition prog_c : com :=
  <{ skip }> .

Definition prog_d : com :=
  <{ while ~(X = 0) do
       X := (X * Y) + 1
     end }>.

Definition prog_e : com :=
  <{ Y := 0 }>.

Definition prog_f : com :=
  <{ Y := X + 1;
     while ~(X = Y) do
       Y := X + 1
     end }>.

Definition prog_g : com :=
  <{ while true do
       skip
     end }>.

Definition prog_h : com :=
  <{ while ~(X = X) do
       X := X + 1
     end }>.

Definition prog_i : com :=
  <{ while ~(X = Y) do
       X := Y + 1
     end }>.

Definition equiv_classes : list (list com)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(* Do not modify the following line: *)
Definition manual_grade_for_equiv_classes : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Properties of Behavioral Equivalence *)

(** We next consider some fundamental properties of program
    equivalence. *)

(* ================================================================= *)
(** ** Behavioral Equivalence Is an Equivalence *)

(** First, we verify that the equivalences on [aexps], [bexps], and
    [com]s really are _equivalences_ -- i.e., that they are reflexive,
    symmetric, and transitive.  The proofs are all easy. *)

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  intros a st. reflexivity.  Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.  Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  unfold cequiv. intros c st st'. reflexivity.  Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  rewrite H. reflexivity.
Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  rewrite H12. apply H23.
Qed.

(* ================================================================= *)
(** ** Behavioral Equivalence Is a Congruence *)

(** Less obviously, behavioral equivalence is also a _congruence_.
    That is, the equivalence of two subprograms implies the
    equivalence of the larger programs in which they are embedded:

                 aequiv a a'
         -------------------------
         cequiv (x := a) (x := a')

              cequiv c1 c1'
              cequiv c2 c2'
         --------------------------
         cequiv (c1;c2) (c1';c2')

    ... and so on for the other forms of commands. *)

(** (Note that we are using the inference rule notation here not
    as part of a definition, but simply to write down some valid
    implications in a readable format. We prove these implications
    below.) *)

(** We will see a concrete example of why these congruence
    properties are important in the following section (in the proof of
    [fold_constants_com_sound]), but the main idea is that they allow
    us to replace a small part of a large program with an equivalent
    small part and know that the whole large programs are equivalent
    _without_ doing an explicit proof about the non-varying parts --
    i.e., the "proof burden" of a small change to a large program is
    proportional to the size of the change, not the program. *)

Theorem CAsgn_congruence : forall x a a',
  aequiv a a' ->
  cequiv <{x := a}> <{x := a'}>.
Proof.
  intros x a a' Heqv st st'.
  split; intros Hceval.
  - (* -> *)
    inversion Hceval. subst. apply E_Asgn.
    rewrite Heqv. reflexivity.
  - (* <- *)
    inversion Hceval. subst. apply E_Asgn.
    rewrite Heqv. reflexivity.  Qed.

(** The congruence property for loops is a little more interesting,
    since it requires induction.

    _Theorem_: Equivalence is a congruence for [while] -- that is, if
    [b] is equivalent to [b'] and [c] is equivalent to [c'], then
    [while b do c end] is equivalent to [while b' do c' end].

    _Proof_: Suppose [b] is equivalent to [b'] and [c] is
    equivalent to [c'].  We must show, for every [st] and [st'], that
    [st =[ while b do c end ]=> st'] iff [st =[ while b' do c'
    end ]=> st'].  We consider the two directions separately.

      - ([->]) We show that [st =[ while b do c end ]=> st'] implies
        [st =[ while b' do c' end ]=> st'], by induction on a
        derivation of [st =[ while b do c end ]=> st'].  The only
        nontrivial cases are when the final rule in the derivation is
        [E_WhileFalse] or [E_WhileTrue].

          - [E_WhileFalse]: In this case, the form of the rule gives us
            [beval st b = false] and [st = st'].  But then, since
            [b] and [b'] are equivalent, we have [beval st b' =
            false], and [E_WhileFalse] applies, giving us
            [st =[ while b' do c' end ]=> st'], as required.

          - [E_WhileTrue]: The form of the rule now gives us [beval st
            b = true], with [st =[ c ]=> st'0] and [st'0 =[ while
            b do c end ]=> st'] for some state [st'0], with the
            induction hypothesis [st'0 =[ while b' do c' end ]=>
            st'].

            Since [c] and [c'] are equivalent, we know that [st =[
            c' ]=> st'0].  And since [b] and [b'] are equivalent,
            we have [beval st b' = true].  Now [E_WhileTrue] applies,
            giving us [st =[ while b' do c' end ]=> st'], as
            required.

      - ([<-]) Similar. [] *)

Theorem CWhile_congruence : forall b b' c c',
  bequiv b b' -> cequiv c c' ->
  cequiv <{ while b do c end }> <{ while b' do c' end }>.
Proof.
  (* WORKED IN CLASS *)

  (* We will prove one direction in an "assert"
     in order to reuse it for the converse. *)
  assert (A: forall (b b' : bexp) (c c' : com) (st st' : state),
             bequiv b b' -> cequiv c c' ->
             st =[ while b do c end ]=> st' ->
             st =[ while b' do c' end ]=> st').
  { unfold bequiv,cequiv.
    intros b b' c c' st st' Hbe Hc1e Hce.
    remember <{ while b do c end }> as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileFalse *)
      apply E_WhileFalse. rewrite <- Hbe. apply H.
    + (* E_WhileTrue *)
      apply E_WhileTrue with (st' := st').
      * (* show loop runs *) rewrite <- Hbe. apply H.
      * (* body execution *)
        apply (Hc1e st st').  apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity. }

  intros. split.
  - apply A; assumption.
  - apply A.
    + apply sym_bequiv. assumption.
    + apply sym_cequiv. assumption.
Qed.

(** **** Exercise: 3 stars, standard, optional (CSeq_congruence) *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ c1;c2 }> <{ c1';c2' }>.
Proof.
  unfold cequiv. intros c1 c1' c2 c2' Hc1 Hc2 st st'. split; intros H; inversion H; subst.
  - apply Hc1 in H2. apply Hc2 in H5. apply E_Seq with st'0; assumption.
  - apply Hc1 in H2. apply Hc2 in H5. apply E_Seq with st'0; assumption.
  Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (CIf_congruence) *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ if b then c1 else c2 end }>
         <{ if b' then c1' else c2' end }>.
Proof.
  unfold cequiv. unfold bequiv. intros b b' c1 c1' c2 c2' Hb Hc1 Hc2 st st'. split; intros H; inversion H; subst.
  - rewrite Hb in H5. rewrite Hc1 in H6. apply E_IfTrue; assumption.
  - rewrite Hb in H5. rewrite Hc2 in H6. apply E_IfFalse; assumption.
  - rewrite <- Hb in H5. rewrite <- Hc1 in H6. apply E_IfTrue; assumption.
  - rewrite <- Hb in H5. rewrite <- Hc2 in H6. apply E_IfFalse; assumption.
  Qed.

(** [] *)

(** For example, here are two equivalent programs and a proof of their
    equivalence... *)

Example congruence_example:
  cequiv
    (* Program 1: *)
    <{ X := 0;
       if (X = 0)
       then
         Y := 0
       else
         Y := 42
       end }>
    (* Program 2: *)
    <{ X := 0;
       if (X = 0)
       then
         Y := X - X   (* <--- Changed here *)
       else
         Y := 42
       end }>.
Proof.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CIf_congruence.
    + apply refl_bequiv.
    + apply CAsgn_congruence. unfold aequiv. simpl.
      symmetry. apply minus_diag.
    + apply refl_cequiv.
Qed.

Print ceval.

(* This doesn't actually make any sense *)

Inductive ccongru : com -> com -> Prop :=
  | Congru_Skip : ccongru <{ skip }> <{ skip }>
  | Congru_Asgn : forall a a' x, aequiv a a' -> ccongru <{x := a }> <{x := a'}>
  | Congru_Seq : forall c1 c1' c2 c2', ccongru c1 c1' -> ccongru c2 c2' -> ccongru <{ c1;c2 }> <{ c1';c2' }>
  | Congru_If : forall b b' c1 c1' c2 c2',
      bequiv b b' -> ccongru c1 c1' -> ccongru c2 c2' ->
      ccongru <{ if b then c1 else c2 end }> <{ if b' then c1' else c2' end }>
  | Congru_While : forall b b' c c',
      bequiv b b' -> ccongru c c' -> ccongru <{ while b do c end }> <{ while b' do c' end }>
  .

Theorem congru_is_equiv : forall c1 c2, ccongru c1 c2 -> cequiv c1 c2.
Proof.
  intros c1 c2 Hcongru.
  induction Hcongru; subst.
  - (* skip *) unfold cequiv. split; intros; assumption.
  - (* assign *) apply CAsgn_congruence; assumption.
  - (* seq *) apply CSeq_congruence; assumption.
  - (* if *) apply CIf_congruence; assumption.
  - (* while *) apply CWhile_congruence; assumption.
  Qed. 
  
Example congruence_example2:
  ccongru
    (* Program 1: *)
    <{ X := 0;
       if (X = 0)
       then
         Y := 0
       else
         Y := 42
       end }>
    (* Program 2: *)
    <{ X := 0;
       if (X = 0)
       then
         Y := X - X   (* <--- Changed here *)
       else
         Y := 42
       end }>.
Proof.
  apply Congru_Seq. apply Congru_Asgn. apply refl_aequiv.
  apply Congru_If. apply refl_bequiv.
  - apply Congru_Asgn.
    unfold aequiv. simpl. lia.
  - apply Congru_Asgn. apply refl_aequiv.
  Qed.

Print aequiv.

Inductive crec (af : aexp -> aexp -> Type) (bf : bexp -> bexp -> Type): com -> com -> Prop :=
  | CRec_Skip : crec af bf <{ skip }> <{ skip }>
  | CRec_Asgn : forall a a' x, af a a' -> crec af bf <{x := a }> <{x := a'}>
  | CRec_Seq : forall c1 c1' c2 c2', crec af bf c1 c1' -> crec af bf c2 c2' -> crec af bf <{ c1;c2 }> <{ c1';c2' }>
  | CRec_If : forall b b' c1 c1' c2 c2',
      bf b b' -> crec af bf c1 c1' -> crec af bf c2 c2' ->
      crec af bf <{ if b then c1 else c2 end }> <{ if b' then c1' else c2' end }>
  | CRec_While : forall b b' c c',
      bf b b' -> crec af bf c c' -> crec af bf <{ while b do c end }> <{ while b' do c' end }>
  .
  
Check crec_ind.  
  
  
Theorem congru_is_equiv2 : forall c1 c2, crec aequiv bequiv c1 c2 -> cequiv c1 c2.
Proof.
  (*
  intros c1 c2 Hcongru.
  remember aequiv eqn:V.
  remember bequiv eqn:X.
  (* remember (aequiv bequiv c1 c2) eqn:E. *)
  induction Hcongru; subst.
  *)
  intros c1 c2 Hcongru.
  induction Hcongru.
  - (* skip *) unfold cequiv. split; intros; assumption.
  - (* assign *) apply CAsgn_congruence; assumption.
  - (* seq *) apply CSeq_congruence; assumption.
  - (* if *) apply CIf_congruence; assumption.
  - (* while *) apply CWhile_congruence; assumption.
  Qed. 

From Coq Require Import FunctionalExtensionality.

Theorem eqb_string_sym: forall x y, eqb_string x y = eqb_string y x.
Proof.
  Check string_dec.
  intros x y.
  (* destruct (Coq.Strings.String.eqb_spec x y).
  - rewrite e. reflexivity.
  - *)
  destruct (string_dec x y).
  - rewrite e. reflexivity.
  - assert (eqb_string x y = false).
    { destruct (eqb_string_false_iff x y).
      apply H0 in n. assumption.
    }
    assert (eqb_string y x = false).
    { destruct (eqb_string_false_iff y x).
      apply H1. unfold not in *. intro. apply n. symmetry. assumption.
    }
    rewrite H,H0. reflexivity.
  Qed.

(*
Theorem all_from_skip: forall x a, (forall st st' : state, st =[ skip ]=> st' -> st =[ x := a ]=> st') -> False.
Proof.
  (* intros x a H.
  set (my_state := t_empty 0).
  assert (my_state =[ x := a ]=> my_state).
  { apply H. apply E_Skip. }
  inversion H0; subst.
  Print functional_extensionality.
  Print Coq.Logic.FunctionalExtensionality.
  set (blah := equal_f H5).
  apply equal_f in H5.
  *)
  (* TODO!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  Try destructing or inverting on aeval a, and based on whether that is 0 or greater
  than zero, I pick a starting state that will make the function passed in fail!
  *)
  intros x a.
  (* destruct (aeval a) eqn:E.*)
  induction a.
  - destruct n.
    + intro H. set (my_state := t_empty 1).
      assert (my_state =[ x := 0 ]=> my_state).
      { apply H. constructor. }
      inversion H0; subst.
      simpl in H4. subst.
      set (blah := equal_f H5).
      specialize (blah x).
      unfold t_update in blah.
      unfold my_state in blah. unfold t_empty in blah.
      Search (eqb_string _ _).
      rewrite <- eqb_string_refl in blah.
      discriminate.
    + intro H. set (my_state := t_empty 0).
      assert (my_state =[ x := (S n) ]=> my_state).
      { apply H. constructor. }
      inversion H0; subst.
      simpl in H4. subst.
      set (blah := equal_f H5).
      specialize (blah x).
      unfold t_update in blah.
      unfold my_state in blah. unfold t_empty in blah.
      rewrite <- eqb_string_refl in blah.
      discriminate.
  - intro H.
    About t_update.
    Print PLF.Maps.
    set (my_state := (x0 !-> 1; _ !-> 0)).
    assert (my_state =[ x := x0 ]=> my_state).
    { apply H. constructor. }
    inversion H0; subst.
    Print ceval.
    unfold my_state in H5.
    unfold aeval in H4.
    unfold my_state in H4. unfold t_update in H4.
    rewrite <- eqb_string_refl in H4.
    unfold t_update in H5.
    unfold t_empty in H5.
    set (blah := equal_f H5 x); simpl in blah.
    rewrite <- eqb_string_refl in blah.
    subst.
    rewrite eqb_string_sym in H4.
    assert (eqb_string x x0 -> eqb_string x0 x)
    simpl in H4.
    unfold t_update in H4,blah. unfold my_state in H4. unfold t_update in H4. rewrite <- eqb_string_refl in H4.
    unfold my_state in blah. unfold t_update in blah. unfold t_empty in blah.
    rewrite <- eqb_string_refl in blah.
    specialize (blah x).
    unfold t_update in blah.

Theorem congru_is_equiv3 : forall c1 c2, cequiv c1 c2 -> crec aequiv bequiv c1 c2.
Proof.
  unfold cequiv.
  intros c1 c2 Hequiv. destruct c1,c2.
  - constructor.
  - Print state. Print total_map.
    About t_empty.
    
    About total_map.
    Print PLF.Maps.
    Print t_empty.
    Check t_empty 0.
    exfalso.
    About state.
    Print PLF.Imp.state.
    About total_map.
    specialize (Hequiv (t_empty 0) (t_empty 0)).
    destruct Hequiv.
    specialize (H (E_Skip (_ !-> 0))).
    inversion H; subst. simpl in H4.
*)


(** **** Exercise: 3 stars, advanced, optional (not_congr)

    We've shown that the [cequiv] relation is both an equivalence and
    a congruence on commands.  Can you think of a relation on commands
    that is an equivalence but _not_ a congruence? *)

Definition cequiv_one_state (c1 c2 : com) : Prop :=
  (t_empty 0 =[ c1 ]=> t_empty 0) <-> (t_empty 0 =[ c2 ]=> t_empty 0).

Theorem skip_left_one_state : forall c,
  cequiv_one_state
    <{ skip; c }>
    c.
Proof.
  (* WORKED IN CLASS *)
  intros c.
  split; intros H.
  - (* -> *)
    inversion H. subst.
    inversion H2. subst.
    assumption.
  - (* <- *)
    apply E_Seq with (t_empty 0).
    apply E_Skip.
    assumption.
Qed.

Lemma refl_cequiv_one_state : forall (c : com), cequiv_one_state c c.
Proof.
  unfold cequiv_one_state. intros c. reflexivity.  Qed.

Lemma sym_cequiv_one_state : forall (c1 c2 : com),
  cequiv_one_state c1 c2 -> cequiv_one_state c2 c1.
Proof.
  unfold cequiv_one_state. intros c1 c2 H.
  rewrite H. reflexivity.
Qed.

Lemma trans_cequiv_one_state : forall (c1 c2 c3 : com),
  cequiv_one_state c1 c2 -> cequiv_one_state c2 c3 -> cequiv_one_state c1 c3.
Proof.
  unfold cequiv_one_state. intros c1 c2 c3 H12 H23.
  rewrite H12. apply H23.
Qed.

Theorem CAsgn_congruence_one_state : forall x a a',
  aequiv a a' ->
  cequiv_one_state <{x := a}> <{x := a'}>.
Proof.
  intros x a a' Heqv.
  split; intros Hceval.
  - (* -> *)
    inversion Hceval. subst.
    unfold aequiv in Heqv.
    rewrite (Heqv _) in H2.
    rewrite H3 at 1.
    apply E_Asgn.
    rewrite H3 in H2.
    assumption.
  - (* <- *)
    Admitted.

Inductive c_le_2 : nat -> com -> Prop :=
    E_Le_2_Skip : c_le_2 1 <{ skip }>
  | E_Le_2_Asgn : forall (a : aexp) (x : string), c_le_2 1 <{ x := a }>
  | E_Le_2_Seq : forall n m (c1 c2 : com), c_le_2 n c1 -> c_le_2 m c2 -> n + m <= 2 -> c_le_2 (n + m) <{ c1; c2 }>
  | E_Le_2_If : forall (b : bexp) (c1 c2 : com), c_le_2 1 <{ if b then c1 else c2 end }>
  .

Definition cequiv_le_2 n (c1 c2 : com) : Prop :=
  c_le_2 n c1 <-> c_le_2 n c2.

Theorem skip_left_le_2 : forall x a,
  cequiv_le_2 1
    <{ skip }>
    <{ x := a }>.
Proof.
  (* WORKED IN CLASS *)
  intros c.
  split; intros H.
  - (* -> *)
    constructor.
  - (* <- *)
    constructor.
Qed.

Lemma refl_cequiv_le_2 : forall n (c : com), cequiv_le_2 n c c.
Proof.
  unfold cequiv_le_2. intros c. reflexivity.  Qed.

Lemma sym_cequiv_le_2 : forall n (c1 c2 : com),
  cequiv_le_2 n c1 c2 -> cequiv_le_2 n c2 c1.
Proof.
  unfold cequiv_le_2. intros n c1 c2 H.
  rewrite H. reflexivity.
Qed.

Lemma trans_cequiv_le_2 : forall n (c1 c2 c3 : com),
  cequiv_le_2 n c1 c2 -> cequiv_le_2 n c2 c3 -> cequiv_le_2 n c1 c3.
Proof.
  unfold cequiv_le_2. intros n c1 c2 c3 H12 H23.
  rewrite H12. apply H23.
Qed.

Theorem n_le_2_cequiv_thing : forall n c, c_le_2 n c -> n <= 2.
Proof.
  intros n c H.
  inversion H; subst; try lia.
  Qed.

(* It looks like I am not able to write a congruence here.  Don't know if this is a "legitimate" congruence though. *)

(*
Theorem CSeq_congruence_le_2 : forall n c1 c1' c2 c2',
  cequiv_le_2 n c1 c1' -> cequiv_le_2 n c2 c2' ->
  cequiv_le_2 n <{ c1;c2 }> <{ c1';c2' }>.
Proof.
  unfold cequiv_le_2.
  intros n c1 c1' c2 c2' Hequiv1 Hequiv2.
  destruct Hequiv1,Hequiv2.
  split; intro H3; set (G := n_le_2_cequiv_thing _ _ H3); induction H3.
  - destruct n0,m; simpl in *.
    * 
  
   apply E_Le_2_Seq.
    *
*)

From Coq Require Import Lists.ListSet.

Print set.
Check empty_set.
Check set_add string_dec.

Print eqb_string.
Check string_dec.

Inductive c_vars_set : com -> set string -> Prop :=
  | E_Vars_Set_Skip : c_vars_set <{ skip }> (@empty_set string)
  | E_Vars_Set_Asgn : 
      forall (a : aexp) (x : string), c_vars_set <{ x := a }> (set_add string_dec x (@empty_set string))
  | E_Vars_Set_Seq :
      forall (c1 c2 : com) s1 s2, c_vars_set c1 s1 -> c_vars_set c2 s2 ->
      c_vars_set <{ c1; c2 }> (set_union string_dec s1 s2)
  .
  
Definition cequiv_same_vars_set (c1 c2 : com) : Prop :=
  forall vs, c_vars_set c1 vs <-> c_vars_set c2 vs.

Theorem set_add_empty_is_singleton : forall A (x : A) f, set_add f x (empty_set A) = [x].
Proof.
  unfold empty_set. unfold set_add. reflexivity.
Qed.

Theorem skip_same_vars : forall x a,
  cequiv_same_vars_set
    <{ skip; x := a }>
    <{ x := a }>.
Proof.
  intros x a.
  split; intros H; inversion H; subst.
  - (* -> *)
    (* TODO: HERE??? *)
    inversion H2; subst. inversion H4; subst.
    unfold set_union in *.
    rewrite set_add_empty_is_singleton in *.
    unfold empty_set in *.
    unfold set_add in *. assumption.
  - (* <- *)
    replace (set_add string_dec x (empty_set string))
      with (set_union string_dec (@empty_set string) (set_add string_dec x (empty_set string))).
    * constructor. constructor. assumption.
    * unfold set_union. unfold empty_set. unfold set_add. reflexivity.
  Qed. 


Lemma refl_cequiv_same_vars_set : forall (c : com), cequiv_same_vars_set c c.
Proof.
  unfold cequiv_same_vars_set. intros c. reflexivity.  Qed.

Lemma sym_cequiv_same_vars_set : forall (c1 c2 : com),
  cequiv_same_vars_set c1 c2 -> cequiv_same_vars_set c2 c1.
Proof.
  unfold cequiv_same_vars_set. intros c1 c2 H vs. specialize (H vs).
  rewrite H. reflexivity.
Qed.

Lemma trans_cequiv_same_vars_set : forall (c1 c2 c3 : com),
  cequiv_same_vars_set c1 c2 -> cequiv_same_vars_set c2 c3 -> cequiv_same_vars_set c1 c3.
Proof.
  unfold cequiv_same_vars_set. intros c1 c2 c3 H12 H23 vs.
  specialize (H12 vs); specialize (H23 vs).
  rewrite H12. apply H23.
Qed.

Theorem CSeq_congruence_le_2 : forall c1 c1' c2 c2',
  cequiv_same_vars_set c1 c1' -> cequiv_same_vars_set c2 c2' ->
  cequiv_same_vars_set <{ c1;c2 }> <{ c1';c2' }>.
Proof.
  unfold cequiv_same_vars_set.
  intros c1 c1' c2 c2' Hc1 Hc2 vs. split; intros H; inversion H; subst.
  - specialize (Hc1 s1); specialize (Hc2 s2). apply Hc1 in H2; apply Hc2 in H4.
    constructor; assumption.
  - specialize (Hc1 s1); specialize (Hc2 s2). apply Hc1 in H2; apply Hc2 in H4.
    constructor; assumption.
  Qed.


(*  IN HERE *)


    
Definition var_swap: Type := (string * string).

Print t_update.
Check t_update_eq : forall (A : Type) (m : total_map A) (x : string) (v : A), (x !-> v; m) x = v.
Check t_update_neq : forall (A : Type) (m : total_map A) (x1 x2 : string) (v : A),
  x1 <> x2 -> (x1 !-> v; m) x2 = m x2.
Check t_update_same : forall (A : Type) (m : total_map A) (x : string), (x !-> m x; m) = m.
Check t_update_shadow : forall (A : Type) (m : total_map A) (x : string) (v1 v2 : A),
  (x !-> v2; x !-> v1; m) = (x !-> v2; m).
Check t_update_permute : forall (A : Type) (m : total_map A) (v1 v2 : A) (x1 x2 : string),
  x2 <> x1 -> (x1 !-> v1; x2 !-> v2; m) = (x2 !-> v2; x1 !-> v1; m).

Definition swap_vars (vs : var_swap) (s : state): state :=
  match vs with
  | (renameA, renameB) =>
      (renameA !-> s renameB; renameB !-> s renameA; s)
  end.

Example y_test_1:  (Y !-> 3; _ !-> 0) Y = 3. Proof. reflexivity. Qed.
Example y_test_2:  (Y !-> 3; _ !-> 0) X = 0. Proof. reflexivity. Qed.
Example swap_x_test_1:  (swap_vars (X,Y) (X !-> 3; _ !-> 0)) X = 0. Proof. reflexivity. Qed.
Example swap_x_test_2:  (swap_vars (X,Y) (X !-> 3; _ !-> 0)) Y = 3. Proof. reflexivity. Qed.

Theorem t_update_same_as_empty : forall (x : string) (n : nat), (x !-> n; _ !-> n) = (_ !-> n).
Proof.
  intros x n. unfold t_empty. unfold t_update. apply functional_extensionality.
  intros y.
  destruct (eqb_string x y); reflexivity.
Qed.

Theorem unwind_e_asgn : forall x a n st, aeval st a = n ->
  st =[ x := a ]=> (x !-> aeval st a; st).
Proof.
  intros x a n st H. rewrite H. now apply E_Asgn.
Qed. 

Example ceval_swap_example1 : forall a st, st =[ X := a ]=> (X !-> aeval st a; st).
Proof. intros a st. constructor. reflexivity. Qed.

Example ceval_swap_example2 : t_empty 0 =[ X := 3 ]=> swap_vars (X,Y) (Y !-> 3; _ !-> 0).
Proof.
  unfold swap_vars.
  rewrite t_update_eq. rewrite t_update_shadow.
  rewrite t_update_neq.
  - replace ((_ !-> 0) X) with 0 by reflexivity.
    rewrite t_update_same_as_empty. constructor. reflexivity.
  - unfold not. intro H. discriminate.
  Qed.
  
Example ceval_swap_example2' : forall a st, 
  st =[ X := a ]=> swap_vars (X,Y) (Y !-> aeval st a; X !-> st Y; st).
Proof.
  unfold swap_vars.
  intros a st.
  rewrite t_update_eq.
  rewrite t_update_shadow.
  rewrite t_update_permute by (intros; discriminate).
  rewrite t_update_shadow.
  rewrite t_update_neq by (intro; discriminate).
  rewrite t_update_eq.
  rewrite t_update_permute by (intros; discriminate).
  rewrite t_update_same.
  now constructor.
  Qed.
  
Example ceval_swap_example3 : t_empty 0 =[ Y := 3 ]=> (Y !-> 3; _ !-> 0).
Proof. constructor. reflexivity. Qed.
  
Example ceval_swap_example4 : t_empty 0 =[ Y := 3 ]=> swap_vars (X,Y) (X !-> 3; _ !-> 0).
Proof.
  unfold swap_vars.
  rewrite t_update_eq.
  rewrite t_update_permute.
  * rewrite t_update_neq.
    - rewrite t_update_shadow. replace ((_ !-> 0) Y) with 0 by (reflexivity).
      rewrite t_update_same_as_empty. constructor. reflexivity.
    - intro H. discriminate.
  * intro H. discriminate.
  Qed.

Print ceval_swap_example4.

Print ceval. Print state.

Definition cequiv_under_var_swaps (c1 c2 : com) : Prop :=
  exists x y, forall st st',
  st =[ c1 ]=> swap_vars (x,y) st' <-> st =[ c2 ]=> (x !-> st' y; st').








Fixpoint swap_id_aexp (x y : string) (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId str => if eqb_string x str then AId y else AId str
  | APlus b c => APlus (swap_id_aexp x y b) (swap_id_aexp x y c)
  | AMinus b c => AMinus (swap_id_aexp x y b) (swap_id_aexp x y c)
  | AMult b c => AMult (swap_id_aexp x y b) (swap_id_aexp x y c)
  end.

Fixpoint swap_id_bexp (x y : string) (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a a' => BEq (swap_id_aexp x y a) (swap_id_aexp x y a')
  | BLe a a' => BLe (swap_id_aexp x y a) (swap_id_aexp x y a')
  | BNot b' => BNot (swap_id_bexp x y b')
  | BAnd b1 b2 => BAnd (swap_id_bexp x y b1) (swap_id_bexp x y b2)
  end.

Fixpoint swap_id_com (x y : string) (c : com) : com :=
  match c with
  | CSkip => CSkip
  | CAsgn str a => if eqb_string x str then CAsgn y (swap_id_aexp x y a) else CAsgn str (swap_id_aexp x y a)
  | CSeq c1 c2 => CSeq (swap_id_com x y c1) (swap_id_com x y c2)
  | CIf b c1 c2 => CIf (swap_id_bexp x y b) (swap_id_com x y c1) (swap_id_com x y c2)
  | CWhile b c' => CWhile (swap_id_bexp x y b) (swap_id_com x y c')
  end.
  
Fixpoint no_vars (a : aexp): Prop :=
  match a with
  | ANum n => True
  | AId str => False
  | APlus b c => no_vars b /\ no_vars c
  | AMinus b c => no_vars b /\ no_vars c
  | AMult b c => no_vars b /\ no_vars c
  end.
  
Theorem no_vars_under_plus : forall a1 a2, no_vars a1 -> no_vars a2 -> no_vars (APlus a1 a2).
Proof.
  intros a1 a2 Hnoa1 Hnoa2. unfold no_vars. fold no_vars. split; assumption.
Qed.

(* no_vars <{ c1 + c2 }> -> no_vars c1 /\ no_vars c2. *)
  
Theorem swap_id_is_no_op_when_no_vars : forall x y c, no_vars c -> swap_id_aexp x y c = c.
Proof.
  intros x y c. induction c. 
  - simpl. reflexivity.
  - simpl. intros. destruct H.
  - unfold swap_id_aexp. fold swap_id_aexp.
    intros Hno_both. unfold no_vars in Hno_both. fold no_vars in Hno_both. destruct Hno_both as [HHH FFF].
    apply IHc1 in HHH. apply IHc2 in FFF. rewrite HHH. now rewrite FFF.
  - unfold swap_id_aexp. fold swap_id_aexp.
    intros Hno_both. unfold no_vars in Hno_both. fold no_vars in Hno_both. destruct Hno_both as [HHH FFF].
    apply IHc1 in HHH. apply IHc2 in FFF. rewrite HHH. now rewrite FFF.
  - unfold swap_id_aexp. fold swap_id_aexp.
    intros Hno_both. unfold no_vars in Hno_both. fold no_vars in Hno_both. destruct Hno_both as [HHH FFF].
    apply IHc1 in HHH. apply IHc2 in FFF. rewrite HHH. now rewrite FFF.
  Qed.
  
Definition cequiv_under_id_change (c1 c2 : com) : Prop :=
  exists x y, swap_id_com x y c1 = c2.

Check eqb_string.

Theorem if_not_known : forall {A} (b : bool) (n m z : A),
  (if b then n else m) = z -> ~(m = z) -> b = true /\ n = z.
Proof.
  intros A b n m z. destruct b.
  - intros. split; auto.
  - intros. unfold not in H0. apply H0 in H. destruct H.
  Qed. 

Theorem simple_id_change : forall a,
  no_vars a ->
  cequiv_under_id_change
    <{ X := a }>
    <{ Y := a }>.
Proof.
  
  unfold cequiv_under_id_change.
  induction a; intros H; exists X,Y.
  - reflexivity.
  - destruct H.
  - destruct H.
    specialize (IHa1 H); destruct IHa1. destruct H1.
    specialize (IHa2 H0); destruct IHa2. destruct H2.
    unfold swap_id_com.
    rewrite <- eqb_string_refl.
    assert (no_vars <{ a1 + a2 }>).
    { apply no_vars_under_plus; assumption. }
    rewrite (swap_id_is_no_op_when_no_vars X Y _ H3).
    reflexivity.
  - destruct H.
    specialize (IHa1 H); destruct IHa1. destruct H1.
    specialize (IHa2 H0); destruct IHa2. destruct H2.
    unfold swap_id_com.
    rewrite <- eqb_string_refl.
    assert (no_vars <{ a1 - a2 }>).
    { unfold no_vars. fold no_vars. split; assumption. }
    now rewrite (swap_id_is_no_op_when_no_vars X Y _ H3).
  - destruct H.
    specialize (IHa1 H); destruct IHa1. destruct H1.
    specialize (IHa2 H0); destruct IHa2. destruct H2.
    unfold swap_id_com.
    rewrite <- eqb_string_refl.
    assert (no_vars <{ a1 * a2 }>).
    { unfold no_vars. fold no_vars. split; assumption. }
    now rewrite (swap_id_is_no_op_when_no_vars X Y _ H3).
  Qed.

Theorem swap_id_aexp_same : forall x a, swap_id_aexp x x a = a.
Proof.
  intros x a. induction a; try reflexivity.
  - unfold swap_id_aexp. unfold eqb_string. remember (string_dec x x0) as cw.
    destruct cw.
    * now rewrite e.
    * reflexivity.
  - unfold swap_id_aexp. fold swap_id_aexp. now rewrite IHa1,IHa2. 
  - unfold swap_id_aexp. fold swap_id_aexp. now rewrite IHa1,IHa2. 
  - unfold swap_id_aexp. fold swap_id_aexp. now rewrite IHa1,IHa2. 
  Qed.
  
Theorem swap_id_bexp_same : forall x b, swap_id_bexp x x b = b.
Proof.
  intros x b.
  induction b; try reflexivity;
  try
    ( unfold swap_id_bexp;
      fold swap_id_bexp;
      rewrite swap_id_aexp_same;
      rewrite swap_id_aexp_same
    );
  try reflexivity.
  - unfold swap_id_bexp. fold swap_id_bexp. now rewrite IHb.
  - unfold swap_id_bexp. fold swap_id_bexp. now rewrite IHb1,IHb2. 
  Qed.

Theorem swap_id_com_same : forall x c, swap_id_com x x c = c.
Proof.
  intros x c.
  induction c;
  try
    ( unfold swap_id_com;
      fold swap_id_com
      (* rewrite swap_id_aexp_same;
      rewrite swap_id_aexp_same *)
    );
  try reflexivity;
  try rewrite swap_id_bexp_same;
  try rewrite swap_id_aexp_same;
  subst.
  - destruct (eqb_string x x0) eqn:E.
    * apply eqb_string_true_iff in E; now subst. 
    * reflexivity.
  - now rewrite IHc1,IHc2.
  - now rewrite IHc1,IHc2.
  - now rewrite IHc.
  Qed.

Lemma refl_cequiv_under_id_change : forall (c : com), cequiv_under_id_change c c.
Proof.
  unfold cequiv_under_id_change. intros c. exists X,X.
  now rewrite swap_id_com_same.
  Qed.

(* Lemma double_swap_aexp : forall x y, swap_id_aexp x y (swap_id_aexp y x a). *)

(*

Lemma sym_cequiv_under_id_change : forall (c1 c2 : com),
  cequiv_under_id_change c1 c2 -> cequiv_under_id_change c2 c1.
Proof.
  unfold cequiv_under_id_change. intros c1 c2 H.
  destruct H as [x [y H]]. exists y,x.
  unfold swap_id_com in H. induction c1; subst.
  - unfold swap_id_com. reflexivity.
  - destruct (eqb_string x x0) eqn:E.
    * apply eqb_string_true_iff in E. subst.
      unfold swap_id_com. rewrite <- eqb_string_refl.
Qed.



Lemma trans_cequiv_same_vars_set : forall (c1 c2 c3 : com),
  cequiv_same_vars_set c1 c2 -> cequiv_same_vars_set c2 c3 -> cequiv_same_vars_set c1 c3.
Proof.
  unfold cequiv_same_vars_set. intros c1 c2 c3 H12 H23 vs.
  specialize (H12 vs); specialize (H23 vs).
  rewrite H12. apply H23.
Qed.

*)

Module FreeCEquiv.

Inductive cequiv: com -> com -> Prop :=
  | CEquivRefl : forall c, cequiv c c
  | CEquivSym : forall c1 c2, cequiv c2 c1 -> cequiv c1 c2
  | CEquivTrans : forall c1 c2 c3, cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3
  | CEquivSwap : forall x y c1 c2, swap_id_com x y c1 = c2 -> cequiv c1 c2
  .


Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof. constructor. Qed.

Lemma sym_cequiv : forall (c1 c2 : com), cequiv c1 c2 -> cequiv c2 c1.
Proof. intros c1 c2 H. apply CEquivSym. apply H. Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com), cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof. intros c1 c2 c3 H12 H23. apply CEquivTrans with c2; auto. Qed.

(* Theorem CSeq_congruence : ~ (forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' -> cequiv <{ c1;c2 }> <{ c1';c2' }>).
Proof.
  unfold not. intros H.
  set (c1 := <{ X := 100 }>). set (c1' := <{ Y := 100 }>).
  set (c2 := <{ X := 200 }>). set (c2' := <{ Z := 200 }>).
  assert (cequiv c1 c1') by (now apply (CEquivSwap X Y)).
  assert (cequiv c2 c2') by (now apply (CEquivSwap X Z)).
  specialize (H _ _ _ _ H0 H1).
  inversion H; subst.
  - *)

(*  
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' -> cequiv <{ c1;c2 }> <{ c1';c2' }>.
Proof.
  intros c1 c1' c2 c2' Hc1.
  induction Hc1; intros Hc2.
  - inversion Hc2; subst.
    * constructor.
    *  
*)

(*
Example no_cseq_congru : 
  cequiv <{ X := 100 }> <{ Y := 100 }> ->
  cequiv <{ X := 200 }> <{ Z := 200 }> ->
  cequiv <{ X := 100; X := 200 }> <{ Y := 100; Z := 200 }> ->
  False.
Proof.
  (* intros Hc1 Hc2 H.
  remember (<{ X := 100; X := 200 }>).
  remember (<{ Y := 100; Z := 200 }>).
  induction H; subst.
  - discriminate.
  - 
  *)
  remember (<{ X := 100; X := 200 }>).
  remember (<{ Y := 100; Z := 200 }>).
  remember (<{ X := 100 }>).
  remember (<{ Y := 100 }>).
  remember (<{ X := 200 }>).
  remember (<{ Z := 200 }>).
  intros Hc1 Hc2 H. generalize dependent Hc1. generalize dependent Hc2.
  inversion H; subst.
  - discriminate.
  -  intros Hc1. induction Hc1.
    * 
*)

Example cseq_congru_1 : 
  cequiv <{ X := Y; Y := Z }> <{ X := X; X := Z }>.
Proof.
  Print cequiv.
  apply CEquivSwap with Y X. simpl. reflexivity.
Qed.

Example cseq_congru_2 : 
  cequiv <{ X := X; X := Z }> <{ X := X; X := X }>.
Proof.
  apply CEquivSwap with Z X. simpl. reflexivity.
Qed.
  
Example cseq_congru_3 : 
  cequiv <{ X := Y; Y := Z }> <{ X := X; X := X }>.
Proof.
  apply CEquivTrans with <{ X := X; X := Z }>.
  apply cseq_congru_1. apply cseq_congru_2.
Qed.

Example cseq_congru_4 : 
  cequiv <{ Z := Y; X := Z }> <{ Z := X; X := Z }>.
Proof. Admitted.

Example cseq_congru_5 : 
  cequiv <{ Z := X; X := Z }> <{ X := X; X := X }>.
Proof.
  apply CEquivSwap with Z X. simpl. reflexivity.
Qed.
  
Example cseq_congru_6 : 
  cequiv <{ Z := Y; X := Z }> <{ X := X; X := X }>.
Proof.
  apply CEquivTrans with  <{ Z := X; X := Z }>.
  apply cseq_congru_4. apply cseq_congru_5.
Qed.

Example cseq_congru_7 : cequiv <{ X := Y; Y := Z }> <{ Z := Y; X := Z }>.
Proof.
  apply CEquivTrans with <{ X := X; X := X }>.
  - apply cseq_congru_3.
  - apply CEquivSym. apply cseq_congru_6.
Qed.

(*

Example no_cseq_congru : 
  cequiv <{ X := Y; Y := Z }> <{ Z := Y; X := Z }> ->
  False.
Proof.
  intros H.
  remember (<{ X := Y}>) as xy. remember ( <{ Y := Z }>) as yz.
  remember (<{ Z := Y}>) as zy. remember ( <{ X := Z }>) as xz.
  remember (<{ xy ; yz }>).
  remember (<{ zy; xz }>).
  inversion H.
  - subst. discriminate. 
  - subst. apply IHcequiv.
    * Check cequiv_ind. subst.
    
*)

End FreeCEquiv.


Module EquivWithSwap.

Inductive xOrYOrOther : string -> Type :=
  | IsX : xOrYOrOther "X"
  | IsY : xOrYOrOther "Y"
  | IsOther : forall s, xOrYOrOther s
  .
  
Definition make_x_or_y_or_other (x : string): xOrYOrOther x :=
  match x as m return xOrYOrOther m with
  | "X"%string => IsX
  | "Y"%string => IsY
  | n => IsOther n
  end. 

Definition var_equiv_with_swap (s1 s2 : string) : Prop :=
  match make_x_or_y_or_other s1 with
  | IsX =>
      match make_x_or_y_or_other s2 with
      | IsY => True
      | _ => False
      end
  | IsY =>
      match make_x_or_y_or_other s2 with
      | IsX => True
      | _ => False
      end
  | IsOther s1' =>
      match make_x_or_y_or_other s2 with
      | IsOther s2' => s1' = s2'
      | _ => False
      end
  end.
  
Example var_equiv_example1 : var_equiv_with_swap "X" "Y".
Proof. reflexivity. Qed.
Example var_equiv_example2 : var_equiv_with_swap "Y" "X".
Proof. reflexivity. Qed.
Example var_equiv_example3 : var_equiv_with_swap "G" "G".
Proof. reflexivity. Qed.
Example var_equiv_example4 : var_equiv_with_swap "X" "X" -> False.
Proof. unfold var_equiv_with_swap. simpl. intros. auto. Qed.
Example var_equiv_example5 : var_equiv_with_swap "G" "Y" -> False.
Proof. intros. unfold var_equiv_with_swap in *. simpl in *. auto. Qed.
Example var_equiv_example6 : var_equiv_with_swap "Y" "G" -> False.
Proof. intros. unfold var_equiv_with_swap in *. simpl in *. auto. Qed.

Theorem var_equiv_with_swap_sym : forall s1 s2, var_equiv_with_swap s1 s2 -> var_equiv_with_swap s2 s1.
Proof.
  unfold var_equiv_with_swap. intros s1 s2 H.
  destruct (make_x_or_y_or_other s1) eqn:E;
  destruct (make_x_or_y_or_other s2) eqn:F;
  try destruct H;
  reflexivity.
Qed.

Theorem var_equiv_with_swap_trans_is_same :
  forall s1 s2 s3, var_equiv_with_swap s1 s2 -> var_equiv_with_swap s2 s3 -> s1 = s3.
Proof.
  unfold var_equiv_with_swap. intros s1 s2 s3 H12 H23.
  destruct (make_x_or_y_or_other s1) eqn:E;
  destruct (make_x_or_y_or_other s2) eqn:F;
  destruct (make_x_or_y_or_other s3) eqn:G;
  simpl; auto; try destruct H12; try destruct H23. auto.
  Qed.

Fixpoint aequiv_with_swap (a1 a2 : aexp) : Prop :=
  match (a1,a2) with
  | (ANum n1, ANum n2) => n1 = n2
  | (AId s1, AId s2) => var_equiv_with_swap s1 s2
  | (<{a1' + a1''}>, <{a2' + a2''}>) => aequiv_with_swap a1' a2' /\ aequiv_with_swap a1'' a2''
  | (<{a1' - a1''}>, <{a2' - a2''}>) => aequiv_with_swap a1' a2' /\ aequiv_with_swap a1'' a2''
  | (<{a1' * a1''}>, <{a2' * a2''}>) => aequiv_with_swap a1' a2' /\ aequiv_with_swap a1'' a2''
  | _ => False
  end.

Example aequiv_with_swap_example1 : aequiv_with_swap X Y.
Proof. reflexivity. Qed.
Example aequiv_with_swap_example2 :
  aequiv_with_swap <{ X + 100 - Y * (AId "G"%string) }> <{ Y + 100 - X * (AId "G"%string) }>.
Proof. now auto. Qed.
Example aequiv_with_swap_example3 : ~ (aequiv_with_swap <{ X }> <{ X }>).
Proof. simpl. intro H. apply var_equiv_example4. auto. Qed.
Example aequiv_with_swap_example4 :
  ~ (aequiv_with_swap <{ X + 100 - Y - (AId "G"%string) }> <{ Y + 100 - X * (AId "G"%string) }>).
Proof. simpl. intro H. destruct H. destruct H. Qed.

Theorem aequiv_with_swap_sym : forall a1 a2, aequiv_with_swap a1 a2 -> aequiv_with_swap a2 a1.
Proof.
  induction a1; destruct a2; simpl; intro H; try destruct H.
  - auto.
  - now apply var_equiv_with_swap_sym.
  - split. apply IHa1_1. assumption. apply IHa1_2. assumption.
  - split. apply IHa1_1. assumption. apply IHa1_2. assumption.
  - split. apply IHa1_1. assumption. apply IHa1_2. assumption.
  Qed.
  
Theorem aequiv_with_swap_trans_is_same :
  forall a1 a2 a3, aequiv_with_swap a1 a2 -> aequiv_with_swap a2 a3 -> a1 = a3.
Proof.
  unfold aequiv_with_swap. induction a1; destruct a2; destruct a3; simpl; subst;
  intros H12 H23; auto; try destruct H12; try destruct H23; auto.
  - set (G := var_equiv_with_swap_trans_is_same _ _ _ H12 H23). rewrite G. auto.
  - fold aequiv_with_swap in *.
    specialize (IHa1_1 _ _ H H1).
    specialize (IHa1_2 _ _ H0 H2).
    now subst.
  - fold aequiv_with_swap in *.
    specialize (IHa1_1 _ _ H H1).
    specialize (IHa1_2 _ _ H0 H2).
    now subst.
  - fold aequiv_with_swap in *.
    specialize (IHa1_1 _ _ H H1).
    specialize (IHa1_2 _ _ H0 H2).
    now subst.
  Qed.

Fixpoint bequiv_with_swap (b1 b2 : bexp) : Prop :=
  match (b1,b2) with
  | (<{ true }>, <{ true }>) => True
  | (<{ false }>, <{ false }>) => True
  | (<{ a1 = a1' }>, <{ a2 = a2' }>) => aequiv_with_swap a1 a2 /\ aequiv_with_swap a1' a2'
  | (<{ a1 <= a1' }>, <{ a2 <= a2' }>) => aequiv_with_swap a1 a2 /\ aequiv_with_swap a1' a2'
  | (<{ ~ b }>, <{ ~ b' }>) => bequiv_with_swap b b'
  | (<{ b1' && b1'' }>, <{ b2' && b2'' }>) => bequiv_with_swap b1' b2' /\ bequiv_with_swap b1'' b2''
  | _ => False
  end.

Theorem bequiv_with_swap_sym : forall b1 b2, bequiv_with_swap b1 b2 -> bequiv_with_swap b2 b1.
Proof.
  induction b1; destruct b2; simpl; intro H; try destruct H; try auto.
  - split; apply aequiv_with_swap_sym; assumption.
  - split; apply aequiv_with_swap_sym; assumption.
  Qed.

Theorem bequiv_with_swap_trans_is_same :
  forall b1 b2 b3, bequiv_with_swap b1 b2 -> bequiv_with_swap b2 b3 -> b1 = b3.
Proof.
  unfold bequiv_with_swap. induction b1; destruct b2; destruct b3; simpl; subst;
  intros H12 H23; auto; try destruct H12; try destruct H23; auto.
  - replace a4 with a1 by (apply aequiv_with_swap_trans_is_same with a0; assumption).
    replace a5 with a2 by (apply aequiv_with_swap_trans_is_same with a3; assumption).
    reflexivity.
  - replace a4 with a1 by (apply aequiv_with_swap_trans_is_same with a0; assumption).
    replace a5 with a2 by (apply aequiv_with_swap_trans_is_same with a3; assumption).
    reflexivity.
  - fold bequiv_with_swap in *.
    replace b3 with b1. reflexivity.
    apply IHb1 with b2; assumption.
  - fold bequiv_with_swap in *.
    specialize (IHb1_1 _ _ H H1).
    specialize (IHb1_2 _ _ H0 H2).
    now subst.
  Qed.

Fixpoint cequiv_with_swap (c1 c2 : com) : Prop :=
  match (c1, c2) with
  | (<{ skip }>, <{ skip }>) => True
  | (<{ s1 := a1 }>, <{ s2 := a2 }>) => var_equiv_with_swap s1 s2 /\ aequiv_with_swap a1 a2
  | (<{ c1'; c1'' }>, <{ c2' ; c2'' }>) => cequiv_with_swap c1' c2' /\ cequiv_with_swap c1'' c2''
  | (<{ if b1 then c1' else c1'' end }>, <{ if b2 then c2' else c2'' end }>) => 
      bequiv_with_swap b1 b2 /\ cequiv_with_swap c1' c2' /\ cequiv_with_swap c1'' c2''
  | _ => False
  end.

Example cequiv_with_swap_example1 :
  cequiv_with_swap
    <{ skip ; X := Y + 100 ; "G" := X }>
    <{ skip ; Y := X + 100 ; "G" := Y }>.
Proof. now auto. Qed.
Example cequiv_with_swap_example2 :
  ~ (cequiv_with_swap <{ skip ; "G" := Y + 100 }> <{ skip ; "F" := X + 100 }>).
Proof. simpl. intro H. destruct H.  destruct H0. discriminate. Qed.
  
Theorem cequiv_with_swap_sym : forall c1 c2, cequiv_with_swap c1 c2 -> cequiv_with_swap c2 c1.
Proof.
  induction c1; destruct c2; simpl; intro H; try destruct H; try auto.
  - split. apply var_equiv_with_swap_sym. assumption. apply aequiv_with_swap_sym; assumption.
  - split.
    + apply bequiv_with_swap_sym. assumption.
    + destruct H0. apply IHc1_1 in H0. apply IHc1_2 in H1. split; assumption.
  Qed.

Theorem cequiv_with_swap_trans_is_same :
  forall c1 c2 c3, cequiv_with_swap c1 c2 -> cequiv_with_swap c2 c3 -> c1 = c3.
Proof.
  unfold cequiv_with_swap. induction c1; destruct c2; destruct c3; simpl; subst;
  intros H12 H23; auto; try destruct H12; try destruct H23; auto.
  - replace x1 with x. replace a1 with a. reflexivity.
    apply aequiv_with_swap_trans_is_same with a0; assumption.
    apply var_equiv_with_swap_trans_is_same with x0; assumption.
  - fold cequiv_with_swap in *.
    specialize (IHc1_1 _ _ H H1).
    specialize (IHc1_2 _ _ H0 H2).
    now subst.
  - fold cequiv_with_swap in *.
    destruct H0,H2.
    specialize (IHc1_1 _ _ H0 H2).
    specialize (IHc1_2 _ _ H3 H4).
    subst.
    replace b1 with b; try reflexivity.
    apply bequiv_with_swap_trans_is_same with b0; assumption.
  Qed.

Inductive cequiv : com -> com -> Prop :=
  | CEquivRefl : forall c, cequiv c c
  | CEquivSwap : forall c1 c2, cequiv_with_swap c1 c2 -> cequiv c1 c2
  .
  
Example cequiv_example1 :
  cequiv
    <{ skip ; X := Y + 100 ; "G" := X }>
    <{ skip ; Y := X + 100 ; "G" := Y }>.
Proof. constructor. simpl. unfold var_equiv_with_swap. simpl. auto. Qed.
Example cequiv_example2:
  cequiv
    <{ skip ; X := X + 100 ; "G" := X }>
    <{ skip ; X := X + 100 ; "G" := X }>.
Proof. constructor. Qed.
Example cequiv_example3:
  ~ (cequiv <{ X := X + 100 ; "G" := Y }> <{ X := X + 100 ; "G" := X }>).
Proof.
  simpl. intros H. inversion H; subst.
  simpl in H0. destruct H0. destruct H0. unfold var_equiv_with_swap in H0. simpl in H0. destruct H0.
Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof. constructor. Qed.

Lemma sym_cequiv : forall (c1 c2 : com), cequiv c1 c2 -> cequiv c2 c1.
Proof. intros c1 c2 H. inversion H; subst. assumption. apply cequiv_with_swap_sym in H0. constructor. auto.  Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com), cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  intros c1 c2 c3 H12 H23.
  inversion H12; subst; inversion H23; subst; try auto.
  - replace c3 with c1. constructor.
    apply cequiv_with_swap_trans_is_same with c2; assumption. 
  Qed.

(* x:=x+1≡y:=y+1 but (x:=0;x:=x+1)≢(x:=0;y:=y+1) *)
 
Theorem no_CSeq_congruence : 
  ~ (forall c1 c1' c2 c2',
      cequiv c1 c1' -> cequiv c2 c2' -> cequiv <{ c1;c2 }> <{ c1';c2' }>).
Proof.
  unfold not. intros H.
  assert (cequiv <{ X := 100 }> <{ X := 100 }>) by constructor.
  assert (cequiv <{ X := X + 1 }> <{ Y := Y + 1 }>).
  { constructor.  simpl. unfold var_equiv_with_swap. simpl. auto. }
  specialize (H _ _ _ _ H0 H1). clear H0 H1. inversion H; subst.
  unfold cequiv_with_swap in H0. destruct H0. destruct H0. unfold var_equiv_with_swap in H0. simpl in H0. destruct H0.
  Qed.  

End EquivWithSwap.

(*

Theorem rename_vars_example : forall a,
  cequiv_under_var_swaps
    <{ X := a }>
    <{ Y := a }>.
Proof.
  intros a. unfold cequiv_under_var_swaps.
  exists X,Y. intros st st'. unfold swap_vars. split.
  - admit.
  - intros H. inversion H. subst. inversion H.  subst.
    rewrite t_update_eq. rewrite t_update_eq. rewrite t_update_permute by (intro; discriminate).
    rewrite t_update_shadow.
    rewrite t_update_permute by discriminate.
    rewrite t_update_shadow.
    rewrite t_update_neq by discriminate.
    rewrite t_update_eq.
    apply 
    replace ((Y !-> aeval st a; st) X) with (st X) by (reflexivity).
    rewrite t_update_shadow.
    replace (Y !-> st X; Y !-> aeval st a; st) with (Y !-> st X; st).
    * admit.
    * 
    rewrite t_update_same.
    Print ceval.
    inversion H. subst.
    constructor.
    rewrite t_update_neq.
    * 
    unfold t_update.
    unfold t_update in H. 
*)

(* ################################################################# *)
(** * Program Transformations *)

(** A _program transformation_ is a function that takes a program as
    input and produces some variant of the program as output.
    Compiler optimizations such as constant folding are a canonical
    example, but there are many others. *)

(*** A program transformation is _sound_ if it preserves the
    behavior of the original program. *)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(* ================================================================= *)
(** ** The Constant-Folding Transformation *)

(** An expression is _constant_ when it contains no variable
    references.

    Constant folding is an optimization that finds constant
    expressions and replaces them by their values. *)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId x        => AId x
  | <{ a1 + a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => <{ a1' + a2' }>
    end
  | <{ a1 - a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => <{ a1' - a2' }>
    end
  | <{ a1 * a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => <{ a1' * a2' }>
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp <{ (1 + 2) * X }>
  = <{ 3 * X }>.
Proof. reflexivity. Qed.

(** Note that this version of constant folding doesn't eliminate
    trivial additions, etc. -- we are focusing attention on a single
    optimization for the sake of simplicity.  It is not hard to
    incorporate other ways of simplifying expressions; the definitions
    and proofs just get longer. *)

Example fold_aexp_ex2 :
  fold_constants_aexp <{ X - ((0 * 6) + Y) }> = <{ X - (0 + Y) }>.
Proof. reflexivity. Qed.

(** Not only can we lift [fold_constants_aexp] to [bexp]s (in the
    [BEq] and [BLe] cases); we can also look for constant _boolean_
    expressions and evaluate them in-place. *)

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | <{true}>        => <{true}>
  | <{false}>       => <{false}>
  | <{ a1 = a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' = a2' }>
      end
  | <{ a1 <= a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <= a2' }>
      end
  | <{ ~ b1 }>  =>
      match (fold_constants_bexp b1) with
      | <{true}> => <{false}>
      | <{false}> => <{true}>
      | b1' => <{ ~ b1' }>
      end
  | <{ b1 && b2 }>  =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (<{true}>, <{true}>) => <{true}>
      | (<{true}>, <{false}>) => <{false}>
      | (<{false}>, <{true}>) => <{false}>
      | (<{false}>, <{false}>) => <{false}>
      | (b1', b2') => <{ b1' && b2' }>
      end
  end.

Example fold_bexp_ex1 :
  fold_constants_bexp <{ true && ~(false && true) }>
  = <{ true }>.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp <{ (X = Y) && (0 = (2 - (1 + 1))) }>
  = <{ (X = Y) && true }>.
Proof. reflexivity. Qed.

(** To fold constants in a command, we apply the appropriate folding
    functions on all embedded expressions. *)

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | <{ skip }> =>
      <{ skip }>
  | <{ x := a }> =>
      <{ x := (fold_constants_aexp a) }>
  | <{ c1 ; c2 }>  =>
      <{ fold_constants_com c1 ; fold_constants_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      match fold_constants_bexp b with
      | <{true}>  => fold_constants_com c1
      | <{false}> => fold_constants_com c2
      | b' => <{ if b' then fold_constants_com c1
                       else fold_constants_com c2 end}>
      end
  | <{ while b do c1 end }> =>
      match fold_constants_bexp b with
      | <{true}> => <{ while true do skip end }>
      | <{false}> => <{ skip }>
      | b' => <{ while b' do (fold_constants_com c1) end }>
      end
  end.

Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    <{ X := 4 + 5;
       Y := X - 3;
       if ((X - Y) = (2 + 4)) then skip
       else Y := 0 end;
       if (0 <= (4 - (2 + 1))) then Y := 0
       else skip end;
       while (Y = 0) do
         X := X + 1
       end }>
  = (* After constant folding: *)
    <{ X := 9;
       Y := X - 3;
       if ((X - Y) = 6) then skip
       else Y := 0 end;
       Y := 0;
       while (Y = 0) do
         X := X + 1
       end }>.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Soundness of Constant Folding *)

(** Now we need to show that what we've done is correct. *)

(** Here's the proof for arithmetic expressions: *)

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  induction a; simpl;
    (* ANum and AId follow immediately *)
    try reflexivity;
    (* APlus, AMinus, and AMult follow from the IH
       and the observation that
              aeval st (<{ a1 + a2 }>)
            = ANum ((aeval st a1) + (aeval st a2))
            = aeval st (ANum ((aeval st a1) + (aeval st a2)))
       (and similarly for AMinus/minus and AMult/mult) *)
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.

(** **** Exercise: 3 stars, standard, optional (fold_bexp_Eq_informal)

    Here is an informal proof of the [BEq] case of the soundness
    argument for boolean expression constant folding.  Read it
    carefully and compare it to the formal proof that follows.  Then
    fill in the [BLe] case of the formal proof (without looking at the
    [BEq] case, if possible).

   _Theorem_: The constant folding function for booleans,
   [fold_constants_bexp], is sound.

   _Proof_: We must show that [b] is equivalent to [fold_constants_bexp b],
   for all boolean expressions [b].  Proceed by induction on [b].  We
   show just the case where [b] has the form [a1 = a2].

   In this case, we must show

       beval st <{ a1 = a2 }>
     = beval st (fold_constants_bexp <{ a1 = a2 }>).

   There are two cases to consider:

     - First, suppose [fold_constants_aexp a1 = ANum n1] and
       [fold_constants_aexp a2 = ANum n2] for some [n1] and [n2].

       In this case, we have

           fold_constants_bexp <{ a1 = a2 }>
         = if n1 =? n2 then <{true}> else <{false}>

       and

           beval st <{a1 = a2}>
         = (aeval st a1) =? (aeval st a2).

       By the soundness of constant folding for arithmetic
       expressions (Lemma [fold_constants_aexp_sound]), we know

           aeval st a1
         = aeval st (fold_constants_aexp a1)
         = aeval st (ANum n1)
         = n1

       and

           aeval st a2
         = aeval st (fold_constants_aexp a2)
         = aeval st (ANum n2)
         = n2,

       so

           beval st <{a1 = a2}>
         = (aeval a1) =? (aeval a2)
         = n1 =? n2.

       Also, it is easy to see (by considering the cases [n1 = n2] and
       [n1 <> n2] separately) that

           beval st (if n1 =? n2 then <{true}> else <{false}>)
         = if n1 =? n2 then beval st <{true}> else beval st <{false}>
         = if n1 =? n2 then true else false
         = n1 =? n2.

       So

           beval st (<{ a1 = a2 }>)
         = n1 =? n2.
         = beval st (if n1 =? n2 then <{true}> else <{false}>),

       as required.

     - Otherwise, one of [fold_constants_aexp a1] and
       [fold_constants_aexp a2] is not a constant.  In this case, we
       must show

           beval st <{a1 = a2}>
         = beval st (<{ (fold_constants_aexp a1) =
                         (fold_constants_aexp a2) }>),

       which, by the definition of [beval], is the same as showing

           (aeval st a1) =? (aeval st a2)
         = (aeval st (fold_constants_aexp a1)) =?
                   (aeval st (fold_constants_aexp a2)).

       But the soundness of constant folding for arithmetic
       expressions ([fold_constants_aexp_sound]) gives us

         aeval st a1 = aeval st (fold_constants_aexp a1)
         aeval st a2 = aeval st (fold_constants_aexp a2),

       completing the case.  [] *)

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* true and false are immediate *)
    try reflexivity.
  - (* BEq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n =? n0); reflexivity.
  - (* BLe *)
    (* simpl. unfold beval. destruct (fold_constants_aexp a1) eqn:E.
    * destruct (fold_constants_aexp a2) eqn:F.
      +  *)
    simpl.
    (*
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1. 
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
      simpl. destruct (n <=? n0); reflexivity.
    *)
    replace (aeval st a1) with (aeval st (fold_constants_aexp a1)) by
      (rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st (fold_constants_aexp a2)) by
      (rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct (fold_constants_aexp a1) eqn:H; destruct (fold_constants_aexp a2) eqn:G; try reflexivity.
      simpl. destruct (n <=? n0); reflexivity.  
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
  Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (fold_constants_com_sound)

    Complete the [while] case of the following proof. *)

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* skip *) apply refl_cequiv.
  - (* := *) apply CAsgn_congruence.
              apply fold_constants_aexp_sound.
  - (* ; *) apply CSeq_congruence; assumption.
  - (* if *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      (* (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          [fold_constants_bexp_sound].) *)
    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply if_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply if_false; assumption.
  - (* while *)
    assert (bequiv b (fold_constants_bexp b)) by (apply fold_constants_bexp_sound).
    destruct (fold_constants_bexp b) eqn:Heqb; try (apply CWhile_congruence; assumption).
    + apply while_true; assumption.
    + apply while_false. assumption.
  Qed.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Soundness of (0 + n) Elimination, Redux *)

(** **** Exercise: 4 stars, advanced, optional (optimize_0plus)

    Recall the definition [optimize_0plus] from the [Imp] chapter
    of _Logical Foundations_:

    Fixpoint optimize_0plus (a:aexp) : aexp :=
      match a with
      | ANum n =>
          ANum n
      | <{ 0 + a2 }> =>
          optimize_0plus a2
      | <{ a1 + a2 }> =>
          <{ (optimize_0plus a1) + (optimize_0plus a2) }>
      | <{ a1 - a2 }> =>
          <{ (optimize_0plus a1) - (optimize_0plus a2) }>
      | <{ a1 * a2 }> =>
          <{ (optimize_0plus a1) * (optimize_0plus a2) }>
      end.

   Note that this function is defined over the old [aexp]s,
   without states.

   Write a new version of this function that accounts for variables,
   plus analogous ones for [bexp]s and commands:

     optimize_0plus_aexp
     optimize_0plus_bexp
     optimize_0plus_com

   Prove that these three functions are sound, as we did for
   [fold_constants_*].  Make sure you use the congruence lemmas in
   the proof of [optimize_0plus_com] -- otherwise it will be _long_!

   Then define an optimizer on commands that first folds
   constants (using [fold_constants_com]) and then eliminates [0 + n]
   terms (using [optimize_0plus_com]).

   - Give a meaningful example of this optimizer's output.

   - Prove that the optimizer is sound.  (This part should be _very_
     easy.)  *)
    
Fixpoint optimize_0plus_aexp (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId s => AId s
  | <{ 0 + a2 }> => optimize_0plus_aexp a2
  | <{ a1 + a2 }> => <{ (optimize_0plus_aexp a1) + (optimize_0plus_aexp a2) }>
  | <{ a1 - a2 }> => <{ (optimize_0plus_aexp a1) - (optimize_0plus_aexp a2) }>
  | <{ a1 * a2 }> => <{ (optimize_0plus_aexp a1) * (optimize_0plus_aexp a2) }>
  end.
  
Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
  match b with
  | <{true}> => <{true}>
  | <{false}> => <{false}>
  | <{ a1 = a2 }>  => <{ (optimize_0plus_aexp a1) = (optimize_0plus_aexp a2) }>
  | <{ a1 <= a2 }>  => <{ (optimize_0plus_aexp a1) <= (optimize_0plus_aexp a2) }>
  | <{ ~ b1 }>  => <{ ~ (optimize_0plus_bexp b1) }>
  | <{ b1 && b2 }>  => <{ (optimize_0plus_bexp b1) && (optimize_0plus_bexp b2) }>
  end.
  
Print com.

Fixpoint optimize_0plus_com (c : com) : com :=
  match c with
  | <{skip}> => <{skip}>
  | <{ x := a }> => <{ x := (optimize_0plus_aexp a) }>
  | <{ c1 ; c2 }> => <{ (optimize_0plus_com c1) ; (optimize_0plus_com c2) }>
  | <{ if b then c1 else c2 end }> => <{ if (optimize_0plus_bexp b) then (optimize_0plus_com c1) else (optimize_0plus_com c2) end }>
  | <{ while b do c' end }> => <{ while (optimize_0plus_bexp b) do (optimize_0plus_com c') end }>
  end.
  

Theorem optimize_0plus_aexp_sound :
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound. induction a; try (simpl; apply refl_aequiv); unfold aequiv in *; intros st.
  - replace (aeval st <{ a1 + a2 }>) with ((aeval st a1) + (aeval st a2)) by reflexivity.
    rewrite IHa1. rewrite IHa2.
    destruct a1; try reflexivity.
    * destruct n; try reflexivity.
  - simpl. rewrite IHa1. now rewrite IHa2.
  - simpl. rewrite IHa1. now rewrite IHa2.
  Qed.
  
Theorem optimize_0plus_bexp_sound :
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. induction b; try (simpl; apply refl_bequiv); intros st; simpl; unfold bequiv in *.
  - assert (Ha1: aeval st a1 = aeval st (optimize_0plus_aexp a1)) by (apply optimize_0plus_aexp_sound).
    assert (Ha2: aeval st a2 = aeval st (optimize_0plus_aexp a2)) by (apply optimize_0plus_aexp_sound).
    now rewrite Ha1,Ha2.
  - assert (Ha1: aeval st a1 = aeval st (optimize_0plus_aexp a1)) by (apply optimize_0plus_aexp_sound).
    assert (Ha2: aeval st a2 = aeval st (optimize_0plus_aexp a2)) by (apply optimize_0plus_aexp_sound).
    now rewrite Ha1,Ha2.
  - now rewrite IHb.
  - now rewrite IHb1,IHb2.
  Qed. 
 
Theorem optimize_0plus_com_sound :
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. induction c; simpl; try (apply refl_cequiv).
  - apply CAsgn_congruence. apply optimize_0plus_aexp_sound.
  - apply CSeq_congruence; assumption.
  - apply CIf_congruence. apply optimize_0plus_bexp_sound. assumption. assumption.
  - apply CWhile_congruence. apply optimize_0plus_bexp_sound. assumption.
  Qed.

(* ################################################################# *)
(** * Proving Inequivalence *)

(** Suppose that [c1] is a command of the form [X := a1; Y := a2]
    and [c2] is the command [X := a1; Y := a2'], where [a2'] is
    formed by substituting [a1] for all occurrences of [X] in [a2].
    For example, [c1] and [c2] might be:

       c1  =  (X := 42 + 53;
               Y := Y + X)
       c2  =  (X := 42 + 53;
               Y := Y + (42 + 53))

    Clearly, this _particular_ [c1] and [c2] are equivalent.  Is this
    true in general? *)

(** We will see in a moment that it is not, but it is worthwhile
    to pause, now, and see if you can find a counter-example on your
    own. *)

(** More formally, here is the function that substitutes an arithmetic
    expression [u] for each occurrence of a given variable [x] in
    another expression [a]: *)

Fixpoint subst_aexp (x : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n       =>
      ANum n
  | AId x'       =>
      if eqb_string x x' then u else AId x'
  | <{ a1 + a2 }>  =>
      <{ (subst_aexp x u a1) + (subst_aexp x u a2) }>
  | <{ a1 - a2 }> =>
      <{ (subst_aexp x u a1) - (subst_aexp x u a2) }>
  | <{ a1 * a2 }>  =>
      <{ (subst_aexp x u a1) * (subst_aexp x u a2) }>
  end.

Example subst_aexp_ex :
  subst_aexp X <{42 + 53}> <{Y + X}>
  = <{ Y + (42 + 53)}>.
Proof. simpl. reflexivity. Qed.

(** And here is the property we are interested in, expressing the
    claim that commands [c1] and [c2] as described above are
    always equivalent.  *)

Definition subst_equiv_property := forall x1 x2 a1 a2,
  cequiv <{ x1 := a1; x2 := a2 }>
         <{ x1 := a1; x2 := subst_aexp x1 a1 a2 }>.

(** Sadly, the property does _not_ always hold.

    We can show the following counterexample:

       X := X + 1; Y := X

    If we perform the substitution, we get

       X := X + 1; Y := X + 1

    which clearly isn't equivalent to the original program. [] *)

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.

  (* Here is the counterexample: assuming that [subst_equiv_property]
     holds allows us to prove that these two programs are
     equivalent... *)
  remember <{ X := X + 1;
              Y := X }>
      as c1.
  remember <{ X := X + 1;
              Y := X + 1 }>
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).
  clear Contra.

  (* ... allows us to show that the command [c2] can terminate
     in two different final states:
        st1 = (Y !-> 1 ; X !-> 1)
        st2 = (Y !-> 2 ; X !-> 1). *)
  remember (Y !-> 1 ; X !-> 1) as st1.
  remember (Y !-> 2 ; X !-> 1) as st2.
  assert (H1 : empty_st =[ c1 ]=> st1);
  assert (H2 : empty_st =[ c2 ]=> st2);
  try (subst;
       apply E_Seq with (st' := (X !-> 1));
       apply E_Asgn; reflexivity).
  clear Heqc1 Heqc2.

  apply H in H1.
  clear H.

  (* Finally, we use the fact that evaluation is deterministic
     to obtain a contradiction. *)
  assert (Hcontra : st1 = st2)
    by (apply (ceval_deterministic c2 empty_st); assumption).
  clear H1 H2.

  assert (Hcontra' : st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. discriminate. Qed.

(** **** Exercise: 4 stars, standard, optional (better_subst_equiv)

    The equivalence we had in mind above was not complete nonsense --
    it was actually almost right.  To make it correct, we just need to
    exclude the case where the variable [X] occurs in the
    right-hand-side of the first assignment statement. *)

Inductive var_not_used_in_aexp (x : string) : aexp -> Prop :=
  | VNUNum : forall n, var_not_used_in_aexp x (ANum n)
  | VNUId : forall y, x <> y -> var_not_used_in_aexp x (AId y)
  | VNUPlus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 + a2 }>)
  | VNUMinus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 - a2 }>)
  | VNUMult : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 * a2 }>).

Lemma aeval_weakening : forall x st a ni,
  var_not_used_in_aexp x a ->
  aeval (x !-> ni ; st) a = aeval st a.
Proof.
  intros x st a ni H. induction H; subst.
  - reflexivity.
  - simpl. apply t_update_neq. assumption.
  - simpl. now rewrite IHvar_not_used_in_aexp1,IHvar_not_used_in_aexp2.
  - simpl. now rewrite IHvar_not_used_in_aexp1,IHvar_not_used_in_aexp2.
  - simpl. now rewrite IHvar_not_used_in_aexp1,IHvar_not_used_in_aexp2.
  Qed.

(** Using [var_not_used_in_aexp], formalize and prove a correct version
    of [subst_equiv_property]. *)

Definition subst_equiv_property_correct := forall x1 x2 a1 a2,
  var_not_used_in_aexp x1 a1 ->
  cequiv <{ x1 := a1; x2 := a2 }>
         <{ x1 := a1; x2 := subst_aexp x1 a1 a2 }>.

Theorem var_not_used_in_aeval :
  forall st x a n, var_not_used_in_aexp x a -> aeval (x !-> n; st) a = aeval st a.
Proof.
  intros st x a n H. induction H; subst.
  - reflexivity.
  - now apply t_update_neq.
  - unfold aeval. fold aeval. rewrite IHvar_not_used_in_aexp1. rewrite IHvar_not_used_in_aexp2. reflexivity.
  - unfold aeval. fold aeval. rewrite IHvar_not_used_in_aexp1. rewrite IHvar_not_used_in_aexp2. reflexivity.
  - unfold aeval. fold aeval. rewrite IHvar_not_used_in_aexp1. rewrite IHvar_not_used_in_aexp2. reflexivity.
Qed.

Theorem aeval_subst_is_same_as_aeval :
  forall a2 a1 st x1,
  var_not_used_in_aexp x1 a1 ->
  aeval (x1 !-> aeval st a1; st) (subst_aexp x1 a1 a2) = aeval (x1 !-> aeval st a1; st) a2.
Proof.
  induction a2; try reflexivity; intros a1 st x1 Hvarnot.
  - destruct (eqb_string x1 x) eqn:E.
    * apply eqb_string_true_iff in E; subst. cbn. rewrite <- eqb_string_refl.
      rewrite (var_not_used_in_aeval _ _ _ _ Hvarnot). now rewrite t_update_eq.
    * simpl. rewrite E. simpl. reflexivity.
  - cbn. rewrite (IHa2_1 _ _ _ Hvarnot). now rewrite (IHa2_2 _ _ _ Hvarnot).
  - simpl. rewrite (IHa2_1 _ _ _ Hvarnot). now rewrite (IHa2_2 _ _ _ Hvarnot).
  - simpl. rewrite (IHa2_1 _ _ _ Hvarnot). now rewrite (IHa2_2 _ _ _ Hvarnot).
  Qed.

Theorem subst_equiv_to :
  forall (x1 x2 : string) (a1 a2 : aexp),
  var_not_used_in_aexp x1 a1 ->
  forall st st', st =[ x1 := a1; x2 := a2 ]=> st' ->
  st =[ x1 := a1; x2 := (subst_aexp x1 a1 a2) ]=> st'.
Proof.
  intros x1 x2 a1 a2 Hvarnot st st' H. inversion H; subst.
  inversion H2; inversion H5; subst.
  apply E_Seq with (x1 !-> aeval st a1; st); try assumption.
  constructor.
  apply aeval_subst_is_same_as_aeval. assumption.
  Qed.
  
Theorem equiv_to_subst :
  forall (x1 x2 : string) (a1 a2 : aexp),
  var_not_used_in_aexp x1 a1 ->
  forall st st', st =[ x1 := a1; x2 := (subst_aexp x1 a1 a2) ]=> st' ->
  st =[ x1 := a1; x2 := a2 ]=> st'.
Proof.
  intros x1 x2 a1 a2 Hvarnot st st' H. inversion H; subst.
  inversion H2; inversion H5; subst.
  apply E_Seq with (x1 !-> aeval st a1; st); try assumption.
  constructor.
  symmetry. apply aeval_subst_is_same_as_aeval. assumption.
  Qed.

Theorem subst_equiv :
  forall (x1 x2 : string) (a1 a2 : aexp),
  var_not_used_in_aexp x1 a1 ->
  cequiv <{ x1 := a1; x2 := a2 }> <{ x1 := a1; x2 := (subst_aexp x1 a1 a2) }>.
Proof.
  split.
  - now apply subst_equiv_to.
  - now apply equiv_to_subst.
  Qed.
  
(** **** Exercise: 3 stars, standard (inequiv_exercise)

    Prove that an infinite loop is not equivalent to [skip] *)

Theorem inequiv_exercise:
  ~ cequiv <{ while true do skip end }> <{ skip }>.
Proof.
  intros H. unfold cequiv in H. specialize (H empty_st empty_st).
  destruct H.
  assert (empty_st =[ skip ]=> empty_st) by constructor.
  specialize (H0 H1). clear H H1. remember (<{ while true do skip end }>) as c.
  induction H0; subst; try discriminate.
  - inversion Heqc; subst. discriminate.
  - inversion Heqc; subst. now apply IHceval2.
  Qed.

(* ################################################################# *)
(** * Extended Exercise: Nondeterministic Imp *)

(** As we have seen (in theorem [ceval_deterministic] in the [Imp]
    chapter), Imp's evaluation relation is deterministic.  However,
    _non_-determinism is an important part of the definition of many
    real programming languages. For example, in many imperative
    languages (such as C and its relatives), the order in which
    function arguments are evaluated is unspecified.  The program
    fragment

      x = 0;
      f(++x, x)

    might call [f] with arguments [(1, 0)] or [(1, 1)], depending how
    the compiler chooses to order things.  This can be a little
    confusing for programmers, but it gives the compiler writer useful
    freedom.

    In this exercise, we will extend Imp with a simple
    nondeterministic command and study how this change affects
    program equivalence.  The new command has the syntax [HAVOC X],
    where [X] is an identifier. The effect of executing [HAVOC X] is
    to assign an _arbitrary_ number to the variable [X],
    nondeterministically. For example, after executing the program:

      HAVOC Y;
      Z := Y * 2

    the value of [Y] can be any number, while the value of [Z] is
    twice that of [Y] (so [Z] is always even). Note that we are not
    saying anything about the _probabilities_ of the outcomes -- just
    that there are (infinitely) many different outcomes that can
    possibly happen after executing this nondeterministic code.

    In a sense, a variable on which we do [HAVOC] roughly corresponds
    to an uninitialized variable in a low-level language like C.  After
    the [HAVOC], the variable holds a fixed but arbitrary number.  Most
    sources of nondeterminism in language definitions are there
    precisely because programmers don't care which choice is made (and
    so it is good to leave it open to the compiler to choose whichever
    will run faster).

    We call this new language _Himp_ (``Imp extended with [HAVOC]''). *)

Module Himp.

(** To formalize Himp, we first add a clause to the definition of
    commands. *)

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.                (* <--- NEW *)

Notation "'havoc' l" := (CHavoc l)
                          (in custom com at level 60, l constr at level 0).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

(** **** Exercise: 2 stars, standard (himp_ceval)

    Now, we must extend the operational semantics. We have provided
   a template for the [ceval] relation below, specifying the big-step
   semantics. What rule(s) must be added to the definition of [ceval]
   to formalize the behavior of the [HAVOC] command? *)

Reserved Notation "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99, st constr,
          st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_Havoc : forall st x n, st =[ havoc x ]=> (x !-> n; st)
(*  IN HERE *)

  where "st =[ c ]=> st'" := (ceval c st st').

(** As a sanity check, the following claims should be provable for
    your definition: *)

Example havoc_example1 : empty_st =[ havoc X ]=> (X !-> 0).
Proof. apply E_Havoc. Qed.

Example havoc_example2 :
  empty_st =[ skip; havoc Z ]=> (Z !-> 42).
Proof.
  eapply E_Seq.  apply E_Skip. apply E_Havoc. Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_Check_rule_for_HAVOC : option (nat*string) := None.
(** [] *)

(** Finally, we repeat the definition of command equivalence from above: *)

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  st =[ c1 ]=> st' <-> st =[ c2 ]=> st'.

(** Let's apply this definition to prove some nondeterministic
    programs equivalent / inequivalent. *)

(** **** Exercise: 3 stars, standard (havoc_swap)

    Are the following two programs equivalent? *)

Definition pXY :=
  <{ havoc X ; havoc Y }>.

Definition pYX :=
  <{ havoc Y; havoc X }>.

(** If you think they are equivalent, prove it. If you think they are
    not, prove that. *)

Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof.
  left. unfold cequiv. unfold pXY. unfold pYX.
  split; intros H.
  - inversion H; subst. inversion H2; subst. inversion H2. subst.
    inversion H5; subst. inversion H5; subst.
    assert ((Y !-> n2; X !-> n; st) = (X !-> n; Y !-> n2; st)).
    { apply t_update_permute. intro. discriminate. }
    rewrite H0.
    apply E_Seq with (Y !-> n2; st).
    apply E_Havoc.
    apply E_Havoc.
  - inversion H; subst. inversion H2; subst. inversion H2. subst.
    inversion H5; subst. inversion H5; subst.
    assert ((Y !-> n; X !-> n2; st) = (X !-> n2; Y !-> n; st)).
    { apply t_update_permute. intro. discriminate. }
    rewrite <- H0.
    apply E_Seq with (X !-> n2; st).
    apply E_Havoc.
    apply E_Havoc.
  Qed.
  
(** [] *)

(** **** Exercise: 4 stars, standard, optional (havoc_copy)

    Are the following two programs equivalent? *)

Definition ptwice :=
  <{ havoc X; havoc Y }>.

Definition pcopy :=
  <{ havoc X; Y := X }>.

(** If you think they are equivalent, then prove it. If you think they
    are not, then prove that.  (Hint: You may find the [assert] tactic
    useful.) *)

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~cequiv ptwice pcopy.
Proof.
  right. unfold not. unfold ptwice. unfold pcopy. unfold cequiv.
  intro H. specialize (H empty_st (Y !-> 2; X !-> 1)).
  destruct H.
  assert (empty_st =[ havoc X; havoc Y ]=> (Y !-> 2; X !-> 1)).
  { apply E_Seq with (X !-> 1). apply E_Havoc. apply E_Havoc. }
  specialize (H H1).
  inversion H; subst.
  inversion H4; subst.
  inversion H4; subst.
  inversion H7; subst.
  unfold aeval in H9.
  rewrite t_update_eq in H9.
  clear H6 H4 H7 H1 H0 H.
  set (G := equal_f H9).
  set (P := G Y). cbv in P.
  set (O := G X). cbv in O. rewrite P in O. discriminate.
  Qed.
(** [] *)

(** The definition of program equivalence we are using here has some
    subtle consequences on programs that may loop forever.  What
    [cequiv] says is that the set of possible _terminating_ outcomes
    of two equivalent programs is the same. However, in a language
    with nondeterminism, like Himp, some programs always terminate,
    some programs always diverge, and some programs can
    nondeterministically terminate in some runs and diverge in
    others. The final part of the following exercise illustrates this
    phenomenon.
*)

(** **** Exercise: 4 stars, advanced (p1_p2_term)

    Consider the following commands: *)

Definition p1 : com :=
  <{ while ~ (X = 0) do
       havoc Y;
       X := X + 1
     end }>.

Definition p2 : com :=
  <{ while ~ (X = 0) do
       skip
     end }>.

(** Intuitively, [p1] and [p2] have the same termination behavior:
    either they loop forever, or they terminate in the same state they
    started in.  We can capture the termination behavior of [p1] and
    [p2] individually with these lemmas: *)

Lemma p1_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p1 ]=> st'.
Proof. 
  intros st st' Hnot H.
  remember p1 as c eqn:Hcc.
  unfold p1 in *.
  induction H; try inversion Hcc; subst; simpl in H.
  - destruct (st X) eqn:E.
    * now apply Hnot.
    * discriminate.
  - clear Hcc.
    destruct (st X) eqn:E.
    * simpl in H. discriminate.
    * apply IHceval2; try reflexivity.
      inversion H0; subst.
      inversion H7; subst.
      rewrite t_update_eq.
      simpl.
      rewrite add_comm. simpl.    
      intro Hn. discriminate.
  Qed.

Lemma p2_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p2 ]=> st'.
Proof.
  intros st st' Hnot H.
  remember p2 as c eqn:Hcc.
  unfold p2 in *.
  induction H; try inversion Hcc; subst; simpl in H.
  - destruct (st X) eqn:E.
    * now apply Hnot.
    * discriminate.
  - inversion H0; subst.
    apply IHceval2; assumption.
  Qed.
    
(** [] *)

(** **** Exercise: 4 stars, advanced (p1_p2_equiv)

    Use these two lemmas to prove that [p1] and [p2] are actually
    equivalent. *)

Theorem p1_p2_equiv : cequiv p1 p2.
Proof. 
  unfold cequiv. intros st st'. destruct (st X) eqn:E; split; intro H.
  - unfold p1 in *; unfold p2 in *.
    inversion H; subst.
    + apply E_WhileFalse. simpl. now rewrite E.
    + simpl in H2. now rewrite E in H2.
  - unfold p1 in *; unfold p2 in *.
    inversion H; subst.
    + apply E_WhileFalse. simpl. now rewrite E.
    + simpl in H2. now rewrite E in H2.
  - exfalso. apply (p1_may_diverge st st'); try assumption.
    intro Contra. now rewrite E in Contra.
  - exfalso. apply (p2_may_diverge st st'); try assumption.
    intro Contra. now rewrite E in Contra.
  Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (p3_p4_inequiv)

    Prove that the following programs are _not_ equivalent.  (Hint:
    What should the value of [Z] be when [p3] terminates?  What about
    [p4]?) *)

Definition p3 : com :=
  <{ Z := 1;
     while ~(X = 0) do
       havoc X;
       havoc Z
     end }>.

Definition p4 : com :=
  <{ X := 0;
     Z := 1 }>.

Theorem p3_p4_inequiv : ~ cequiv p3 p4.
Proof. 
  unfold cequiv. intro H.
  assert ((X !-> 5) =[ p3 ]=> (Z !-> 5; X !-> 0; Z !-> 1; X !-> 5)).
  { apply E_Seq with (Z !-> 1; X !-> 5).
    * now constructor.
    * apply E_WhileTrue with (Z !-> 5; X !-> 0; Z !-> 1; X !-> 5).
      + reflexivity.
      + apply E_Seq with (X !-> 0; Z !-> 1; X !-> 5); apply E_Havoc.
      + now apply E_WhileFalse.
  }
  apply (H _ _) in H0.
  inversion H0; subst.
  inversion H3; subst. simpl in *.
  rewrite t_update_shadow in H6,H3.
  assert (X <> Z) by (intro V; discriminate).
  rewrite (t_update_permute _ _ _ _ _ _ H1) in H6.
  rewrite t_update_shadow in H6.
  assert (Z <> X) by (intro V; discriminate).
  rewrite (t_update_permute _ _ _ _ _ _ H1) in H6.
  rewrite t_update_shadow in H6.
  inversion H6; subst. simpl in *.
  assert (forall x, (Z !-> 1; X !-> 0) x = (X !-> 0; Z !-> 5) x) by (now apply equal_f).
  specialize (H4 Z). rewrite t_update_eq in H4. rewrite t_update_neq in H4; try assumption.
  rewrite t_update_eq in H4. discriminate.
  Qed.
    
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (p5_p6_equiv)

    Prove that the following commands are equivalent.  (Hint: As
    mentioned above, our definition of [cequiv] for Himp only takes
    into account the sets of possible terminating configurations: two
    programs are equivalent if and only if the set of possible terminating
    states is the same for both programs when given a same starting state
    [st].  If [p5] terminates, what should the final state be? Conversely,
    is it always possible to make [p5] terminate?) *)

Definition p5 : com :=
  <{ while ~(X = 1) do
       havoc X
     end }>.

Definition p6 : com :=
  <{ X := 1 }>.

Theorem p5_p6_equiv : cequiv p5 p6.
Proof. unfold cequiv. unfold p5. unfold p6.
  intros st st'. destruct (st X =? 1) eqn:E; split; intro H.
  - apply beq_nat_true in E.
    inversion H; subst; try simpl in H4.
    * rewrite E in H4. simpl in H4.
      assert (st' = (X !-> 1; st')).
      { apply functional_extensionality.
        intro x. destruct (string_dec X x).
        - subst. now rewrite t_update_eq.
        - rewrite t_update_neq; try reflexivity. assumption.
      }
      rewrite H0 at 2. now apply E_Asgn.
    * simpl in H2. rewrite E in H2. simpl in H2. discriminate.
  - apply beq_nat_true in E.
    inversion H; subst. simpl in *.
    assert (st = (X !-> 1; st)).
    { apply functional_extensionality.
      intro x. destruct (string_dec X x).
        - subst. now rewrite t_update_eq.
        - rewrite t_update_neq; try reflexivity. assumption.
    }
    rewrite <- H0.
    apply E_WhileFalse. simpl. now rewrite E.
  - apply beq_nat_false in E.
    remember <{ while ~ X = 1 do havoc X end }> as c eqn:Hc.
    induction H; try (discriminate); inversion Hc; subst; clear Hc.
    * simpl in H.
      replace (st X =? 1) with false in H; try discriminate.
      rewrite <- eqb_neq in E. now symmetry.
    * simpl in H.
      inversion H0; subst. inversion H0; subst. clear H0.
      rewrite t_update_eq in IHceval2.
      destruct (eqb_spec n 1).
      + subst. inversion H1; subst.
        -- now apply E_Asgn.
        -- discriminate.
      + assert (<{ while ~ X = 1 do havoc X end }> = <{ while ~ X = 1 do havoc X end }>) by reflexivity.
        specialize (IHceval2 n1 H0).
        inversion IHceval2; subst.
        simpl. rewrite t_update_shadow. now constructor.
  - inversion H; subst. simpl in *. inversion H; subst. simpl in *.
    clear H4.
    apply E_WhileTrue with (X !-> 1; st).
    + simpl. now rewrite E.
    + apply E_Havoc.
    + now apply E_WhileFalse.
  Qed.
        
(** [] *)

End Himp.

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 4 stars, standard, optional (for_while_equiv)

    This exercise extends the optional [add_for_loop] exercise from
    the [Imp] chapter, where you were asked to extend the language
    of commands with C-style [for] loops.  Prove that the command:

      for (c1; b; c2) {
          c3
      }

    is equivalent to:

       c1;
       while b do
         c3;
         c2
       end
*)
(* FILL IN HERE

    [] *)

(** **** Exercise: 3 stars, standard, optional (swap_noninterfering_assignments)

    (Hint: You'll need [functional_extensionality] for this one.) *)

Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 ->
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    <{ l1 := a1; l2 := a2 }>
    <{ l2 := a2; l1 := a1 }>.
Proof.
(* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 4 stars, advanced, optional (capprox)

    In this exercise we define an asymmetric variant of program
    equivalence we call _program approximation_. We say that a
    program [c1] _approximates_ a program [c2] when, for each of
    the initial states for which [c1] terminates, [c2] also terminates
    and produces the same final state. Formally, program approximation
    is defined as follows: *)

Definition capprox (c1 c2 : com) : Prop := forall (st st' : state),
  st =[ c1 ]=> st' -> st =[ c2 ]=> st'.

(** For example, the program

  c1 = while ~(X = 1) do
         X := X - 1
       end

    approximates [c2 = X := 1], but [c2] does not approximate [c1]
    since [c1] does not terminate when [X = 0] but [c2] does.  If two
    programs approximate each other in both directions, then they are
    equivalent. *)

(** Find two programs [c3] and [c4] such that neither approximates
    the other. *)

Definition c3 : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Definition c4 : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem c3_c4_different : ~ capprox c3 c4 /\ ~ capprox c4 c3.
Proof. (* FILL IN HERE *) Admitted.

(** Find a program [cmin] that approximates every other program. *)

Definition cmin : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem cmin_minimal : forall c, capprox cmin c.
Proof. (* FILL IN HERE *) Admitted.

(** Finally, find a non-trivial property which is preserved by
    program approximation (when going from left to right). *)

Definition zprop (c : com) : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem zprop_preserving : forall c c',
  zprop c -> capprox c c' -> zprop c'.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(* 2021-08-11 15:11 *)
