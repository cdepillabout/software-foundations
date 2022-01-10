(** * Rel: Properties of Relations *)

(** This short (and optional) chapter develops some basic definitions
    and a few theorems about binary relations in Coq.  The key
    definitions are repeated where they are actually used (in the
    [Smallstep] chapter of _Programming Language Foundations_),
    so readers who are already comfortable with these ideas can safely
    skim or skip this chapter.  However, relations are also a good
    source of exercises for developing facility with Coq's basic
    reasoning facilities, so it may be useful to look at this material
    just after the [IndProp] chapter. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

(* ################################################################# *)
(** * Relations *)

(** A binary _relation_ on a set [X] is a family of propositions
    parameterized by two elements of [X] -- i.e., a proposition about
    pairs of elements of [X].  *)

Definition relation (X: Type) := X -> X -> Prop.

(** Rather confusingly, the Coq standard library hijacks the generic
    term "relation" for this specific instance of the idea. To
    maintain consistency with the library, we will do the same.  So,
    henceforth, the Coq identifier [relation] will always refer to a
    binary relation _on_ some set (between the set and itself),
    whereas in ordinary mathematical English the word "relation" can
    refer either to this specific concept or the more general concept
    of a relation between any number of possibly different sets.  The
    context of the discussion should always make clear which is
    meant. *)

(** An example relation on [nat] is [le], the less-than-or-equal-to
    relation, which we usually write [n1 <= n2]. *)

Print le.
(* ====> Inductive le (n : nat) : nat -> Prop :=
             le_n : n <= n
           | le_S : forall m : nat, n <= m -> n <= S m *)
Check le : nat -> nat -> Prop.
Check le : relation nat.
(** (Why did we write it this way instead of starting with [Inductive
    le : relation nat...]?  Because we wanted to put the first [nat]
    to the left of the [:], which makes Coq generate a somewhat nicer
    induction principle for reasoning about [<=].) *)

(* ################################################################# *)
(** * Basic Properties *)

(** As anyone knows who has taken an undergraduate discrete math
    course, there is a lot to be said about relations in general,
    including ways of classifying relations (as reflexive, transitive,
    etc.), theorems that can be proved generically about certain sorts
    of relations, constructions that build one relation from another,
    etc.  For example... *)

(* ----------------------------------------------------------------- *)
(** *** Partial Functions *)

(** A relation [R] on a set [X] is a _partial function_ if, for every
    [x], there is at most one [y] such that [R x y] -- i.e., [R x y1]
    and [R x y2] together imply [y1 = y2]. *)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

(** For example, the [next_nat] relation defined earlier is a partial
    function. *)

Print next_nat.
(* ====> Inductive next_nat (n : nat) : nat -> Prop :=
           nn : next_nat n (S n) *)
Check next_nat : relation nat.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity.  Qed.

(** However, the [<=] relation on numbers is not a partial
    function.  (Assume, for a contradiction, that [<=] is a partial
    function.  But then, since [0 <= 0] and [0 <= 1], it follows that
    [0 = 1].  This is nonsense, so our assumption was
    contradictory.) *)

Print le.


Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense.   Qed.
  
  
  
Theorem le_not_a_partial_function2 :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  specialize (Hc 0 0 1 (le_n _) (le_S _ _ (le_n _))).
  discriminate Hc. Qed.

Theorem le_not_a_partial_function3 :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1).
  { apply (Hc 0); repeat constructor. }
  discriminate H.
  Qed.

(** **** Exercise: 2 stars, standard, optional (total_relation_not_partial)

    Show that the [total_relation] defined in (an exercise in)
    [IndProp] is not a partial function. *)

Print total_relation.

Theorem total_relation_not_a_partial_function : ~ (partial_function total_relation).
Proof.
  intros Hc.
  discriminate (Hc 0 0 1 (total_rel _ _) (total_rel _ _)).
Qed.


(** **** Exercise: 2 stars, standard, optional (empty_relation_partial)

    Show that the [empty_relation] defined in (an exercise in)
    [IndProp] is a partial function. *)

Inductive empty_relation (n m : nat) : Prop :=.

Theorem empty_relation_is_partial_function : partial_function empty_relation.
Proof.
  intros ? ? ? H1. destruct H1.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Reflexive Relations *)

(** A _reflexive_ relation on a set [X] is one for which every element
    of [X] is related to itself. *)

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Transitive Relations *)

(** A relation [R] is _transitive_ if [R a c] holds whenever [R a b]
    and [R b c] do. *)

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - (* le_n *) apply Hnm.
  - (* le_S *) apply le_S. apply IHHmo.  Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

(** **** Exercise: 2 stars, standard, optional (le_trans_hard_way)

    We can also prove [lt_trans] more laboriously by induction,
    without using [le_trans].  Do this. *)

Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that [m] is less than [o]. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  - constructor. auto.
  - apply le_S in IHHm'o. auto.
  Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (lt_trans'')

    Prove the same thing again by induction on [o]. *)

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o' IHo].
  - inversion Hmo.
  - apply le_S_n in Hmo. apply le_n_S.
    fold (lt n m) in Hnm.
    fold (lt m o') in IHo.
    fold (lt n o') in IHo.
    destruct m,n.
    + assumption.
    + inversion Hnm.
    + apply le_0_n.
    + fold (lt m o') in Hmo.
      fold (lt n o').
      apply Lt.lt_S_n in Hnm.
      inversion Hmo.
      * apply PeanoNat.Nat.lt_lt_succ_r. assumption.
      * rewrite <- H0 in IHo,Hmo.
        clear H0 o'.
        fold (lt m m0) in H.
        apply Lt.lt_n_S in H.
        apply IHo in H.
        apply Lt.lt_S_n in H.
        apply PeanoNat.Nat.lt_lt_succ_r.
        assumption.
Qed.

(*
Theorem lt_trans''' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o' IHo].
  - induction m as [| m' IHm].
    + induction n as [| n' IHn].
      * 
  - 
Qed.
*)

(** The transitivity of [le], in turn, can be used to prove some facts
    that will be useful later (e.g., for the proof of antisymmetry
    below)... *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.

Print Sn_le_Sm__n_le_m.

Theorem le_S_S2 : forall n m, S n <= S m -> n <= m.
Proof.
  (*
  induction n.
  - intros. inversion H.
    * constructor.
    * apply PeanoNat.Nat.le_0_l.
  - intros. inversion H.
    * constructor.
    * induction m.
      + inversion H1.
      +  
    * inversion H.
      + constructor.
      + 
  *) 
  (*
  intros n m H. inversion H.
  - constructor.
  - 
  *)
  intros n m. generalize dependent n.
  induction m.
  - intros. inversion H.
    + constructor.
    + inversion H1.
  - intros.
    inversion H.
    + constructor.
    + apply IHm in H1.
      constructor.
      assumption.
  (*
  intros. inversion H as [|m' Hm' a].
  + auto.
  + inversion Hm' as [b|m''].
    - auto.
    - generalize dependent n.
      induction m.
      * intros. inversion Hm'.
      * intros.
  *)
  (*
  intros n m H. inversion H; auto.
  - destruct n,m; auto.
    + induction m; auto. admit.
    + inversion H1.
  *)
  Qed.

Theorem le_Sn_le2 : forall n m, S n <= m -> n <= m.
Proof.
  (*
  intros n m H. induction H.
  - constructor. constructor.
  - auto.
  *)
  intros n m. generalize dependent n.
  induction m.
  - intros. inversion H.
  - intros.
    inversion H.
    + auto.
    + constructor. apply IHm. apply H1.
Qed.

(** **** Exercise: 1 star, standard, optional (le_S_n) *)
Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  (*
  intros. apply le_trans with (b := S n).
  - constructor. constructor.
  - inversion H.
    +  
  *)
  (*
  intros n m H. inversion H.
  - constructor.
  - (* apply (le_Sn_le2 _ _ H1). *)
  *)
  (*
  intros n. induction n.
  - intros. induction m. 
    + constructor.
    + 
    +  constructor.
    +  
  *)
  intros n m. generalize dependent n.
  induction m.
  - intros. inversion H.
    + constructor.
    + inversion H1.
  - intros. 
    inversion H.
    + constructor.
    + specialize (IHm _ H1).
      constructor. auto.
  Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (le_Sn_n_inf)

    Provide an informal proof of the following theorem:

    Theorem: For every [n], [~ (S n <= n)]

    A formal proof of this is an optional exercise below, but try
    writing an informal proof without doing the formal proof first.

    Proof: *)
    (* FILL IN HERE

    [] *)

(** **** Exercise: 1 star, standard, optional (le_Sn_n) *)
Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  (*
  set (G := PeanoNat.Nat.neq_succ_diag_l).
  unfold PeanoNat.Nat.neq_succ_diag_l in G.
  *)
  (*
  intros n H. inversion H.
  - induction n.
    + inversion H0.
    + 
  - 
  *)
  (*
  unfold not.
  induction n.
  - intros. inversion H.
  - intros. inversion H.
    + set (G := le_n n).
      rewrite <- H1 in G at 1.
      apply (IHn G).
    + apply le_Sn_le2 in H1.
      apply (IHn H1).
  *)
  (*
  unfold not.
  intros n H.
  induction H as [|].
  - admit.
  - auto.  
  *)
  unfold not.
  induction n.
  - intros. inversion H.
  - intros. apply IHn.
    apply le_S_S2. auto.
  Qed.
  
(** [] *)

(** Reflexivity and transitivity are the main concepts we'll need for
    later chapters, but, for a bit of additional practice working with
    relations in Coq, let's look at a few other common ones... *)

(* ----------------------------------------------------------------- *)
(** *** Symmetric and Antisymmetric Relations *)

(** A relation [R] is _symmetric_ if [R a b] implies [R b a]. *)

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

(** **** Exercise: 2 stars, standard, optional (le_not_symmetric) *)
Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  unfold not. unfold symmetric.
  intro H.
  specialize (H 0 1 (le_S _ _ (le_n 0))).
  inversion H.
Qed.
(** [] *)

(** A relation [R] is _antisymmetric_ if [R a b] and [R b a] together
    imply [a = b] -- that is, if the only "cycles" in [R] are trivial
    ones. *)

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(** **** Exercise: 2 stars, standard, optional (le_antisymmetric) *)
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  intros a b Haleb Hblea.
  induction Haleb as [| b _ ].
  - reflexivity.
  - specialize (IHHaleb (le_Sn_le _ _ Hblea)).
    rewrite <- IHHaleb in Hblea.
    rewrite IHHaleb.
    clear IHHaleb.
    fold (lt a a) in Hblea.
    induction a.
    * inversion Hblea.
    * apply IHa.
      apply Lt.lt_S_n.
      assumption.
Qed.
    
    
Theorem le_antisymmetric' :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  induction a as [|a' IHa].
  - intros. inversion H0. reflexivity.
  - intros b Ha'leb Hblea'.
    fold (lt a' b) in Ha'leb.
    destruct b.
    * inversion Ha'leb.
    * unfold lt in Ha'leb.
      apply Le.le_S_n in Ha'leb.
      apply Le.le_S_n in Hblea'.
      f_equal.
      apply IHa; assumption.
Qed.       
(** [] *)

(** **** Exercise: 2 stars, standard, optional (le_step) *)
Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  unfold lt.
  intros n m p H1 H2.
  apply le_S_n. 
  apply PeanoNat.Nat.le_trans with (m := m); auto.
Qed.

Theorem le_step_2 : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  (*
  unfold lt.
  intros n m. generalize dependent n.
  induction m as [|m' IHm].
  - intros. inversion H.
  - intros n p H1 H2.
    induction p as [|p' IHp].
    * inversion H2.
      + rewrite H0 in H2,H1.
        inversion H1.
        -- constructor.
        -- inversion H3.
      + inversion H0.
    * inversion H2.
      + rewrite H0 in IHp,H2,H1,IHm.
        clear H2. clear IHp. clear H0.
  *)
  (*
  unfold lt.
  intros n m p. generalize dependent n. generalize dependent m.
  induction p as [|p' IHp].
  - intros n m. generalize dependent n.
    induction m as [|p' IHp].
    + auto.
    + intros.
      destruct n.
      * inversion H.
      * inversion H0.
        -- rewrite H2 in H.
           inversion H.
           inversion H3.
        -- inversion H2.
  - induction m as [|m' IHm].
    + intros ? H. inversion H.
    + intros n H1 H2.
      inversion H2.
      * rewrite H0 in H2,H1,IHm.
        clear H0 H2.
        inversion H1.
        -- auto.
        -- clear H m.
           apply IHm; auto.
      * clear H m.
        inversion H1.
        -- rewrite <- H3 in H1. clear H3 H1.
  *)
  (*
  unfold lt.
  intros n m p. generalize dependent n. generalize dependent m.
  induction p as [|p' IHp].
  - intros n m. generalize dependent n.
    induction m as [|p' IHp].
    + auto.
    + intros.
      destruct n.
      * inversion H.
      * inversion H0.
        -- rewrite H2 in H.
           inversion H.
           inversion H3.
        -- inversion H2.
  - intros m n H1 H2.
    induction H1.
    *)
  (*  
  unfold lt.
  intros n m p H1 H2. inversion H2.
  * admit.
  * clear m0 H.
  *)
  Admitted.

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Equivalence Relations *)

(** A relation is an _equivalence_ if it's reflexive, symmetric, and
    transitive.  *)

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(* ----------------------------------------------------------------- *)
(** *** Partial Orders and Preorders *)

(** A relation is a _partial order_ when it's reflexive,
    _anti_-symmetric, and transitive.  In the Coq standard library
    it's called just "order" for short. *)

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

(** A preorder is almost like a partial order, but doesn't have to be
    antisymmetric. *)

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split.
    - (* refl *) apply le_reflexive.
    - split.
      + (* antisym *) apply le_antisymmetric.
      + (* transitive. *) apply le_trans.  Qed.

(* ################################################################# *)
(** * Reflexive, Transitive Closure *)

(** The _reflexive, transitive closure_ of a relation [R] is the
    smallest relation that contains [R] and that is both reflexive and
    transitive.  Formally, it is defined like this in the Relations
    module of the Coq standard library: *)

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
  | rt_step x y (H : R x y) : clos_refl_trans R x y
  | rt_refl x : clos_refl_trans R x x
  | rt_trans x y z
        (Hxy : clos_refl_trans R x y)
        (Hyz : clos_refl_trans R y z) :
        clos_refl_trans R x z.

(** For example, the reflexive and transitive closure of the
    [next_nat] relation coincides with the [le] relation. *)

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  - (* -> *)
    intro H. induction H.
    + (* le_n *) apply rt_refl.
    + (* le_S *)
      apply rt_trans with m. apply IHle. apply rt_step.
      apply nn.
  - (* <- *)
    intro H. induction H.
    + (* rt_step *) inversion H. apply le_S. apply le_n.
    + (* rt_refl *) apply le_n.
    + (* rt_trans *)
      apply le_trans with y.
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2. Qed.

(** The above definition of reflexive, transitive closure is natural:
    it says, explicitly, that the reflexive and transitive closure of
    [R] is the least relation that includes [R] and that is closed
    under rules of reflexivity and transitivity.  But it turns out
    that this definition is not very convenient for doing proofs,
    since the "nondeterminism" of the [rt_trans] rule can sometimes
    lead to tricky inductions.  Here is a more useful definition: *)

Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.

(** Our new definition of reflexive, transitive closure "bundles"
    the [rt_step] and [rt_trans] rules into the single rule step.
    The left-hand premise of this step is a single use of [R],
    leading to a much simpler induction principle.

    Before we go on, we should check that the two definitions do
    indeed define the same relation...

    First, we prove two lemmas showing that [clos_refl_trans_1n] mimics
    the behavior of the two "missing" [clos_refl_trans]
    constructors.  *)

Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
  R x y -> clos_refl_trans_1n R x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y. apply H. apply rt1n_refl.   Qed.

(** **** Exercise: 2 stars, standard, optional (rsc_trans) *)
Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y  ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  intros ? ? x y z HCxy HCyz.
  induction HCxy.
  - assumption.
  - specialize (IHHCxy HCyz).
    apply rt1n_trans with y; assumption.
  Qed. 

(*
Lemma rsc_trans' :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y  ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  intros ? ? x y z HCxy HCyz.
  inversion HCyz as [Hxx|y' z' HR Hrest ffff].
  - rewrite <- Hxx. assumption.
  - clear ffff z'.
    inversion HCxy as [Hxx|x' y'' HRx Hrestxy gggg].
    + assumption.
    + clear gggg y''.
      cut (clos_refl_trans_1n R x' z).
      { intros. apply rt1n_trans with x'; assumption. }
      
  Qed.
*)


(*
Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z. *)

(** Then we use these facts to prove that the two definitions of
    reflexive, transitive closure do indeed define the same
    relation. *)

(** **** Exercise: 3 stars, standard, optional (rtc_rsc_coincide) *)
Theorem rtc_rsc_coincide :
  forall (X:Type) (R: relation X) (x y : X),
    clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  intros X R x y. split.
  - intros H. induction H.
    + apply rt1n_trans with y; auto. apply rt1n_refl.
    + apply rt1n_refl.
    + apply rsc_trans with y; assumption.
  - intros H. induction H.
    + apply rt_refl.
    + apply rt_trans with y.
      * apply rt_step. assumption.
      * assumption.
  Qed.
  
(*
Theorem rtc_rsc_coincide' :
  forall (X:Type) (R: relation X) (x y : X),
    clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  intros X R x y. split.
  - intros H. inversion H.
    + apply rt1n_trans with y; auto. apply rt1n_refl.
    + apply rt1n_refl.
    + apply rsc_trans with y0. assumption.
  - intros H. induction H.
    + apply rt_refl.
    + apply rt_trans with y.
      * apply rt_step. assumption.
      * assumption.
  Qed. 
*)
(** [] *)

(* 2021-08-11 15:08 *)












































Lemma rsc_R_2 : forall (X : Type) (R : relation X) (x y : X),
  R x y -> clos_refl_trans_1n R x y.
Proof.
  intros. apply (rt1n_trans R x y y).
  - auto.
  - apply (rt1n_refl R y).
  Qed.
  
Theorem next_nat_closure_is_le_2 : forall n m,
  (n <= m) <-> clos_refl_trans next_nat n m.
Proof.
  split.
  - intros H.
    induction H.
    + apply rt_refl.
    + apply rt_trans with (y := m).
      -- auto.
      -- apply rt_step. apply nn.
  - intros H.
    induction H.
    + inversion H. constructor. constructor.
    + constructor.
    + apply (le_trans x y z); auto.
  Qed.

Theorem next_nat_closure_is_le_3 : forall n m,
  (n <= m) <-> clos_refl_trans next_nat n m.
Proof.
  intros n m. generalize dependent n.
  induction m as [|m' IHm].
  - split. 
    + intros. inversion H. apply rt_refl.
    + intros. induction H. 
      * inversion H. constructor. constructor.
      * constructor.
      * apply (le_trans x y z); auto.
  - split.
    + intros H.
      inversion H.
      * apply rt_refl.
      * clear H0 m H.
        apply IHm in H1.
        apply rt_trans with (y := m').
        -- auto.
        -- apply rt_step. apply nn.
    + intros H.
      induction H.
      * destruct H. constructor. constructor.
      * constructor.
      * apply (le_trans x y z); auto.
  Qed.

Lemma clos_refl_trans_is_trans :
  forall A f (n y m : A),
  clos_refl_trans f n y -> clos_refl_trans f y m -> clos_refl_trans f n m.
Proof.
  intros A f n y m Hny Hym.
  induction Hym.
  - apply rt_step in H.
    apply rt_trans with x; assumption.
  - assumption.
  - apply IHHym2.
    apply IHHym1.
    apply Hny.
  Qed.

Theorem eq_closure_is_eq : forall A (n m : A),
  (n = m) <-> clos_refl_trans eq n m.
Proof.
  split.
  - intros. inversion H. constructor. reflexivity.
  - intros. induction H.
    + assumption.
    + reflexivity.
    + rewrite IHclos_refl_trans1. auto.
  Qed.
  
Theorem f_closure_is_f : forall A f (n m : A), reflexive f -> transitive f ->
  (f n m) <-> clos_refl_trans f n m.
Proof.
  unfold reflexive. unfold transitive.
  intros A f n m reflF transF.
  split.
  - intros. apply rt_step. assumption.
  - intros. induction H.
    + assumption.
    + apply reflF.
    + apply transF with y; assumption.
  Qed.
  
Inductive city :=
  | Bal
  | Chicago
  | LA
  | Houston
  .
  
Inductive flight : city -> city -> Prop :=
  | BalChi : flight Bal Chicago
  | ChiLA : flight Chicago LA
  | LAHou : flight LA Houston
  | HouBal : flight Houston Bal
  .
  
Inductive reachable : city -> city -> Prop :=
  | inCity : forall c, reachable c c
  | directFlight : forall b c d, reachable b c -> flight c d -> reachable b d
  .

Theorem flight_closure_is_reachable : forall n m, reachable n m <-> clos_refl_trans flight n m.
Proof.
  split.
  - intros Hreachable. induction Hreachable as [ c | b c d HReachable HClos HFlight ].
    + apply rt_refl.
    + apply rt_step in HFlight.
      apply rt_trans with c; assumption.
  - intros HClos. induction HClos.
    + apply directFlight with x.
      * apply inCity.
      * assumption.
    + apply inCity.
    + cut (forall a b c, reachable a b -> reachable b c -> reachable a c).
      * intros. apply H with y; auto.
      * clear.
        intros a b c rab rbc.
        induction rbc.
        -- auto.
        -- apply IHrbc in rab.
           apply directFlight with c; auto.
  Qed.
