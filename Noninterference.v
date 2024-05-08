(** * Noninterference: Defining Secrecy and Secure Multi-Execution *)

(** HIDE: A nice example here could be that of Moodle. Students shouldn't have
    access to / lean information about each other's grade, or to the solutions
    while the homework is still on. This quickly brings up declassification. We
    sometimes can release aggregate data, like the average grade. Or certain
    private things become public at some point in time: homework solutions. *)

(** Information flow control tries to prevent the leak of secret information to
    public outputs.

    But how does one formalize that a program doesn't leak secret information?

    We first investigate this question in the very simple setting of Coq
    functions taking two arguments, one we call the public input and the other
    one we call the secret input. Our functions return a pair containing one
    public output and one secret output. *)

(** Say we have the following function working on natural numbers: *)

Definition secure_f (pi si : nat) : nat*nat := (pi+1, pi+si*2).

(** This function seems intuitively secure, since the first output [pi+1], which
    we assume to be public, only depends on the public input [pi], but not on
    the secret input [si]. The second output [pi+si*2] depends on both the
    public input and the secret input, but that's okay, since we assume this
    second output to be secret. Still, what security notion does this function
    satisfy? Let's try it on a couple of inputs: *)

Example example1_secure_f : secure_f 0 0 = (1,0).
Proof. reflexivity. Qed.

Example example2_secure_f : secure_f 0 1 = (1,2).
Proof. reflexivity. Qed.

Example example3_secure_f : secure_f 1 2 = (2,5).
Proof. reflexivity. Qed.

(** In the last two cases the value of the public output is equal to the value
    of secret input. But that's just a coincidence, and has nothing to do with
    the public output leaking the secret input, which wasn't used in computing
    the public output.

    So a naive security definition, which we'll only use as a strawman, is one
    that simply compares secret inputs with public outputs: *)

Definition broken_def (f : nat -> nat -> nat*nat) :=
  forall pi si, fst (f pi si) <> si.

(** This definition would reject our secure function above as insecure: *)

Lemma broken_def_rejects_secure_f : ~broken_def secure_f.
Proof.
  unfold broken_def. intros contra.
  apply (contra 0 1). reflexivity.
Qed.

(** Even worse, this broken definition of security would allow insecure
    functions, such as the following one whose public output is [si+1]: *)

Definition insecure_f (pi si : nat) : nat*nat := (si+1, pi+si*2).

(** This function's public output is never equal to its secret input, yet an
    attacker can easily compute one from the other by just subtracting [1]. So
    the secret is entirely leaked, yet our broken definition accepts this: *)

Lemma broken_def_accepts_insecure_f : broken_def insecure_f.
Proof.
  unfold broken_def. intros pi si. induction si as [| si' IH].
  - simpl. intros contra. discriminate contra.
  - simpl in *. intro Hc. injection Hc as Hc. apply IH. apply Hc.
Qed.

(** This attempt at defining secure information flow by looking at how inputs
    and outputs are related for a single execution of the program has failed.
    In fact, it is well known in the formal security research community that
    secure information flow cannot be defined by looking at just one single
    program execution. *)


(** * Noninterference for pure functions *)

(** The usual way to define secure information flow is a property called
    _noninterference_, which in its most standard form looks at _two_ program
    executions: for two different secret inputs the public outputs should not
    change: *)

Definition noninterferent {PI SI PO SO : Type} (f : PI -> SI -> PO*SO) :=
  forall (pi:PI) (si1 si2:SI), fst (f pi si1) = fst (f pi si2).

(** We defined this for arbitrary types of inputs and outputs, but we can still
    instantiate them to [nat] when looking at our example functions above: *)

Lemma noninterferent_secure_f : noninterferent secure_f.
Proof.
  unfold noninterferent, secure_f. simpl. reflexivity.
Qed.

Lemma interferent_insecure_f : ~noninterferent insecure_f.
Proof.
  unfold noninterferent, insecure_f. simpl. intros contra.
  specialize (contra 0 0 1). discriminate contra.
Qed.

(** The tactic [specialize] we used above instantiates a quantified hypothesis to
    the concrete arguments we specify. *)

(** In the definition of noninterference we pass the same public inputs to the
    two executions, since this allows public outputs to depend on public
    inputs. To convince ourselves of this, let's look at the following too
    strong definition of security: *)

Definition too_strong_def {PI SI PO SO : Type} (f : PI -> SI -> PO*SO) :=
  forall (pi1 pi2:PI) (si1 si2:SI), fst (f pi1 si1) = fst (f pi2 si2).

(** This basically says that the first output of [f] has to be constant, which
    is not the case for our [secure_f]. *)

Lemma secure_f_rejected_again : ~too_strong_def secure_f.
Proof.
  unfold too_strong_def, secure_f. simpl. intros contra.
  specialize (contra 0 1 0 0). discriminate contra.
Qed.

(** Noninterference is still a very strong property. In particular, [f] being
    noninterferent is equivalent to [f] being splittable into two different
    functions, one of which doesn't get the secret at all. *)

Definition splittable {PI SI PO SO : Type} (f : PI -> SI -> PO*SO) :=
  exists (pf : PI -> PO) (sf:PI -> SI -> SO),
    forall pi si , f pi si = (pf pi, sf pi si).

Theorem splittable_noninterferent : forall PI SI PO SO : Type,
  forall f : PI -> SI -> PO*SO, splittable f -> noninterferent f.
Proof.
  unfold splittable, noninterferent.
  intros PI SI PO SO f [pf [sf H]] pi si1 si2.
  rewrite H. rewrite H. simpl.
  reflexivity.
Qed.

Theorem noninterferent_splittable : forall PI SI PO SO : Type,
  forall some_si : SI, (* we require SI to be an inhabited type! *)
  forall f : PI -> SI -> PO*SO, noninterferent f -> splittable f.
Proof.
  unfold splittable, noninterferent.
  intros PI SI PO SO some_si f Hni.
  (* we pass the SI inhabitant as a dummy secret value! *)
  exists (fun pi => fst (f pi some_si)).
  exists (fun pi si => snd (f pi si)).
  intros pi si. rewrite (Hni _ _ si).
  destruct (f pi si) as [po so]. reflexivity.
Qed.


(** * Secure Multi-Execution (SME) *)

(** The previous proof also captures the key idea behind Secure Multi-Execution
    (SME), an enforcement mechanism that can make _any_ function
    noninterferent. To achieve this SME runs the function twice, once passing a
    dummy secret as input to obtain the public output, and once using the real
    secrets to obtain the secret output. *)

Definition sme {PI SI PO SO : Type} (some_si : SI)
  (f : PI -> SI -> PO*SO) pi si :=
    (fst (f pi some_si), snd (f pi si)).

(** Functions protected by [sme] are guaranteed to satisfy noninterference: *)

Theorem noninterferent_sme :  forall PI SI PO SO : Type,
  forall some_si : SI,
  forall f : PI -> SI -> PO*SO,
    noninterferent (sme some_si f).
Proof.
  intros PI SI PO SO some_si f pi si1 si2. simpl. reflexivity.
Qed.

(** Moreover, if the function we pass to [sme] is already noninterferent,
    then its behavior will not change; so we say that [sme] is a _transparent_
    enforcement mechanism for noninterference: *)

Theorem transparent_sme : forall PI SI PO SO : Type,
  forall some_si : SI,
  forall f : PI -> SI -> PO*SO,
    noninterferent f -> forall pi si, f pi si = sme some_si f pi si.
Proof.
  unfold noninterferent, sme. intros PI SI PO SP some_si f Hni pi si.
  rewrite (Hni _ _ si).
  destruct (f pi si) as [po so]. reflexivity.
Qed.

(** It is interesting to look at what [sme] does for _interferent_ functions,
    like [insecure_f], whose public output was one plus its secret input: *)

Example example1_sme_insecure_f: sme 0 insecure_f 0 0 = (1, 0).
Proof. reflexivity. Qed.

Example example2_sme_insecure_f: sme 0 insecure_f 0 1 = (1, 2).
Proof. reflexivity. Qed.

Example example3_sme_insecure_f: sme 0 insecure_f 1 1 = (1, 3).
Proof. reflexivity. Qed.

(** Now the public output is one plus the dummy constant [0] we passed to the
   [sme] function, so always the constant [1]. *)

Lemma constant_sme_insecure_f: forall pi si,
  fst (sme 0 insecure_f pi si) = 1.
Proof. reflexivity. Qed.

(** This is a secure behavior, but a behavior that's different than that of the
    original [insecure_f] function. So we are giving up some correctness for
    security. There is no free lunch! *)

(** The other downside of [sme] is that we have to run the function twice for
    our two security levels, public and secret. In general, we need to run the
    program as many times as we have security levels, which is often an
    exponential number, say if we take our security levels to be sets of
    principals.

    Other information flow control mechanisms overcome this downside, but have
    other downsides of their own, for instance:
        - by requiring complex manual proofs for each individual program
          (e.g. Relational Hoare Logic), or
        - by using static overapproximations that reject some secure programs
          (security type systems), or
        - by using dynamic overapproximations that unnecessarily change program
          behavior, for instance forcefully terminating even some secure
          programs to prevent leaks, in which case they are not transparent
          (dynamic information flow control).

    Again, there is no free lunch! *)


(** * Noninterference for state transformers *)

(** This development is easy to adapt to functions that transform states
    ([state->state]), where we label each variable as either public or secret. *)

From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From SECF Require Import Maps.
From SECF Require Import Imp.

Print state. (* state = total_map nat = string -> nat *)

Definition pub_map := total_map bool.

Definition pub_equiv (pub : pub_map) (s1 s2 : state) :=
  forall x:string, pub x = true -> s1 x = s2 x.

Definition noninterferent_state (pub : pub_map) (f : state -> state) :=
  forall s1 s2, pub_equiv pub s1 s2 -> pub_equiv pub (f s1) (f s2).

(** We can prove an equivalence between [noninterferent_state] and our original
    [noninterferent] definition. For this we need to split and merge states,
    and a few helper lemmas. *)

(** HIDE: CH: Using total maps doesn't particularly help intuition when it comes
    to splitting and merging. This seems to be what Imp uses, and it's probably
    convenient not to be in an error monad everywhere, but if needed Maps.v also
    defines partial maps. *)

(** The way we define [split_state] and [merge_state] is a good example of
    programming with higher-order functions, and there's more of this in
    \CHAP{Maps}.

    The [split_state] function takes a state [s] and zeroes out the variables
    [x] for which [pub x] is different than an argument bit [b]. So
    [split_state s pub true] keeps the public variables, and zeroes out the
    secret ones. Dually, [split_state s pub false] keeps the secret variables,
    and zeroes out the public ones.  *)

Definition split_state (s:state) (pub:pub_map) (b:bool) : state :=
  fun x : string => if Bool.eqb (pub x) b then s x else 0.

(** HIDE: CH: Unclear whether going for curried functions was the best design
    choice for some of these definitions, like split_state. In it's current form
    it's only better for SME, where we only have to split one way. *)

(** The [merge_state] function takes in two states [s1] and [s2] and produces a
    new state that contains the public variables from [s1] and the private
    variables from [s2]. *)

Definition merge_states (s1 s2:state) (pub:pub_map) : state :=
  fun x : string => if pub x then s1 x else s2 x.

(** The technical development needed for the equivalence proof between
    [noninterferent_state] and our original [noninterferent] definition is not
    that interesting though, and can be skipped on first read. *)

Definition split_state_fun (pub : pub_map) (mf : state -> state) :=
  fun s1 s2 : state => let ms := mf (merge_states s1 s2 pub) in
                       (split_state ms pub true, split_state ms pub false).

Definition pub_equiv_split (pub : pub_map) (s1 s2 : state) :=
  forall x:string, (split_state s1 pub true) x = (split_state s2 pub true) x.

Theorem pub_equiv_split_iff : forall pub s1 s2,
  pub_equiv pub s1 s2 <-> pub_equiv_split pub s1 s2.
Proof.
  unfold pub_equiv, pub_equiv_split, split_state. intros. split.
  - intros H x. destruct (Bool.eqb_spec (pub x) true).
    + apply H. apply e.
    + reflexivity.
  - intros H x. specialize (H x). destruct (Bool.eqb_spec (pub x) true).
    + intros _. apply H.
    + contradiction.
Qed.

Theorem pub_equiv_merge_states : forall pub s z1 z2,
  pub_equiv pub (merge_states s z1 pub) (merge_states s z2 pub).
Proof.
  unfold pub_equiv, merge_states. intros pub s z1 z2 x Hx.
  rewrite Hx. reflexivity.
Qed.

Require Import FunctionalExtensionality.

Theorem merge_states_split_state : forall s pub,
  merge_states (split_state s pub true) (split_state s pub false) pub = s.
Proof.
  unfold merge_states, split_state. intros s pub.
  apply functional_extensionality. intro x.
  destruct (pub x) eqn:Heq; reflexivity.
Qed.

(** Now we can finally state our theorem about the equivalence between
    [non_interferent_state] and [noninterferent]: *)

Theorem noninterferent_state_ni : forall pub f,
  noninterferent_state pub f <->
  noninterferent (split_state_fun pub f).
Proof.
  unfold noninterferent_state, noninterferent, split_state_fun.
  intros pub f. split.
  - intros H s z1 z2. simpl.
    assert (H' : pub_equiv pub (merge_states s z1 pub) (merge_states s z2 pub)).
      { apply pub_equiv_merge_states. }
    apply H in H'. rewrite pub_equiv_split_iff in H'.
    unfold pub_equiv_split in H'. apply functional_extensionality. apply H'.
  - intros H s1 s2 Hequiv. simpl in H.
    rewrite pub_equiv_split_iff in Hequiv. unfold pub_equiv_split in Hequiv.
    rewrite pub_equiv_split_iff. unfold pub_equiv_split. intro x.
    specialize (H (split_state s1 pub true)
                  (split_state s1 pub false)
                  (split_state s2 pub false)).
    rewrite merge_states_split_state in H.
    apply functional_extensionality in Hequiv. rewrite Hequiv in H.
    rewrite merge_states_split_state in H.
    rewrite H. reflexivity.
Qed.

(* HIDE: I guess a similar equivalence can be proved by starting with a split
   function and turning that into a merged-state function? *)
(* HIDE *)
Definition merged_state_fun (pub : pub_map) (sf : state -> state -> state*state) :=
  fun s : state => merge_states (split_state s pub true)
                                (split_state s pub false) pub.
(* /HIDE *)


(** * SME for state transformers *)

Definition sme_state (f : state -> state) (pub:pub_map) :=
  fun s => merge_states (f (split_state s pub true)) (f s) pub.

(* HIDE: Is this related to [sme] and/or [split_state_fun] and/or
         [merge_state_fun] above? *)
(* HIDE: Definition sme (f : PI -> SI -> PO*SO) x y := *)
(* HIDE:   (fst (f x some_si), snd (f x y)). *)
(* HIDE: Definition split_state_fun (pub : pub_map) (f : state -> state) := *)
(* HIDE:   fun s1 s2 : state => let ms := f (merge_states s1 s2 pub) in *)
(* HIDE:                        (split_state ms pub true, split_state ms pub false). *)

Theorem noninterferent_sme_state : forall pub f,
  noninterferent_state pub (sme_state f pub).
Proof.
  unfold noninterferent_state, sme_state. intros pub f s1 s2 Hequiv.
  rewrite pub_equiv_split_iff in Hequiv. unfold pub_equiv_split in Hequiv.
  apply functional_extensionality in Hequiv. rewrite Hequiv.
  apply pub_equiv_merge_states.
Qed.

Theorem transparent_sme_state : forall f pub,
  noninterferent_state pub f -> forall s, f s = sme_state f pub s.
Proof.
  unfold noninterferent_state, sme_state.
  intros f pub Hni s.
  unfold merge_states, split_state. unfold pub_equiv in Hni.
  apply functional_extensionality. intro x.
  destruct (pub x) eqn:Eq.
  - apply Hni. intros x' Hx'.
    destruct (Bool.eqb_spec (pub x') true).
    + reflexivity.
    + contradiction.
    + assumption.
  - reflexivity.
Qed.

(** One thing to note in this proof is that we used the lemma [Bool.eqb_spec] to
    do case analysis on whether the [pub x'] is equal to [true]. For more
    details on how this works, please check out the explanations about the
    [reflect] inductive predicate in \CHAP{IndProp}. *)

(** HIDE: These are easy to prove, but they may also follow from the (putative)
    connection to [sme] (see comments above). Unsure whether it's worth it. *)


(** * Noninterference and SME for Imp programs without loops *)

(** For programs without loops the "failed attempt" evaluation function from
   \CHAP{Imp} works well and allows us to easily define a state transformer
   function for each command. *)

Print ceval_fun_no_while.

Definition noninterferent_no_while pub c : Prop :=
  noninterferent_state pub (fun s => ceval_fun_no_while s c).

Definition xpub : pub_map :=
  (X !-> true;
   _ !-> false).

Definition secure_com : com :=
  <{ X := X+1;
     Y := X+Y*2 }>.

(** For proving [secure_com] noninterferent we first prove a few
    helper lemmas. *)

Lemma xpub_true : forall x, xpub x = true -> x = X.
Proof.
  unfold xpub. intros x Hx.
  destruct (eqb_spec x X).
  - subst. reflexivity.
  - rewrite t_update_neq in Hx.
    + rewrite t_apply_empty in Hx. discriminate.
    + intro contra. subst. contradiction.
Qed.

(** Here we are using the [t_update_neq] and [t_apply_empty] lemmas that were
    proved in \CHAP{Maps} *)

Lemma xpubX : xpub X = true.
Proof. reflexivity. Qed.

(** Using these lemmas the noninterference proof for [secure_com] is easy: *)

Lemma noninterferent_secore_com :
  noninterferent_no_while xpub secure_com.
Proof.
  unfold noninterferent_no_while, noninterferent_state,
         secure_com, pub_equiv.
  intros s1 s2 H x Hx. simpl. apply xpub_true in Hx.
  subst. rewrite (H X xpubX). reflexivity.
Qed.

(** Now let's look at a couple of insecure commands: *)

Definition insecure_com1 : com :=
  <{ X := Y+1; (* <- bad explicit flow! *)
     Y := X+Y*2 }>.

(** An _explicit flow_ is when a command directly assigns an expression
    depending on secret variables to a public variable, like the [X := Y+1]
    assignment above. We can prove that this is insecure: *)

Lemma interferent_secore_com1 :
  ~noninterferent_no_while xpub insecure_com1.
Proof.
  unfold noninterferent_no_while, noninterferent_state,
         insecure_com1, pub_equiv.
  intro Hc. simpl in Hc.
  specialize (Hc (X !-> 0 ; Y !-> 0) (X !-> 0 ; Y !-> 1)).
  assert (H: forall x, xpub x = true ->
                       (X !-> 0; Y !-> 0) x = (X !-> 0; Y !-> 1) x).
  { clear Hc. intros x H. apply xpub_true in H. subst. reflexivity. }
  specialize (Hc H X xpubX). simpl in Hc.
  repeat try rewrite t_update_eq in Hc.
  discriminate.
Qed.

(** Noninterference can be violated not only by explicit flows, but also by
    _implicit flows_, which leak secret information via the control-flow of the
    program. Here is a simple example: *)

Definition insecure_com2 : com :=
  <{ if Y = 0 then
       Y := 42
     else
       X := X+1 (* <- bad implicit flow! *)
     end }>.

(** Here the expression [X+1] we are assigning to [X] is public information, but
    we are doing this assignment after we branched on a secret condition [Y =
    0], so we are indirectly leaking information about the value of [Y]. In this
    case we can infer that if [X] gets incremented the value of [Y] is not [0]. *)

Lemma interferent_secore_com2 :
  ~noninterferent_no_while xpub insecure_com2.
Proof.
  (* same insecurity proof as for [insecure_com1] does the job *)
  unfold noninterferent_no_while, noninterferent_state,
         insecure_com2, pub_equiv.
  intro Hc. simpl in Hc.
  specialize (Hc (X !-> 0 ; Y !-> 0) (X !-> 0 ; Y !-> 1)).
  assert (H: forall x, xpub x = true ->
                       (X !-> 0; Y !-> 0) x = (X !-> 0; Y !-> 1) x).
  { clear Hc. intros x H. apply xpub_true in H. subst. reflexivity. }
  specialize (Hc H X xpubX). simpl in Hc.
  repeat try rewrite t_update_eq in Hc.
  discriminate.
Qed.

(** We can use [sme_state] to execute such programs to obtain a noninterferent
    state transformer, by running them 2 times, once on a state without secrets
    and once on the original input state and then merging the final states. *)

Definition sme_cmd c :=
  sme_state (fun s => ceval_fun_no_while s c).

Definition sme_insecure_com1 := sme_cmd insecure_com1 xpub.

Definition sme_insecure_com2 := sme_cmd insecure_com2 xpub.

(** The result of applying [sme_cmd] to a program is no longer a program, but a
    state transformer. We can prove them noninterferent as state transformers
    using our noninterference theorem about [sme_state]. *)

Theorem noninterferent_sme_insecure_com1 :
  noninterferent_state xpub sme_insecure_com1.
Proof. apply noninterferent_sme_state. Qed.

Theorem noninterferent_sme_insecure_com2 :
  noninterferent_state xpub sme_insecure_com2.
Proof. apply noninterferent_sme_state. Qed.


(** * Noninterference and SME for Imp programs with loops *)

(** In the presence of loops, we need to define noninterference using the
    evaluation relation ([ceval]) of Imp: *)

Definition noninterferent_while pub c := forall s1 s2 s1' s2',
  pub_equiv pub s1 s2 ->
  s1 =[ c ]=> s1' ->
  s2 =[ c ]=> s2' ->
  pub_equiv pub s1' s2'.

Ltac invert H := inversion H; subst; clear H.

Lemma noninterferent_secore_com' :
  noninterferent_while xpub secure_com.
Proof.
  unfold noninterferent_while, secure_com, pub_equiv.
  intros s1 s2 s1' s2' H H1 H2 x Hx.
  apply xpub_true in Hx. subst.
  (* the proof is the same, but with some extra ugly [invert]s *)
  invert H1. invert H4. invert H7.
  invert H2. invert H3. invert H6. simpl.
  rewrite (H X xpubX). reflexivity.
Qed.

(** Now to define SME we also need to use a relation,
    of a similar type to [ceval]: *)

Check ceval : com -> state -> state -> Prop.

Definition sme_while (pub:pub_map) (c:com) (s s':state) : Prop :=
  exists ps ss, split_state s pub true =[ c ]=> ps /\
                                     s =[ c ]=> ss /\
                       merge_states ps ss pub = s'.

(** To state that sme_eval is secure, we need to generalize our noninterference
    definition, so that it works not only with [ceval], but with any evaluation
    relation, including [sme_while pub]. *)

Definition noninterferent_while_R (R:com->state->state->Prop) pub c :=
  forall s1 s2 s1' s2',
  pub_equiv pub s1 s2 ->
  R c s1 s1' ->
  R c s2 s2' ->
  pub_equiv pub s1' s2'.

(** The proof that [while_sme] is noninterferent is as before, but now it relies
    on the determinism of [ceval], which was obvious for state transformer
    functions, but is not obvious for evaluation relations. *)

Check ceval_deterministic : forall (c : com) (st st1 st2 : state),
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.

Theorem noninterferent_while_sme : forall pub c,
  noninterferent_while_R (sme_while pub) pub c.
Proof.
  unfold noninterferent_while_R, sme_while.
  intros pub c s1 s2 s1' s2' H [ps1 [ss1 [H1p [H1s H1m]]]]
                               [ps2 [ss2 [H2p [H2s H2m]]]].
  subst. rewrite pub_equiv_split_iff in H. unfold pub_equiv_split in H.
  apply functional_extensionality in H. rewrite H in H1p.
  rewrite (ceval_deterministic _ _ _ _ H1p H2p).
  apply pub_equiv_merge_states.
Qed.

(** Turns out we can only prove a weak version of transparency, and this has to
    do with nontermination (more later). But first we need a few lemmas:  *)

Lemma pub_equiv_split_state : forall (pub:pub_map) s,
  pub_equiv pub (split_state s pub true) s.
Proof.
  unfold pub_equiv, split_state.
  intros pub s x Hx. destruct (Bool.eqb_spec (pub x) true).
  reflexivity. contradiction.
Qed.

Lemma pub_equiv_sym : forall (pub:pub_map) s1 s2,
  pub_equiv pub s1 s2 ->
  pub_equiv pub s2 s1.
Proof.
  unfold pub_equiv. intros pub s1 s2 H x Hx.
  rewrite H. reflexivity. assumption.
Qed.

Lemma merge_state_pub_equiv : forall pub ss ps,
  pub_equiv pub ss ps ->
  merge_states ps ss pub = ss.
Proof.
  unfold pub_equiv, merge_states.
  intros pub ss ps H. apply functional_extensionality.
  intros x. destruct (pub x) eqn:Heq.
  - rewrite H. reflexivity. assumption.
  - reflexivity.
Qed.

(** More specifically, we can only prove that [sme_while] execution implies
    [ceval]. But we cannot prove the reverse implication, since a command
    terminating when starting in state [s], does not necessarily still
    terminates when starting in state [split_state s pub true], as would be
    needed for proving [sme_while]. *)

Theorem somewhat_transparent_while_sme : forall pub c,
  noninterferent_while pub c ->
  (forall s s', (sme_while pub) c s s' -> s =[ c ]=> s').
Proof.
  unfold noninterferent_while, sme_while.
  intros pub c Hni s s' [ps [ss [Hp [Hs Hm]]]]. subst s'.
    assert(H:pub_equiv pub s (split_state s pub true)).
    { apply pub_equiv_sym. apply pub_equiv_split_state. }
    specialize (Hni s (split_state s pub true) ss ps H Hs Hp).
    apply merge_state_pub_equiv in Hni. rewrite Hni. apply Hs.
Qed.

(** Still, it seems we can still do the same things as in the setting without
    while loops, including SME (just not fully transparent). So is there
    anything special about loops and nontermination?

    Yes, there is! Let's look at our noninterference definition again:
[[
Definition noninterferent_while pub c := forall s1 s2 s1' s2',
  pub_equiv pub s1 s2 ->
  s1 =[ c ]=> s1' ->
  s2 =[ c ]=> s2' ->
  pub_equiv pub s1' s2'.
]] 
    It says that for any two _terminating_ executions, if the initial states
    agree on their public variables, then so do the final states. This is
    traditionally called _termination-insensitive_ noninterference (TINI),
    since it doesn't consider nontermination to be observable to an attacker.

    In particular, the following program is considered secure wrt TINI: *)

Definition termination_leak : com :=
  <{ if Y = 0 then
       Y := 42
     else
       while true do skip end (* <- we leak the secret by looping *)
     end }>.

(** And we can prove it ... *)

Lemma Y_neq_X : (Y <> X).
Proof. intro contra. discriminate. Qed.

(* TERSE *)
Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Admitted. (* this one is a homework exercise in Imp *)
(* /TERSE *)

Definition tini_secure_termination_leak :
  noninterferent_while xpub termination_leak.
Proof.
  unfold noninterferent_while, termination_leak, pub_equiv.
  intros s1 s2 s1' s2' H H1 H2 x Hx. apply xpub_true in Hx.
  subst. specialize (H X xpubX).
  invert H1.
  + invert H8. simpl.
    rewrite (t_update_neq _ _ _ _ _ Y_neq_X).
    invert H2.
    * invert H8. simpl.
      rewrite (t_update_neq _ _ _ _ _ Y_neq_X). assumption.
    * apply loop_never_stops in H8. contradiction.
  + apply loop_never_stops in H8. contradiction.
Qed.


(** * Termination-Sensitive Noninterference *)

(** We can give a stronger definition of security that prevents such
    nontermination leaks. It is traditionally called _termination-sensitive
    noninterference_ (TSNI) and it is defined as follows: *)

Definition tsni_while_R (R:com->state->state->Prop) pub c :=
  forall s1 s2 s1',
  R c s1 s1' ->
  pub_equiv pub s1 s2 ->
  (exists s2', R c s2 s2' /\ pub_equiv pub s1' s2').

(** We can prove that [termination_leak] doesn't satisfy TSNI: *)

Definition tsni_insecure_termination_leak :
  ~tsni_while_R ceval xpub termination_leak.
Proof.
  unfold tsni_while_R, termination_leak.
  intros Hc.
  specialize (Hc (X !-> 0 ; Y !-> 0) (X !-> 0 ; Y !-> 1)
                 (Y !-> 42; X !-> 0 ; Y !-> 0)).
  assert (HH : (X !-> 0; Y !-> 0) =[ termination_leak ]=>
               (Y !-> 42; X !-> 0; Y !-> 0)).
  { clear. unfold termination_leak. constructor.
    - reflexivity.
    - constructor. reflexivity. }
  specialize (Hc HH). clear HH.
  assert (H: forall x, xpub x = true ->
                       (X !-> 0; Y !-> 0) x = (X !-> 0; Y !-> 1) x).
  { clear Hc. intros x H. apply xpub_true in H. subst. reflexivity. }
  specialize (Hc H). clear H.
  destruct Hc as [s2' [Hc _]].
  invert Hc.
  - simpl in H4. discriminate.
  - apply loop_never_stops in H5. contradiction.
Qed.

(** More generally, we can prove that TSNI is strictly stronger than TINI
    (noninterferent_while) *)

Lemma tsni_noninterferent : forall pub c,
  tsni_while_R ceval pub c ->
  noninterferent_while_R ceval pub c.
Proof.
  unfold noninterferent_while_R, tsni_while_R.
  intros pub c Htsni s1 s2 s1' s2' Hequiv H1 H2.
  specialize (Htsni s1 s2 s1' H1 Hequiv).
  destruct Htsni as [s2'' [H2' Hequiv']].
  rewrite (ceval_deterministic _ _ _ _ H2 H2').
  apply Hequiv'.
Qed.

(** The reverse direction of the implication only works for programs that
    always terminate (such as most of our simple examples above). *)

Lemma terminating_noninterferent_tsni: forall pub c,
  (forall s, exists s', s =[ c ]=> s') ->
  noninterferent_while_R ceval pub c ->
  tsni_while_R ceval pub c.
Proof.
  unfold noninterferent_while_R, tsni_while_R.
  intros pub c Hterminating Hni s1 s2 s1' H Eq.
  destruct (Hterminating s2) as [s2' H'].
  exists s2'; split.
  - assumption.
  - apply Hni with (s1 := s1) (s2 := s2).
    + assumption.
    + assumption.
    + assumption.
Qed.

(** Now for a more interesting use of TSNI: it turns out that
    [sme_while] is transparent for programs satisfying TSNI. *)

Theorem tsni_transparent_while_sme : forall pub c,
  tsni_while_R ceval pub c ->
  (forall s s', s =[ c ]=> s' <-> (sme_while pub) c s s').
Proof.
  unfold tsni_while_R, sme_while.
  intros pub c Hni s s'.
  assert(HH:pub_equiv pub s (split_state s pub true)).
    { apply pub_equiv_sym. apply pub_equiv_split_state. }
  split.
  - intros H. specialize (Hni s (split_state s pub true) s' H HH).
    destruct Hni as [s'' [Heval Hequiv]].
    exists s''. exists s'. split. assumption. split. assumption.
    apply merge_state_pub_equiv. assumption.
  - intros [ps [ss [Hp [Hs Hm]]]]. subst s'.
    specialize (Hni s (split_state s pub true) ss Hs HH).
    destruct Hni as [s' [Hp' Hni]].
    rewrite (ceval_deterministic _ _ _ _ Hp Hp').
    apply merge_state_pub_equiv in Hni. rewrite Hni. apply Hs.
Qed.

(** Unfortunately [sme_while] does not imply TSNI, and this is hard to fix in
    our current setting, where programs only return a result in the end, a final
    state, so we had to merge the public and secret inputs into a single final
    state. Instead, SME is commonly defined in a setting with interactive IO, in
    which public outputs and secret outputs can be performed independently,
    during the execution. In that setting, it does transparently enforce TSNI. *)


(* HIDE *)
(** Does SME ensure TSNI? Seems not! *)

Theorem tsni_while_sme : forall pub c,
  tsni_while_R (sme_while pub) pub c.
Proof.
  unfold tsni_while_R, sme_while.
  intros pub c s1 s2 s1' [ps [ss [H1 [H2 Hm]]]] H.
  (* the public execution is easy, but the private one is not *)
  eexists. split. eexists. eexists. split.
  - rewrite pub_equiv_split_iff in H. unfold pub_equiv_split in H.
    apply functional_extensionality in H. rewrite <- H. eassumption.
  - split.
Abort.

(** Could it be defined so that it does?
    Looking at the original SME paper it seems that they did!
    But it probably relies on concurrent execution and
    _interactive_ IO? It would be good to double check. *)

(* TODO: It would be good to also check this paper:
   Impossibility of Precise and Sound Termination Sensitive Security Enforcements
   (https://www-sop.inria.fr/lemme/Tamara.Rezk/publication/sp18.pdf)
   in which they claim that SME enforces a weaker notion called Indirect TSNI. *)

(** How about a SME definition that first does the public run.
    If the public run loops, the whole thing loops.
    If the public run terminates, it does the private run.
    If the private run terminates, we merge the two final states.
    If the private run loops, the result is the public
      part of the final state of the public run.
    Such an execution strategy doesn't seem implementable / decidable,
    especially the last part: still returning a result when the private run
    loops. It's not like we can detect nontermination in practice.
    So a model of _interactive_ IO would be the more realistic setting, since
    then we can send out the public and private outputs as they arise,
    instead of trying to merge them into a single output. *)

Definition sme_while' (pub:pub_map) (c:com) (s s':state) : Prop :=
  (exists ps, split_state s pub true =[ c ]=> ps /\
    ((exists ss, s =[ c ]=> ss /\ merge_states ps ss pub = s')
    \/ ((~exists ss, s =[ c ]=> ss) /\ split_state ps pub true = s'))).

Require Import Coq.Logic.Classical_Prop.

Lemma pub_equiv_merge_split : forall pub ps ss,
  pub_equiv pub (merge_states ps ss pub) (split_state ps pub true).
Admitted.

Lemma pub_equiv_split_merge : forall pub ps ss,
  pub_equiv pub (split_state ps pub true) (merge_states ps ss pub).
Admitted.

Lemma pub_equiv_refl : forall pub s, pub_equiv pub s s.
Proof. unfold pub_equiv. reflexivity. Qed.

Theorem tsni_while_sme' : forall pub c,
  tsni_while_R (sme_while' pub) pub c.
Proof.
  unfold tsni_while_R, sme_while'.
  intros pub c s1 s2 s1' HH H.
  rewrite pub_equiv_split_iff in H. unfold pub_equiv_split in H.
  apply functional_extensionality in H. rewrite <- H.
  destruct HH as [ps [Hps [[ss1 [Hss1 Hm]] | [H2 Heq]]]].
{ destruct (classic (exists ss2 : state, s2 =[ c ]=> ss2))
   as [[ss2 Hss2] | Hnss2].
  - exists (merge_states ps ss2 pub). split.
    + exists ps. split.
      * apply Hps.
      * left. exists ss2. split. apply Hss2. reflexivity.
    + subst. apply pub_equiv_merge_states.
  - exists (split_state ps pub true). split.
    + exists ps. split.
      * apply Hps.
      * right. split. apply Hnss2. reflexivity.
    + subst. apply pub_equiv_merge_split. }
{ destruct (classic (exists ss2 : state, s2 =[ c ]=> ss2))
   as [[ss2 Hss2] | Hnss2].
  - exists (merge_states ps ss2 pub). split.
    + exists ps. split.
      * apply Hps.
      * left. exists ss2. split. apply Hss2. reflexivity.
    + subst. apply pub_equiv_split_merge.
  - exists (split_state ps pub true). split.
    + exists ps. split.
      * apply Hps.
      * right. split. apply Hnss2. reflexivity.
    + subst. apply pub_equiv_refl. }
Qed.

(* Could add syntax (Imp) and then look at dynamic enforcement?
   - my dynamic IFC development from underconstruction is quite complicated!
   Maybe drop while loops and stick to a denotational semantics,
   which directly corresponds to the state transformers above? At first at least?

   Without loops vs. step-indexed evaluator?
   - instead of dropping loops can we use the step-indexed evaluator from ImpCEvalFun?
     + this only has some chance of working if we ensure cryptographic constant
       time, since otherwise the number of steps a program takes is a big
       side-channel that will influence the failure behavior of the step-indexed
       evaluator (i.e. running out of fuel or not)

   Any weakening of noninterference? Declassification?

   Expressing leakage (=attacker knowledge?) with input partitions?
   - this is often the first step towards quantifying leakage?
   - also related to cryptographic constant time, see below

   Cryptographic constant time
   - Just a simpler kind of IFC type system? (Has anyone done it dynamically?)
   - Noninterference usually defined wrt an instrumented semantics with traces
     of output events issued for memory accesses and branch conditions.
     + Can probably also be defined in terms of execution steps, but that's only
       interesting if one actually models the instruction and data caches?

   Extend Imp with traces of interactive Outputs (but no interactive Inputs)
   - Doesn't seem too difficult, is it?
   - Wasn't it already done in SF? Couldn't find anything yet.
   - Already enough to express side-channels (e.g. cryptographic constant time)
   - SME already becomes more interesting, since Output ordering matters;
     and maybe Concurrent Imp from Smallstep.v won't be enough?

   Taint tracking?
   - there are ways to define security only for explicit flows,
     but it's not only weaker, but probably also more complex than for regular IFC?
*)

(* The idea in this file seems so obvious, it's probably folklore. Still does any paper
   mention this?  Here are some candidates, but I didn't find anything yet:

Steve Zdancewic, Lantian Zheng, Nathaniel Nystrom, Andrew C. Myers:
Secure program partitioning. ACM Trans. Comput. Syst. 20(3): 283-328 (2002)
https://www.cis.upenn.edu/~stevez/papers/ZZNM02.pdf

Still to check out:
https://scholar.google.com/scholar?oi=bibs&hl=en&cites=11105745796447656430
https://scholar.google.com/scholar?hl=en&q=noninterference+partitioning

Q: Is this idea related to self-composition or secure multi-execution?
   Yes, with secure multi-execution! They are focused on I/O programs.

Dominique Devriese, Frank Piessens: Noninterference through Secure
Multi-execution. IEEE Symposium on Security and Privacy 2010: 109-124
https://doi.org/10.1109/SP.2010.15

*)

(** Noninterference from parametricity? Probably not in this last lecture! *)

Section NI_from_parametricity.

Context (PI PO SO : Type).
(* Do I need to fix the types PI PO SP, or can they remain generic? *)

(** Q: What parametricity theorem do we get to assume for the type of f below? *)
(* Reference: Dynamic IFC Theorems for Free: https://arxiv.org/pdf/2005.04722.pdf *)

Theorem noninterference_by_type_abstraction :
  forall f : (forall AI:Type, PI -> AI -> PO*SO),
    forall SI:Type, noninterferent (f SI).
Admitted.

(** This should morally be the same proof as showing
    that [forall a, a -> nat] is a constant function *)

(* [| Type |] A0 A1 = A0 -> A1 -> Type *)
(* [| forall a:Type, a -> nat |] f0 f1 =
        a0:Type -> a1:Type -> ar:(a0 -> a1 -> Type) ->
        x0:a0 -> x1:a1 -> ar x0 x1 ->
        f0 a0 x0 = f1 a1 x1 *)

(* Not sure I got the parametricity translation right, but anyway, the axiom
   seems more complicated than what we're trying to prove, and then the
   instantiation is trivial to prove constant function. So pedagogical
   usefulness is very uncertain.  Maybe could use the parametricity plugin for
   Coq to at least make sure that the statement of the axiom is correct and
   standard?  We could, but still uncertain this kind of example would be
   helpful for students. Would need to explain a lot more about parametricity
   for this to make sense. *)
Axiom parametricity_forall_a_a_to_nat : forall f : (forall a, a -> nat),
  forall (a0 a1:Type) (ar:a0->a1->Type) (x0:a0) (x1:a1), ar x0 x1 -> f a0 x0 = f a1 x1.

Theorem constant_forall_a_a_to_nat : forall f : (forall a, a -> nat),
  forall t (x1 x2:t), f t x1 = f t x2.
Proof.
  intros f t x1 x2.
  apply parametricity_forall_a_a_to_nat with (ar := (fun x0 x1 => True)).
  apply I.
Qed.

End NI_from_parametricity.

(* Could go further in the direction of LIO, using monads for IFC?
   Too advanced for this last lecture! *)
(* /HIDE *)
